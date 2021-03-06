{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}

module Github.Haxl (
    membersOf,
    userInfoFor,
    initDataSource,
    GithubRequest(..),
    GithubDataSourceException(..),
    ) where

import Prelude        ()
import Prelude.Compat

import Control.Concurrent.ParallelIO.Local (parallel_, withPool)

import Control.Exception
import Data.Bifunctor    (first)
import Data.Hashable     (Hashable (..))
import Data.Typeable     (Typeable)
import Data.Vector       (Vector)
import Haxl.Core

import qualified GitHub     as GH

data GithubRequest a where
    GithubRequest :: Show a => GH.Request 'True a -> GithubRequest a

deriving instance Show (GithubRequest a)
deriving instance Typeable GithubRequest
deriving instance Eq (GithubRequest a)

instance Show1 GithubRequest where show1 = show

instance Hashable (GithubRequest a) where
  hashWithSalt salt (GithubRequest gh) = hashWithSalt salt gh

membersOf :: GH.Name GH.Organization -> GenHaxl u (Vector GH.SimpleUser)
membersOf = dataFetch . GithubRequest . flip GH.membersOfR Nothing

userInfoFor :: GH.Name GH.User -> GenHaxl u GH.User
userInfoFor = dataFetch . GithubRequest. GH.userInfoForR

instance StateKey GithubRequest where
    data State GithubRequest = GithubDataState GH.Auth

initDataSource :: GH.Auth           -- ^ Authentication token
               -> IO (State GithubRequest)
initDataSource auth =
    pure (GithubDataState auth)

instance DataSourceName GithubRequest where
    dataSourceName _ = "GithubDataSource"

instance DataSource u GithubRequest where
    fetch (GithubDataState auth) _flags _userEnv blockedFetches =
        SyncFetch $ batchFetch auth blockedFetches

batchFetch :: GH.Auth  -> [BlockedFetch GithubRequest] -> IO ()
batchFetch auth fetches =
    withPool 10 $ \pool ->
        parallel_ pool (doFetch auth <$> fetches)

putEither :: ResultVar a -> Either String a -> IO ()
putEither v res = case res of
    Right x -> putSuccess v x
    Left err -> putFailure v (GithubDataSourceException err)

doFetch :: GH.Auth -> BlockedFetch GithubRequest -> IO ()
doFetch auth (BlockedFetch (GithubRequest req) v) =
    action >>= putEither v
  where
    action = first show <$> GH.executeRequest auth req

data GithubDataSourceException = GithubDataSourceException String
  deriving (Show, Typeable)

instance Exception GithubDataSourceException where
    toException = transientErrorToException
    fromException = transientErrorFromException
