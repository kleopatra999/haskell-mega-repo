{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright : (c) 2015 Futurice Oy
-- License   : BSD3
-- Maintainer: Oleg Grenrus <oleg.grenrus@iki.fi>
--
-- Authentication tools
module PlanMill.Auth (
    Auth(..),
    getAuth,
    getNonce,
    ) where

import PlanMill.Internal.Prelude

-- Almost standard imports
import Control.Monad   (replicateM)
import Data.ByteString (ByteString)

import qualified Data.Vector as V

-- 3rd party imports
import Crypto.Hash   (HMAC (..), SHA256, hmac)
import Data.Byteable (toBytes)

-- Local imports
import PlanMill.Classes
import PlanMill.Types

-- | Authentication information
data Auth = Auth
    { authUser      :: UserId
    , authNonce     :: Nonce
    , authTimestamp :: UTCTime
    , authSignature :: ByteString
    }
    deriving (Eq, Show)

signature :: UserId -> ApiKey -> UTCTime -> Nonce -> ByteString
signature (Ident uid) (ApiKey k) timestamp (Nonce nonce) =
    toBytes $ hmacGetDigest digest
  where
    digest :: HMAC SHA256
    digest = hmac k message

    message :: ByteString
    message = bsShow uid <> nonce <> bsShow (utcTimeToInteger timestamp)


auth :: UserId -> ApiKey -> UTCTime -> Nonce -> Auth
auth u k t n = Auth u n t (signature u k t n)

-- | Create new authentication data for new request.
getAuth :: ( MonadCRandom' m
           , MonadTime m
           , MonadReader env m
           , HasCredentials env
           )
        => m Auth
getAuth = auth <$> fmap getUserId ask
               <*> fmap getApiKey ask
               <*> currentTime
               <*> getNonce

-- | Generate new fresh nonce.
--
-- Uniqueness isn't checked.
getNonce :: MonadCRandom' m => m Nonce
getNonce = Nonce . fromString <$> replicateM 8 randomNonceChar
  where
    randomNonceChar = do
        n <- (fromIntegral :: Word8 -> Int) <$> getCRandom
        if n >= 0 && n < validNonceCharsLength
            then pure $ validNonceChars V.! n
            else randomNonceChar

validNonceChars :: V.Vector Char
validNonceChars =
    V.fromList $ ['A'..'Z'] <> ['a'..'Z'] <> ['0'..'9']

validNonceCharsLength :: Int
validNonceCharsLength = V.length validNonceChars
