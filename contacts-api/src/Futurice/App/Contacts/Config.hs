module Futurice.App.Contacts.Config (
    Config(..),
    getConfig,
    ) where

import Futurice.Prelude
import Prelude          ()

import Futurice.EnvConfig

import qualified Chat.Flowdock.REST as FD
import qualified FUM
import qualified GitHub             as GH

-- | TODO: split config into two parts
data Config = Config
    { cfgFumAuth     :: !FUM.AuthToken     -- ^ FUM auth token
    , cfgFumBaseUrl  :: !FUM.BaseUrl       -- ^ FUM base url
    , cfgFumUserList :: !FUM.ListName      -- ^ FUM user list
    , cfgGhAuth      :: !GH.Auth           -- ^ Github auth information
    , cfgGhOrg       :: !(GH.Name GH.Organization)
      -- ^ Github organisation
    , cfgFdAuth      :: !FD.AuthToken      -- ^ Flowdock token
    , cfgFdOrg       :: !(FD.ParamName FD.Organisation)
      -- ^ Flowdock organisation
    , cfgPort        :: !Int
      -- ^ Port to listen from, default is 'defaultPort'.
    }
    deriving (Show)

getConfig :: IO Config
getConfig = Config
    <$> parseEnvVar "FUM_AUTH_TOKEN"
    <*> parseEnvVar "FUM_BASE_URL"
    <*> parseEnvVar "FUM_USER_LIST"
    <*> parseEnvVar "GH_AUTH_TOKEN"
    <*> parseEnvVar "GH_ORGANISATION"
    <*> parseEnvVar "FD_AUTH_TOKEN"
    <*> parseEnvVar "FD_ORGANISATION"
    <*> parseDefaultPort
