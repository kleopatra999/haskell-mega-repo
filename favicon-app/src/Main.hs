{-# LANGUAGE CPP               #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeOperators     #-}
module Main (main) where

import Futurice.Prelude
import Prelude          ()

import Codec.Picture            (Image, PixelRGBA8)
import Control.Concurrent.STM   (atomically)
import Futurice.Colour
import Futurice.Logo
import Lucid                    hiding (for_)
import Network.Wai              (Application)
import Servant
import Servant.Cache
import Servant.Cache.Class      (DynMapCache)
import Servant.Futurice.Favicon
import Servant.Futurice.Status
import Servant.HTML.Lucid
import Servant.JuicyPixels      (PNG)
import System.Environment       (lookupEnv)
import System.IO                (hPutStrLn, stderr)

import qualified Network.Wai.Handler.Warp      as Warp
import qualified Servant.Cache.Internal.DynMap as DynMap

type IconAPI = "icon" :> Capture "colour" Colour :> Get '[PNG] (Image PixelRGBA8)

type UncachedAPI
    = FutuFaviconAPI ('FutuAccent 'AF5 'AC3)
    :<|> Get '[HTML] (Html ())
    :<|> IconAPI

type API = Cached SomeCache 3600 :> UncachedAPI :<|> StatusAPI

api :: Proxy API
api = Proxy

iconEndpoint :: Proxy IconAPI
iconEndpoint = Proxy

stats :: DynMapCache -> StatusInfoIO
stats dmap = gcStatusInfo <> dynmapStats
  where
    dynmapStats :: StatusInfoIO
    dynmapStats = SIIO $ group "cache" . metric "size" <$> dynmapSize

    dynmapSize :: IO Int
    dynmapSize = atomically $ DynMap.size dmap

server :: DynMapCache -> Server API
server dmap =
    (serveFutuFavicon :<|> pure indexPage
                      :<|> pure . makeLogo)
    :<|> serveStatus (stats dmap)

app :: DynMapCache -> Application
app dmap = serveWithContext api context $ server dmap
  where
    context = cache :. EmptyContext
    cache = SomeCache dmap

main :: IO ()
main = do
  hPutStrLn stderr "Hello, I'm alive"
  port <- fromMaybe 8000 . (>>= readMaybe) <$> lookupEnv "PORT"
  cache <- DynMap.newIO
  Warp.run port (app cache)

indexPage :: Html ()
indexPage = doctypehtml_ $ for_ [minBound..maxBound] $ \colour ->
    let link = textShow $ safeLink api iconEndpoint colour
    in a_ [href_ link] $ img_ [src_ link]
