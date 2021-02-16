module FOL.Search where

import Control.Monad
import Control.Applicative
import Control.Monad.Logic
import Data.Maybe

-- Search up to a certain depth, given by the argument.
newtype Search a = Search {runSearch :: Int -> Logic a}

instance Monad Search where
    Search k >>= f = Search $ \d -> (flip runSearch d . f) =<< (k d)

deeper :: Search a  -> Search a
deeper (Search f) = Search (\d -> case d of
                                    0 -> empty
                                    n -> f (n - 1))

choose :: Alternative m => [a] -> m a
choose xs = foldr (<|>) empty $ map pure xs 

try :: Alternative m => Maybe a -> m a
try = maybe empty pure

instance Functor Search where
  fmap f = (pure f <*>)

instance Applicative Search where
  pure x = Search (\_ -> pure x)
  (<*>) = ap

instance Alternative Search where
  empty = Search (\_ -> empty)
  (Search m) <|> (Search n) = Search (\d -> m d `interleave` n d)


runSearchAt :: Int -> Search a -> Maybe a
runSearchAt d (Search f) = listToMaybe (observeMany 1 (f d))

-- >>> runSearchAt 1 (return "ok" <|>  return "nok" <|> empty)
-- ["ok","nok"]
