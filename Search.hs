module Search where
import Control.Monad
import Control.Applicative
import Data.Maybe

-- Search up to a certain depth, given by the argument.
newtype Search a = Search {runSearch :: Int -> [a]}

instance Monad Search where
    return x = Search $ \_ -> [x]
    (Search k) >>= f = Search $ \d -> concatMap (flip runSearch d . f) (k d)

deeper :: Search a  -> Search a
deeper (Search f) = Search (\d -> case d of
                                    0 -> []
                                    n -> f (n - 1))

choose :: Alternative m => [a] -> m a
choose xs = foldr (<|>) empty $ map pure xs 

try :: Alternative m => Maybe a -> m a
try = maybe empty pure

instance Functor Search where
  fmap f = (pure f <*>)

instance Applicative Search where
  pure = return
  (<*>) = ap

instance Alternative Search where
  empty = Search (\_ -> [])
  (Search m) <|> (Search n) = Search (\d -> m d ++ n d)
