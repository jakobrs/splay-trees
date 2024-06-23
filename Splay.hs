{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

import Data.Foldable (foldlM)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (..))
import Data.Monoid (Endo (..), Sum (..))

-- Used only in example code at the bottom
import Control.Monad.State
  ( MonadState (..),
    State,
    StateT,
    evalStateT,
    execState,
    modify',
  )
import Control.Monad.Writer (MonadWriter (..), Writer (..), execWriter)

data Node n a = Node
  { left :: ONode n a,
    value :: a,
    right :: ONode n a,
    metadata :: n
  }
  deriving (Show, Eq, Foldable, Functor, Traversable)

class Metadata a n where
  calc :: ONode n a -> a -> ONode n a -> n

instance Metadata a () where
  calc _ _ _ = ()

monoidCalc :: (Monoid m) => (a -> m) -> ONode m a -> a -> ONode m a -> m
monoidCalc f l x r = maybe mempty (.metadata) l <> f x <> maybe mempty (.metadata) r

instance (Num a) => Metadata a (Sum a) where
  calc = monoidCalc Sum

fixup :: (Metadata a n) => Node n a -> Node n a
fixup n@(Node {left, value, right}) = n {metadata = calc left value right}

mkNode :: (Metadata a n) => ONode n a -> a -> ONode n a -> Node n a
mkNode left value right =
  Node
    { left,
      value,
      right,
      metadata = calc left value right
    }

type ONode n a = Maybe (Node n a)

data Dir = L | R deriving (Show)

mapL, mapR :: (Metadata a n) => (Node n a -> Node n a) -> (Node n a -> Node n a)
mapL f n = fixup $ n {left = f <$> n.left}
mapR f n = fixup $ n {right = f <$> n.right}

splayByPath' :: (Metadata a n) => [Dir] -> Node n a -> Node n a
splayByPath' [] n = n
splayByPath' [L] n = rotR n
splayByPath' [R] n = rotL n
splayByPath' (L : L : d) n = n & (mapL . mapL) (splayByPath' d) & rotR & rotR
splayByPath' (R : R : d) n = n & (mapR . mapR) (splayByPath' d) & rotL & rotL
splayByPath' (L : R : d) n = n & (mapL . mapR) (splayByPath' d) & mapL rotL & rotR
splayByPath' (R : L : d) n = n & (mapR . mapL) (splayByPath' d) & mapR rotR & rotL

splayByPath :: (Metadata a n) => [Dir] -> ONode n a -> ONode n a
splayByPath = fmap . splayByPath'

splayM :: (Metadata a n, Monad m) => (ONode n a -> m [Dir]) -> ONode n a -> m (ONode n a)
splayM f n = f n <&> flip splayByPath n

-- splay f = runIdentity . splayM (Identity . f)
splay :: (Metadata a n) => (ONode n a -> [Dir]) -> ONode n a -> ONode n a
splay f n = splayByPath (f n) n

splayByKey :: (Metadata a n, Ord a) => a -> ONode n a -> ONode n a
splayByKey = splay . locateByKey

rotL, rotR :: (Metadata a n) => Node n a -> Node n a
rotL (Node a x (Just (Node b y c _)) _) = mkNode (Just (mkNode a x b)) y c
rotL n = n
rotR (Node (Just (Node a x b _)) y c _) = mkNode a x (Just (mkNode b y c))
rotR n = n

locateM :: (Monad m) => (Node n a -> m (Maybe Dir)) -> ONode n a -> m [Dir]
locateM _f Nothing = pure []
locateM f (Just n) =
  f n >>= \case
    Nothing -> pure []
    Just L -> (L :) <$> locateM f n.left
    Just R -> (R :) <$> locateM f n.right

locate :: (Node n a -> Maybe Dir) -> ONode n a -> [Dir]
locate f = runIdentity . locateM (Identity . f)

cmpToDir :: Ordering -> Maybe Dir
cmpToDir EQ = Nothing
cmpToDir LT = Just L
cmpToDir GT = Just R

locateByKey :: (Ord a) => a -> ONode n a -> [Dir]
locateByKey key = locate $ cmpToDir . compare key . (.value)

splitM :: (Metadata a n, Monad m) => (ONode n a -> m [Dir]) -> ONode n a -> m (ONode n a, ONode n a)
splitM f n =
  splayM f n >>= \case
    Nothing -> pure (Nothing, Nothing)
    Just n' -> do
      d <- f $ Just n'
      let split_left = (n'.left, Just (fixup (n' {left = Nothing})))
          split_right = (Just (fixup (n' {right = Nothing})), n'.right)
      pure $ case d of
        [] -> split_left
        (L : _) -> split_left
        (R : _) -> split_right

split :: (Metadata a n) => (ONode n a -> [Dir]) -> ONode n a -> (ONode n a, ONode n a)
split f = runIdentity . splitM (Identity . f)

splitByKey :: (Metadata a n, Ord a) => a -> ONode n a -> (ONode n a, ONode n a)
splitByKey = split . locateByKey

insert :: (Metadata a n, Ord a) => a -> ONode n a -> ONode n a
insert key (splitByKey key -> (l, r)) = Just $ mkNode l key r

empty :: ONode n a
empty = Nothing

singleton :: (Metadata a n) => a -> Node n a
singleton x = mkNode Nothing x Nothing

fromList :: (Metadata a n, Ord a) => [a] -> ONode n a
fromList = foldl (flip insert) empty

fromList' :: (Ord a) => [a] -> ONode () a
fromList' = fromList

toList :: ONode n a -> [a]
toList = flip appEndo [] . (foldMap . foldMap) (Endo . (:))

getMetadata :: ONode n a -> Maybe n
getMetadata = fmap (.metadata)

benchmark :: forall a. (Ord a) => [a] -> Int
benchmark lst = flip execState 0 $ do
  let locateByKeyB key = locateM $ \x -> do
        modify' (+ 1)
        pure $ cmpToDir (compare key x.value)
      insertB key n = do
        (l, r) <- splitM (locateByKeyB key) n
        pure . Just $ mkNode l key r
      fromListB :: [a] -> _ (ONode () a)
      fromListB = foldlM (flip insertB) empty
  _ <- fromListB lst
  pure ()

toDot :: (Show n) => (Show a) => Node n a -> String
toDot n = flip appEndo [] . execWriter . flip evalStateT 0 $ do
  tell $ Endo ("digraph {\n" <>)
  go n
  tell $ Endo ("}\n" <>)
  where
    go :: (Show n, Show a) => Node n a -> StateT Int (Writer (Endo String)) Int
    go (Node {left, value, right, metadata}) = do
      i <- get
      modify' (+ 1)
      tell $ Endo (("n" <> show i <> " [shape=\"box\", label=\"value = " <> show value <> "\\nmeta = " <> show metadata <> "\"]\n") <>)
      let descend n =
            case n of
              Nothing -> do
                j <- get
                modify' (+ 1)
                tell $ Endo (("n" <> show i <> " -> n" <> show j <> "\nn" <> show j <> " [shape=\"point\"]\n") <>)
              Just l -> do
                j <- go l
                tell $ Endo (("n" <> show i <> " -> n" <> show j <> "\n") <>)
      descend left
      descend right
      pure i

data Meta = Meta {height :: Int, order :: Int} deriving (Show)

instance Metadata a Meta where
  calc l x r =
    Meta
      { height = max (maybe 0 (.metadata.height) l) (maybe 0 (.metadata.height) r) + 1,
        order = maybe 0 (.metadata.order) l + maybe 0 (.metadata.order) r + 1
      }
