{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Utility where

import Control.Category ((>>>))
import Control.Monad (foldM, (>=>))
import Data.Function ((&))
import Text.PrettyPrint (Doc, comma, hcat, hsep, nest, punctuate, vcat, (<+>))

filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap f = foldMap (f >>> maybe mempty pure)

filterMapM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m [b]
filterMapM f = foldMapM (f >=> return . maybe mempty pure)

foldMapM :: (Foldable t, Monad m, Monoid b) => (a -> m b) -> t a -> m b
foldMapM f = foldM (\m a -> (m <>) <$> f a) mempty

bullets :: [Doc] -> Doc
bullets [] = "[empty]"
bullets ds = ds & vcat . fmap (("-" <+>) . nest 4)

commas :: [Doc] -> Doc
commas = hcat . punctuate comma

spacedCommas :: [Doc] -> Doc
spacedCommas = hsep . punctuate comma

extractAtIndex :: Int -> [a] -> Maybe ([a], a)
extractAtIndex = go []
  where
    go :: [a] -> Int -> [a] -> Maybe ([a], a)
    go ys 0 (x : xs) = return (reverse ys <> xs, x)
    go ys i (x : xs) = go (x : ys) (i - 1) xs
    go _ _ [] = Nothing

extractions :: [a] -> [([a], a)]
extractions = go [] []
  where
    go :: [([a], a)] -> [a] -> [a] -> [([a], a)]
    go outputs _ [] = outputs
    go outputs xs (y : ys) = go (outputs <> [(xs <> ys, y)]) (xs <> [y]) ys

indices :: [a] -> [Int]
indices xs = [0 .. length xs - 1]

fixpointEq :: (Eq a) => (a -> a) -> a -> a
fixpointEq f a =
  let a' = f a
   in if a /= a'
        then fixpointEq f a'
        else a

fixpointEqM :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixpointEqM f a = do
  a' <- f a
  if a /= a'
    then fixpointEqM f a'
    else return a

subscriptNumber :: Int -> String
subscriptNumber i = "_" <> show i

applyFirst :: (a -> a) -> [a] -> [a]
applyFirst _ [] = []
applyFirst f (x : xs) = f x : xs

