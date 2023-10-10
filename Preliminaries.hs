module Preliminaries where

import Data.Word
import Data.Set

fresh_variable :: Maybe a
fresh_variable = Nothing

{- | A type class for finite types with full, known lists of inhabitants.

  Note: This is to ensure that all quantifications in the spec take place
  over finite sets, and can be faithfully translated to quite weak SMT
  theories such as @QF_ABV@.
-}
class Finite a where
  inhabitants :: [a]

indexOf :: (Eq a, Finite a) => a -> Word64
indexOf p = fromIntegral $ length (takeWhile (/= p) inhabitants)

instance (Finite a, Finite b) => Finite (a,b) where
  inhabitants = [(a,b) | a <- inhabitants, b <- inhabitants]

{- | Universal quantifier bounded by a finite set.

  Since sets are finite, no `Finite a` class is required here.

  Note: This is to ensure that our quantifications can be faithfully
  translated to quite weak theories such as @QF_ABV@. See the `Finite`
  type class.
-}
forall :: Set a -> (a -> Bool) -> Bool
forall = flip all

forall_ub :: Finite a => (a -> Bool) -> Bool
forall_ub = flip all inhabitants

{- | Existential quantifier bounded by a finite set.

  Since sets are finite, no `Finite a` class is required here.

  Note: This is to ensure that our quantifications can be faithfully
  translated to quite weak theories such as @QF_ABV@. See the `Finite`
  type class.
-}
exists :: Set a -> (a -> Bool) -> Bool
exists = flip any

exists_ub :: Finite a => (a -> Bool) -> Bool
exists_ub = flip any inhabitants
