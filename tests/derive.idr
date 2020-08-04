import Extra.Prelude
import Extra.Language.Derive
import Language.Reflection
import Decidable.Equality

%language ElabReflection

data Tree a = Branch (Tree a) a (Tree a)
            | Leaf

Uninhabited (Branch l x y = Leaf) where
  uninhabited Refl impossible

Uninhabited (Leaf = Branch l x r) where
  uninhabited Refl impossible

mutual
  eqTree : Eq a
    => Tree a
    -> Tree a
    -> Bool
  %runElab deriveEq `{{ eqTree }} `{{ Tree }}

  Eq a => Eq (Tree a) where
    (==) = eqTree

mutual
  decEqTree : DecEq a
    => (x : Tree a)
    -> (y : Tree a)
    -> Dec (x = y)
  %runElab deriveDecEq `{{ decEqTree }} `{{ Tree }}

  DecEq a => DecEq (Tree a) where
    decEq = decEqTree

main : IO ()
main = putStrLn "Hi!"
