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

-- Namespace it so it doesn't conflict with other `derivedDecEq`s
namespace TreeDerive
  mutual
    derivedEq : Eq a
      => Tree a
      -> Tree a
      -> Bool
    %runElab deriveEq `{{ Tree }}

    Eq a => Eq (Tree a) where
      (==) = derivedEq

  mutual
    derivedDecEq : DecEq a
      => (x : Tree a)
      -> (y : Tree a)
      -> Dec (x = y)
    %runElab deriveDecEq `{{ Tree }}

    DecEq a => DecEq (Tree a) where
      decEq = derivedDecEq

main : IO ()
main = putStrLn "Hi!"
