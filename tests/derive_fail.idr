import Extra.Prelude
import Extra.Language.Derive
import Language.Reflection
import Decidable.Equality

%language ElabReflection

data BalancedTree : Nat -> Type -> Type where
  Leaf : BalancedTree 0 a
  Branch : {n : Nat}
    -> (1 l : BalancedTree n a)
    -> (1 x : a)
    -> (1 r : BalancedTree n a)
    -> BalancedTree (S n) a

Uninhabited (Branch l x y = Leaf) where
  uninhabited Refl impossible

Uninhabited (Leaf = Branch l x r) where
  uninhabited Refl impossible

-- Namespace it so it doesn't conflict with other `derivedDecEq`s
namespace BalancedTreeDerive
  mutual
    derivedEq : Eq a
      => BalancedTree n a
      -> BalancedTree n a
      -> Bool
    %runElab deriveEq `{{ BalancedTree }}

    Eq a => Eq (BalancedTree n a) where
      (==) = derivedEq

  -- This fails since the clause `decEq Leaf (Branch _ _ _)` fails to typecheck
  mutual
    derivedDecEq : DecEq a
      => (x : BalancedTree n a)
      -> (y : BalancedTree n a)
      -> Dec (x = y)
    %runElab deriveDecEq `{{ BalancedTree }}

    DecEq a => DecEq (BalancedTree n a) where
      decEq = derivedDecEq

main : IO ()
main = putStrLn "Hi!"
