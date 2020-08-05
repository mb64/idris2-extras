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

-- This works fine
mutual
  eqBalancedTree : Eq a
    => BalancedTree n a
    -> BalancedTree n a
    -> Bool
  %runElab deriveEq `{{ eqBalancedTree }} `{{ BalancedTree }}

  Eq a => Eq (BalancedTree n a) where
    (==) = eqBalancedTree

-- This fails since the clause `decEq Leaf (Branch _ _ _)` fails to typecheck
mutual
  decEqBalancedTree : DecEq a
    => (x : BalancedTree n a)
    -> (y : BalancedTree n a)
    -> Dec (x = y)
  %runElab deriveDecEq `{{ decEqBalancedTree }} `{{ BalancedTree }}

  DecEq a => DecEq (BalancedTree n a) where
    decEq = decEqBalancedTree

main : IO ()
main = putStrLn "Hi!"
