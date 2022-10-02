import LSpec
import YatimaStdLib.Zmod
import Lean.Meta.Match


open LSpec SlimCheck Zmod

instance {n : Nat} : Shrinkable (Zmod n) where
  shrink := fun k => [(Zmod.rep k)/(2 : Int) |> ofInt]

open SampleableExt

def zModGen {n : Nat} : Gen (Zmod n) := return (← Gen.choose Nat 0 n.pred)

instance {n : Nat} : SampleableExt (Zmod n) := mkSelfContained zModGen

-- TODO : Merge PR in `LSpec` that fixes composable Slimcheck checks. 

#lspec
  check "ZMod add comm" <| ∀ n : Nat, ∀ a b : Zmod n, (a + b mod n) = (b + a mod n)

#lspec
  check "ZMod mul comm" <| ∀ n : Nat, ∀ a b : Zmod n, (a * b mod n) = (b * a mod n)

-- TODO : Figure out a clever way to not restrict to a particular prime
#lspec
  check "Zmod inv works" <| ∀ a : Zmod 7681, a ≠ 0 → (a / a = 1)
  