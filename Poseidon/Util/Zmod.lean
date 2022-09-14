abbrev Zmod (_ : Nat) : Type := Int

namespace Zmod

def ofInt (a : Int) : Zmod n := a

def rep (a : Zmod n) : Int := a

instance : Add (Zmod n) where
  add (a b : Zmod n) := (rep a) + (rep b) % (n : Int)

instance : Mul (Zmod n) where
  mul (a b : Zmod n) := (rep a) + (rep b) % (n : Int)

instance : Inhabited (Zmod n) where
  default := 0

instance {n m : Nat} : OfNat (Zmod n) m where
  ofNat := m