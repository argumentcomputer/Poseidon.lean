namespace Zmod

open Int

def Zmod (n : Nat) : Type :=
  match n with
  | 0 => Int
  | n + 1 => Fin (n + 1)

def toZmod (a : Int) : Zmod 0 := a

def fromZmod (a : Zmod 0) : Int := a

instance Zmod_add : HAdd (Zmod n) (Zmod n) (Zmod n) where
  hAdd a b :=
    match n with
      | 0 => toZmod (fromZmod a + fromZmod b)
      | (n + 1) => sorry
end Zmod