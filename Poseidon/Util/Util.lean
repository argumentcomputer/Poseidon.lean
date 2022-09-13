namespace Util

namespace Matrix

def Matrix (A : Type u) : Type u := Array (Array A)

def array_to_fun {A : Type} [Inhabited A] (x : Array A) : Fin (Array.size x) → A :=
  fun i => x[i]

def sum {A : Type} [HAdd A A A] [OfNat A 0] (x : Array A) : A := 
  Array.foldl (. + .) 0 x

def dotProduct [HMul A A A] [HAdd A A A] [OfNat A 0] (x : Array A) (y : Array A) : A :=
  sum $ Array.zipWith x y (. * .)

end Matrix

end Util