namespace Util

namespace Matrix

variable (A : Type) [Inhabited A] [HAdd A A A] [HMul A A A] [OfNat A 0]

def Matrix : Type := Array (Array A)

def array_to_fun (x : Array A) : Fin (Array.size x) → A :=
  fun i => x[i]

def sum (x : Array A) : A := 
  Array.foldl (. + .) 0 x

def dotProduct(x : Array A) (y : Array A) : A :=
  sum A $ Array.zipWith x y (. * .)

end Matrix

end Util