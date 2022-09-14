/-
I'm not sure which of the following two approaches is actually better so I implemented both of them

WARNING: There's like a 50% chance I got the transposes wrong in these definitions, so the first
step is going to be to test if it's right
-/
section abstract_linear_algebra

def Vector (A : Type) (n : Nat) : Type := Fin n → A

def Matrix (A : Type) (r c : Nat) : Type := Fin c → Fin r → A

namespace Matrix

variable [Inhabited A] [Add A] [Mul A] [OfNat A 0]

def last (f : Fin n.succ → A) : Fin n → A := f ∘ Fin.succ

open Nat in
theorem lt_succ (n : Nat) : n < n + 1 := by
  rw [add_one]
  apply lt_succ_of_le
  apply Nat.le_refl

def sum (f : Fin n → A) : A := match n with
  | 0 => 0
  | n + 1 => f ⟨n, lt_succ n⟩ + sum (last f)

def dotProduct (v w : Vector A c) : A := sum fun ⟨i, h⟩ => v ⟨i, h⟩ * w ⟨i, h⟩

infixl:50 " ⬝ " => dotProduct

def transpose (m : Matrix A r c) : Matrix A c r := fun ⟨i, hi⟩ ⟨j, hj⟩ => m ⟨j, hj⟩ ⟨i, hi⟩

postfix:max "ᵀ" => transpose

variable (m : Matrix A r c) (k : Fin r) (v : Vector A c)

def matrixVecAction (m : Matrix A r c) (v : Vector A c) : Vector A r := 
  fun ⟨i, h⟩ => mᵀ ⟨i, h⟩ ⬝ v

instance : HMul (Matrix A r c) (Vector A c) (Vector A r) := ⟨matrixVecAction⟩

def matrixMul (m : Matrix A r c) (m' : Matrix A c r') : Matrix A r r' := 
  fun ⟨i, hi⟩ ⟨j, hj⟩ => mᵀ ⟨j, hj⟩ ⬝ m' ⟨i, hi⟩

instance : HMul (Matrix A r c) (Matrix A c r') (Matrix A r r') := ⟨matrixMul⟩

end Matrix

end abstract_linear_algebra

section concrete_linear_algebra



end concrete_linear_algebra

-- def array_to_fun (x : Array A) : Fin (Array.size x) → A :=
--   fun i => x[i]

-- def sum (x : Array A) : A := 
--   Array.foldl (. + .) 0 x

-- def dotProduct (x : Array A) (y : Array A) : A :=
--   sum A $ Array.zipWith x y (. * .)