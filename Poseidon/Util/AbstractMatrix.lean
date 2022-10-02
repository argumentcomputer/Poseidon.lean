/-
This is oen attempt at writing down the implementation of a Matrix/Vector library for Poseidon.
I'm fairly certain this would be unwieldy to use in practice, so we prefer the implementation in
`Matrix.lean`.

WARNING: There's like a 50% chance I got the transposes wrong in these definitions, so the first
step is going to be to test if it's right
-/
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

infixl:50 "⬝" => dotProduct

def transpose (m : Matrix A r c) : Matrix A c r := fun ⟨i, hi⟩ ⟨j, hj⟩ => m ⟨j, hj⟩ ⟨i, hi⟩

postfix:max "ᵀ" => transpose

variable (m : Matrix A r c) (k : Fin r) (v : Vector A c)

def matrixVecAction (m : Matrix A r c) (v : Vector A c) : Vector A r := 
  fun ⟨i, h⟩ => mᵀ ⟨i, h⟩ ⬝ v

instance : HMul (Matrix A r c) (Vector A c) (Vector A r) := ⟨matrixVecAction⟩

def matrixMul (m : Matrix A r c) (m' : Matrix A c r') : Matrix A r r' := 
  fun ⟨i, hi⟩ ⟨j, hj⟩ => mᵀ ⟨j, hj⟩ ⬝ m' ⟨i, hi⟩

instance : HMul (Matrix A r c) (Matrix A c r') (Matrix A r r') := ⟨matrixMul⟩

def vectorSum (v₁ v₂ : Vector A c) : Vector A c :=
  fun i => v₁ i + v₂ i

instance : HAdd (Vector A c) (Vector A c) (Vector A c) := ⟨vectorSum⟩

end Matrix

/-
It'd be nice if we could use these definitions to keep track of the dimension of the vectors and
matrices, but we don't have enough Array lemmas in Std4 yet to fill in all the proofs...
-/

-- structure Vector (dim : Nat) (R : Type) [Ring R] where
--   data : Array R
--   size_eq : data.size = dim

-- namespace Vector

-- #check zip_data

-- variable (R : Type) [Ring R]

-- def add (v w : Vector n R) : Vector n R := 
--   let ⟨vVec, vLen⟩ := v
--   let ⟨wVec, wLen⟩ := w
--   ⟨vVec.zip wVec |>.map fun (x, y) => x + y, sorry ⟩

-- end Vector 

-- structure Matrix (r c : Nat) (R : Type) [Ring R] where
--   data : Array (Vector r R) 
--   col_eq : data.size = c
