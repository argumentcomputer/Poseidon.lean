import Mathlib.Init.Algebra.Order

namespace Util

def castLt (i : Fin m) (h : i.1 < n) : Fin n := ⟨i.1, h⟩

instance : Preorder Nat where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry

section Nat

theorem add_lt_add_of_lt_of_le 
  {a b c d : Nat} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := sorry

theorem add_lt_add_of_le_of_lt 
  {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := sorry

theorem le_mul_iff_one_le_right
  {a b : Nat} : 0 < b → (b ≤ b * a ↔ 1 ≤ a) := sorry

theorem lt_add_of_lt_of_nonneg
  {a b c : Nat} : b < c → 0 ≤ a → b < c + a := sorry

theorem lt_add_iff_pos_right
  (a : Nat) {b : Nat} : a < a + b ↔ 0 < b := sorry

theorem add_pos_of_pos_of_nonneg
  {a b : Nat} : 0 < a → 0 ≤ b → 0 < a + b := sorry

theorem one_le_iff_ne_zero {n : Nat} : 1 ≤ n ↔ n ≠ 0 := sorry

end Nat

end Util