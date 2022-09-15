import Mathlib.Init.Algebra.Order

namespace Util

def castLt (i : Fin m) (h : i.1 < n) : Fin n := ⟨i.1, h⟩

instance : Preorder Nat where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry

section Nat

/- It must be in mathlib but I haven't found those definitions for
natural numbers, currently most of the formulated for integers only
-/
theorem add_lt_add_of_lt_of_le 
  {a b c d : Nat} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (Nat.add_lt_add_right h₁ c) (Nat.add_le_add_left h₂ b)

theorem add_lt_add_of_le_of_lt 
  {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
  lt_of_le_of_lt (Nat.add_le_add_right h₁ c) (Nat.add_lt_add_left h₂ b)

lemma mul_le_mul_iff_left {a b c : Nat} : a * b ≤ a * c ↔ b ≤ c :=
  Iff.intro sorry sorry

theorem le_mul_iff_one_le_right
  {a b : Nat} (x : 0 < b) : a ≤ a * b ↔ 1 ≤ b := 
  Iff.trans (by rw [Nat.mul_one]) mul_le_mul_iff_left

theorem lt_add_of_lt_of_nonneg
  {a b c : Nat} : b < c → 0 ≤ a → b < c + a :=
  Nat.add_zero b ▸ add_lt_add_of_lt_of_le

theorem lt_add_iff_pos_right
  (a : Nat) {b : Nat} : a < a + b ↔ 0 < b := by
  apply Iff.intro 
  . induction a
    rw [Nat.zero_add b]
    intro h
    exact h
    intro h
    rw [Nat.succ_add] at *
    simp [Nat.lt_of_succ_lt_succ] at h
    sorry
  . induction a
    intros
    rw [Nat.zero_add] at *
    exact
    sorry


theorem add_pos_of_pos_of_nonneg
  {a b : Nat} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  Nat.zero_add 0 ▸ add_lt_add_of_lt_of_le ha hb

theorem one_le_iff_ne_zero {n : Nat} : 1 ≤ n ↔ n ≠ 0 := sorry

end Nat

section Fin

def fin_coercion (ho : o < r + cap) : Fin o → Fin (r + cap) :=
  λ (i : Fin o) => 
    (⟨(i : Nat), lt_of_le_of_lt (le_of_lt i.2) ho⟩ : Fin (r + cap))

lemma helper (d r cap : Nat) (j : Fin (d * r + (r + cap))) :
  ↑j + r < (d + 1) * r + (r + cap) := by
    have h1 : d.succ * r + (r + cap) = d * r + (r + cap) + r := by
      rw [Nat.add_assoc]
      rw [Nat.add_comm _ r]
      rw [← Nat.add_assoc _ _ (r + cap)] 
      rw [← Nat.succ_mul]
    rw [h1]
    apply add_lt_add_of_lt_of_le j.2 (Nat.le_refl r)

end Fin

end Util