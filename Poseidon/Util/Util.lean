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

lemma mul_le_mul_iff_left {a b c : Nat} (h : a > 0) : a * b ≤ a * c ↔ b ≤ c :=
  Iff.intro (flip (@Nat.le_of_mul_le_mul_left b c a) h) (@Nat.mul_le_mul_left b c a)

lemma le_mul_iff_one_le_right₁ {a b : Nat} (h : 0 < b) : a ≤ a * b → 1 ≤ b := by
  induction a
  intro
  assumption
  intro
  assumption

lemma le_mul_iff_one_le_right₂ {a b : Nat} : 1 ≤ b → a ≤ a * b := by
  intro h
  induction a
  rw [Nat.zero_mul]
  exact (Nat.le_refl 0)
  rw [Nat.succ_mul]
  rw [←Nat.add_one]
  apply Nat.add_le_add
  assumption
  exact h

theorem le_mul_iff_one_le_right
  {a b : Nat} (h : 0 < b) : a ≤ a * b ↔ 1 ≤ b := 
  Iff.intro (le_mul_iff_one_le_right₁ h) (fun _ => le_mul_iff_one_le_right₂ h)

theorem lt_add_of_lt_of_nonneg
  {a b c : Nat} : b < c → 0 ≤ a → b < c + a :=
  Nat.add_zero b ▸ add_lt_add_of_lt_of_le

lemma lt_add_iff_pos_right₁ {a b : Nat} : a < a + b → 0 < b := by
  induction a
  intro h
  rw [Nat.zero_add] at *
  exact h
  intro h
  rw [Nat.succ_add] at *
  sorry

lemma lt_add_iff_pos_right₂ {a b : Nat} : 0 < b → a < a + b := by
  intro h
  induction a
  rw [Nat.zero_add]
  exact h
  rw [Nat.succ_add] at *
  apply Nat.succ_lt_succ
  assumption

theorem lt_add_iff_pos_right
  (a : Nat) {b : Nat} : a < a + b ↔ 0 < b :=
  Iff.intro lt_add_iff_pos_right₁ lt_add_iff_pos_right₂

theorem add_pos_of_pos_of_nonneg
  {a b : Nat} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  Nat.zero_add 0 ▸ add_lt_add_of_lt_of_le ha hb

lemma one_le_iff_ne_zero₁ {n : Nat} (p : 1 ≤ n) : n ≠ 0 := by
  induction n
  contradiction
  exact (Nat.succ_ne_zero _)

lemma one_leq_succ {n : Nat} : 1 ≤ Nat.succ n := by
  induction n
  exact Nat.le_refl 1
  sorry

lemma one_le_iff_ne_zero₂ {n : Nat} (p : n ≠ 0) : 1 ≤ n := by
  induction n
  contradiction
  exact one_leq_succ

theorem one_le_iff_ne_zero {n : Nat} : 1 ≤ n ↔ n ≠ 0 := 
  Iff.intro one_le_iff_ne_zero₁ one_le_iff_ne_zero₂

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