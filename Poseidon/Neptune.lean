import Mathbin.Data.Fin.Basic
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Zmod.Algebra

noncomputable section

namespace Neptune

variable {p t : ℕ} [Fact p.Prime] [Field (Zmod p)] [Fintype (Finₓ t)]
variable {R_f R_p : ℕ}

/- The AddRoundConstant linear step of a single round of the Poseidon permutation -/
def ARC (c a : Finₓ t → Zmod p) (i : Finₓ t) : Zmod p := (a i) + (c i)

/- An `R_f`-round, that is, a full round. -/
def R_f_round (S_box' : Zmod p → Zmod p) (c : Finₓ t → Zmod p)
  (MDS' : Matrix (Finₓ t) (Finₓ t) (Zmod p)) (a : Finₓ t → Zmod p) : Finₓ t → Zmod p :=
  Matrix.mulVecₓ MDS' (λ i => S_box' (ARC p t c a i))

/- An `R_p`-round, that is, a partial round. -/
def R_p_round (S_box' : Zmod p → Zmod p) (c : Finₓ t → Zmod p)
  (MDS' : Matrix (Finₓ t) (Finₓ t) (Zmod p)) (a : Finₓ t → Zmod p) : Finₓ t → Zmod p :=
  Matrix.mulVecₓ MDS' 
    (λ i => dite ((i : ℕ) = 0) (λ _ => S_box' (ARC p t c a i)) (λ _ => ARC p t c a i))

/- The Poseidon permutation function, takes as input `t` elements, and returns `t` elements;
  this is defined in terms of compositions of `R_f_round` and `R_p_round`. -/
def P_perm (S_box' : Zmod p → Zmod p) (c a : Finₓ t → Zmod p)
  (MDS' : Matrix (Finₓ t) (Finₓ t) (Zmod p)) : Finₓ t → Zmod p :=
  (R_f_round S_box' c MDS')^[R_f] ((R_p_round S_box' c MDS')^[R_p]
  ((R_f_round S_box' c MDS')^[R_f] a))

/- Adding an `r`-chunk to the state. -/
def add_to_state (r cap : ℕ) (m : Finₓ r → Zmod p) 
  (a : Finₓ t → Zmod p) (h : t = r + cap) : Finₓ t → Zmod p :=
  λ i => dite ((i : ℕ) < r) (λ h => a i + m (Finₓ.castLt i h)) (λ h => a i)

lemma helper_1 (d r cap : ℕ) (j : Finₓ (d * r + (r + cap))) :
  ↑j + r < d.succ * r + (r + cap) := by
    have h1 : d.succ * r + (r + cap) = d * r + (r + cap) + r := by
      rw [add_assoc]
      rw [add_comm _ r]
      rw [← add_assoc _ _ (r + cap)] 
      rw [← Nat.succ_mul]
    rw [h1]
    apply add_lt_add_of_lt_of_le j.prop le_rfl

/-- The Poseidon hash function, takes `N` bits and returns `o` `𝔽_p`-elements. -/
def P_hash (R_f R_p r o cap : ℕ) (hr : 1 ≤ r) (S_box' : Zmod p → Zmod p) 
  (c : Finₓ (r + cap) → Zmod p)
  (MDS' : Matrix (Finₓ (r + cap)) (Finₓ (r + cap)) (Zmod p)) (ho : o ≤ r + cap)
  (k : ℕ) (a : Finₓ (k * r + (r + cap)) → Zmod p) : Finₓ o → Zmod p := by sorry
/- 
  @Function.comp (Finₓ o) (Finₓ (r + cap)) (Zmod p)
  by induction k with d hd,
  { rw [zero_mul, zero_add] at *
  { refine λ i, P_perm' p (r + cap) R_p R_f S_box' c a MDS' i }
    refine λ i, P_perm' p (r + cap) R_p R_f S_box' c (add_to_state' p (r + cap) r cap
      (λ j, a ⟨d.succ + j, add_lt_add_of_le_of_lt ((le_mul_iff_one_le_right (nat.succ_pos _)).2 hr)
      (lt_add_of_lt_of_nonneg j.prop (nat.zero_le _))⟩)
      (hd (λ j, dite ((j : ℕ) < d.succ * r) (λ h, a (Finₓ.castLt j (lt_trans h
      ((lt_add_iff_pos_right _).2 (add_pos_of_pos_of_nonneg (nat.pos_of_ne_zero
      (Nat.one_le_iff_ne_zero.1 hr)) (nat.zero_le _)))))) (λ h, a ⟨(j : ℕ) + r
      helper_1 d r cap j⟩))) rfl) MDS' i }
  (λ (i : Finₓ o) => (⟨(i : ℕ), lt_of_lt_of_le i.prop ho⟩ : Finₓ (r + cap)) : Finₓ o → Finₓ (r + cap))
-/

end Neptune