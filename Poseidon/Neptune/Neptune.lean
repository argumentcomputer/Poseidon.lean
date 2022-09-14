import Mathbin.Data.Fin.Basic
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Zmod.Algebra
import Poseidon.Util.Util

noncomputable section

open Util

namespace Neptune

variable (p t : ℕ) [Fact p.Prime] [Field (Zmod p)] [Fintype (Finₓ t)]

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

def iterate {A : Sort u} (n : ℕ) (f : A → A) : A → A :=
  match n with
    | .zero => id
    | .succ k => f ∘ (iterate k f)

/- The Poseidon permutation function, takes as input `t` elements, and returns `t` elements;
  this is defined in terms of compositions of `R_f_round` and `R_p_round`. -/
def P_perm (R_f R_p : ℕ) (S_box' : Zmod p → Zmod p) (c a : Finₓ t → Zmod p)
  (MDS' : Matrix (Finₓ t) (Finₓ t) (Zmod p)) : Finₓ t → Zmod p :=
  (iterate R_f (R_f_round p t S_box' c MDS')) ((iterate R_p (R_p_round p t S_box' c MDS'))
  ((iterate R_f $ R_f_round p t S_box' c MDS') a))

/- Adding an `r`-chunk to the state. -/
def add_to_state (r : ℕ) (m : Finₓ r → Zmod p) 
  (a : Finₓ t → Zmod p) : Finₓ t → Zmod p :=
  λ i => dite ((i : ℕ) < r) (λ h => a i + m (Finₓ.castLt i h)) (λ _ => a i)

def fin_coercion (ho : o < r + cap) : Finₓ o → Finₓ (r + cap) :=
  λ (i : Finₓ o) => 
    (⟨(i : ℕ), lt_of_le_of_ltₓ (le_of_ltₓ i.prop) ho⟩ : Finₓ (r + cap))

lemma helper_1 (d r cap : ℕ) (j : Finₓ (d * r + (r + cap))) :
  ↑j + r < d.succ * r + (r + cap) := by
    have h1 : d.succ * r + (r + cap) = d * r + (r + cap) + r := by
      rw [add_assoc]
      rw [add_comm _ r]
      rw [← add_assoc _ _ (r + cap)] 
      rw [← Nat.succ_mul]
    rw [h1]
    apply add_lt_add_of_lt_of_le j.prop le_rfl

def r_elements_of_zmodp (r d cap : ℕ) 
                        (a : Finₓ ((.succ d) * r + (r + cap)) → Zmod p)
                        (hr : 1 ≤ r) : Finₓ r → Zmod p := 
  (λ (j : Finₓ r) => 
    a ⟨(.succ d) + j, 
        add_lt_add_of_le_of_lt ((le_mul_iff_one_le_right (Nat.succ_posₓ _)).2 hr)
          (lt_add_of_lt_of_nonneg j.prop (Nat.zero_leₓ _))⟩) 

def helper_step (d r : ℕ)
                (a : Finₓ ((.succ d) * r + (r + cap)) → Zmod p) 
                (j : Finₓ (d * r + (r + cap))) : ¬j.val < (Nat.succ d) * r → Zmod p := 
  λ _ => a ⟨(j : ℕ) + r, helper_1 d r cap j⟩

def simplifications (d r cap : ℕ) (a : Finₓ ((.succ d) * r + (r + cap)) → Zmod p) 
                    (hr : 1 ≤ r) (j : Finₓ (d * r + (r + cap))) : j.val < (Nat.succ d) * r → Zmod p :=
  λ h => 
    a (Finₓ.castLt j (lt_transₓ h
              ((lt_add_iff_pos_right _).2 (add_pos_of_pos_of_nonneg (Nat.pos_of_ne_zeroₓ
                (Nat.one_le_iff_ne_zero.1 hr)) (Nat.zero_leₓ _)))))

def compose_MDS (R_f R_p r cap : ℕ) (hr : 1 ≤ r) 
                (S_box : Zmod p → Zmod p) (c : Finₓ (r + cap) → Zmod p) 
                (MDS : Matrix (Finₓ (r + cap)) (Finₓ (r + cap)) (Zmod p)) (k : ℕ) 
                (a : Finₓ (k * r + (r + cap)) → Zmod p) : Finₓ (r + cap) → Zmod p :=
  by induction k with
    | zero => 
        rw [Nat.zero_mul] at a 
        rw [zero_add] at a;
        refine λ i => P_perm p (r + cap) R_p R_f S_box c a MDS i
    | succ d hd => 
        refine (λ i => P_perm p (r + cap) R_p R_f S_box c
                         (add_to_state p (r + cap) r (r_elements_of_zmodp p r d cap a hr) 
                            (hd (λ j => dite ((j : ℕ) < (.succ d) * r) 
                                          (simplifications p d r cap a hr j) 
                                          (helper_step p d r a j)
                                          )))
                             MDS 
                             i)

/- The Poseidon hash function, takes `N` bits and returns `o` `𝔽_p`-elements. -/
def P_hash (R_f R_p r o cap : ℕ) (hr : 1 ≤ r) (S_box : Zmod p → Zmod p) 
  (c : Finₓ (r + cap) → Zmod p)
  (MDS : Matrix (Finₓ (r + cap)) (Finₓ (r + cap)) (Zmod p)) (ho : o < r + cap)
  (k : ℕ) (a : Finₓ (k * r + (r + cap)) → Zmod p) : Finₓ o → Zmod p :=
  @Function.comp (Finₓ o) (Finₓ (r + cap)) (Zmod p)
    (compose_MDS p R_f R_p r cap hr S_box c MDS k a)
    (fin_coercion ho)

end Neptune