import Poseidon.Util.ZMod
import Poseidon.Util.AbstractMatrix
import Poseidon.Util.Lemmas

import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Lemmas

namespace Unsafe

open ZMod Matrix Util Nat

variable (p t : Nat)

/- The AddRoundConstant linear step of a single round of the Poseidon permutation -/
def ARC (c a : Vector (ZMod p) t) : Vector (ZMod p) t := c + a

/- An `R_f`-round, that is, a full round. -/
def R_f_round (S_box' : ZMod p → ZMod p) (c : Vector (ZMod p) t)
    (MDS : Matrix (ZMod p) t t) (a : Vector (ZMod p) t) : Vector (ZMod p) t :=
    matrixVecAction MDS $ fun i => S_box' (ARC p t c a i)

/- An `R_p`-round, that is, a partial round. -/
def R_p_round (S_box' : ZMod p → ZMod p) (c : Vector (ZMod p) t)
    (MDS : Matrix (ZMod p) t t) (a : Vector (ZMod p) t) : Vector (ZMod p) t :=
    matrixVecAction MDS
      (λ i => dite ((i : Nat) = 0) (λ _ => S_box' (ARC p t c a i)) (λ _ => ARC p t c a i))

def iterate {A : Sort u} (n : Nat) (f : A → A) : A → A :=
  match n with
    | 0 => id
    | (k + 1) => f ∘ (iterate k f)

/- The Poseidon permutation function, takes as input `t` elements, and returns `t` elements;
  this is defined in terms of compositions of `R_f_round` and `R_p_round`. -/
def P_perm (R_f R_p : Nat) (S_box' : ZMod p → ZMod p) (c a : Vector (ZMod p) t) 
    (MDS : Matrix (ZMod p) t t) : Vector (ZMod p) t :=
    (iterate R_f (R_f_round p t S_box' c MDS)) ((iterate R_p (R_p_round p t S_box' c MDS))
      ((iterate R_f $ R_f_round p t S_box' c MDS) a))

/- Adding an `r`-chunk to the state. -/
def add_to_state (r : Nat) (m : Vector (ZMod p) r) 
  (a : Vector (ZMod p) t) : Vector (ZMod p) t :=
  λ i => dite ((i : Nat) < r) (λ h => a i + m (castLt i h)) (λ _ => a i)

def r_elements_of_ZModp (r d cap : Nat) 
                        (a : Vector (ZMod p) ((d + 1) * r + (r + cap)))
                        (hr : 1 ≤ r) : Vector (ZMod p) r := 
  (λ (j : Fin r) => 
    a ⟨(d + 1) + j, 
        add_lt_add_of_le_of_lt ((le_mul_iff_one_le_right (Nat.succ_pos _)).2 hr) -- TODO : Fix this
          (lt_add_of_lt_of_nonneg j.2 (Nat.zero_le _))⟩) 

def helper_step (d r : Nat)
                (a : Vector (ZMod p) ((d + 1) * r + (r + cap))) 
                (j : Fin (d * r + (r + cap))) : ¬j.1 < (d + 1) * r → ZMod p := 
  λ _ => a ⟨(j : Nat) + r, helper d r cap j⟩

def simplifications (d r cap : Nat) (a : Vector (ZMod p) ((d + 1) * r + (r + cap))) 
                    (hr : 1 ≤ r) (j : Fin (d * r + (r + cap))) : j.val < (Nat.succ d) * r → ZMod p :=
  λ h => 
    a (castLt j (lt_trans h
              ((lt_add_iff_pos_right _).2 (add_pos_of_pos_of_nonneg (Nat.pos_of_ne_zero
                (one_le_iff_ne_zero.1 hr)) (Nat.zero_le _)))))

def compose_MDS (R_f R_p r cap : Nat) (hr : 1 ≤ r) 
                (S_box : ZMod p → ZMod p) (c : Vector (ZMod p) (r + cap)) 
                (MDS : Matrix (ZMod p) (r + cap) (r + cap)) (k : Nat) 
                (a : Vector (ZMod p) (k * r + (r + cap))) : Vector (ZMod p) (r + cap) :=
  match k with
    | 0 => by
      rw [Nat.zero_mul] at a 
      rw [Nat.zero_add] at a;
      refine λ i => P_perm p (r + cap) R_p R_f S_box c a MDS i
    | (d + 1) => by
        let rec_call := compose_MDS R_f R_p r cap hr S_box c MDS d 
        refine (λ i => P_perm p (r + cap) R_p R_f S_box c
                         (add_to_state p (r + cap) r (r_elements_of_ZModp p r d cap a hr) 
                            (rec_call (λ j => dite ((j : ℕ) < (.succ d) * r) 
                                          (simplifications p d r cap a hr j) 
                                          (helper_step p d r a j)
                                          )))
                             MDS 
                             i)

/- The Poseidon hash function, takes `N` bits and returns `o` `𝔽_p`-elements. -/
def P_hash (R_f R_p r o cap : Nat) (hr : 1 ≤ r) (S_box : ZMod p → ZMod p) 
  (c : Vector (ZMod p) (r + cap))
  (MDS : Matrix (ZMod p) (r + cap) (r + cap)) (ho : o < r + cap)
  (k : Nat) (a : Vector (ZMod p) (k * r + (r + cap))) : Vector (ZMod p) o :=
  @Function.comp (Fin o) (Fin (r + cap)) (ZMod p)
    (compose_MDS p R_f R_p r cap hr S_box c MDS k a)
    (fin_coercion ho)
end Unsafe
