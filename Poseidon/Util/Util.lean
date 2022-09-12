import Mathbin

namespace Util

def iterate {A : Sort u} (n : ℕ) (f : A → A) : A → A :=
  match n with
    | .zero => id
    | .succ k => f ∘ (iterate k f)

namespace Fin

def fin_coercion (ho : o < r + cap) : Finₓ o → Finₓ (r + cap) :=
  λ (i : Finₓ o) => 
    (⟨(i : ℕ), lt_of_le_of_ltₓ (le_of_ltₓ i.prop) ho⟩ : Finₓ (r + cap))

end Fin

end Util