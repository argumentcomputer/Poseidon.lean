import Poseidon.HashImpl
import Poseidon.Parameters.Lurk

/-!
# Parameters for Lurk Profile

This module contains the definitions necessary to use the exact profile,
context, and input formatting to mirror the Poseidon hashing used in Lurk.
-/

namespace Poseidon.Lurk

abbrev F := Zmod Lurk.Profile.p

/-- The pre-computed hashing context used by Lurk. -/
def Context : Hash.Context Profile := ⟨Lurk.MDS, Lurk.roundConstants⟩

/--
The hashing function used by Lurk that uses pre-initialized Lurk parameters and
constants.
-/
def hash (f₁ f₂ f₃ f₄ : F) : F :=
  Poseidon.hash Profile Context #[f₁, f₂, f₃, f₄] .merkleTree
