import Poseidon.HashImpl
import Poseidon.Parameters.Lurk

open Poseidon

abbrev F' := Zmod Lurk.Profile.p

def Lurk.Context : Hash.Context Lurk.Profile := ⟨Lurk.MDS, Lurk.roundConstants⟩

def Lurk.Hash : F' → F' → F' → F' → F'
  | f₁, f₂, f₃, f₄ => hash Lurk.Profile Lurk.Context #[f₁, f₂, f₃, f₄] .merkleTree