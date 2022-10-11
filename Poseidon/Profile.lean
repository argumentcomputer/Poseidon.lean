import YatimaStdLib.Zmod

namespace Poseidon

structure Profile where
  (N t fullRounds partialRounds prime : Nat)
  a : Int
  sBox : Zmod prime → Zmod prime := fun n => 
    match a with
    | .ofNat a => n^a
    | _        => Zmod.modInv n

def Profile.n (p : Profile) := p.N/p.t 