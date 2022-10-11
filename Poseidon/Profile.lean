import YatimaStdLib.Zmod

namespace Poseidon

structure Profile where
  (N t fullRounds partialRounds prime : Nat)
  sBox : Zmod prime → Zmod prime

def Profile.n (p : Profile) := p.N/p.t 