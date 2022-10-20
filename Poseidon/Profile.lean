import YatimaStdLib.Zmod

namespace Poseidon

structure SecProfile where
  M : Nat -- Security 
  t : Nat -- Internal capacity
  p : Nat -- Prime
  a : Int -- SBox exponent

structure HashProfile extends SecProfile where
  fullRounds : Nat
  partRounds : Nat

open Zmod in
def HashProfile.sBox (profile : HashProfile) : Zmod profile.p → Zmod profile.p := 
  match profile.a with
  | .ofNat n => fun x => x^n
  | .negSucc n => fun x => (.modInv x)^(n + 1)