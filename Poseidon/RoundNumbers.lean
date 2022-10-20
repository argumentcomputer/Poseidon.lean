import Poseidon.Profile
import YatimaStdLib.Float
import YatimaStdLib.List
import YatimaStdLib.Nat
import YatimaStdLib.NonEmpty

/-!
# Calculate Round Numbers

This file calculates the **Round Numbers** (`partialRounds` and `fullRounds` in `Poseidon.Profile`)
This is an implementation of the Python algorithm found in the reference implementation which 
generates round numbers satisfying the following _security inequalities_, while minimizing the 
number of _SBox_ calls:

1) `2^M ≤ p^t`: Ensures sufficient data throughput
Note: This is manifestly satisfied by the chosen `p, M, t` for Filecoin/Lurk

2) `fullRounds ≥ 6`: Ensures protection from statistical attacks

Let `R = partialRounds + fullRounds`, and let the S-box be given by `x ↦ xᵃ`

3) `R > M logₐ2 + logₐt`:  Ensures protection from interpolation attacks
Note: This simplifies to `R > 57 or 58` for Filecoin/Lurk's chosen parameters

4a) `R > M logₐ2 / 3`
4b) `R > t - 1 + M logₐ2 / (t + 1)` Ensuring protection from Gaussian elimination attacks
Note: `4a)` simplifies to `R > 18.3` for Filecoin/Lurk's chosen parameters

The 
-/

private instance : Coe Nat Float := ⟨UInt64.toFloat ∘ Nat.toUInt64⟩

private instance : Coe Int Float where
  coe n := match n with
    | .ofNat n   => Nat.toFloat n
    | .negSucc n => - Nat.toFloat n.succ

open Float (log log2 ceil toNat floor logBase)

/--
Taken from the reference implementation
TODO : Double check this with the white paper, because there are some weird things going on here...
-/
def securityTest (p t rF rP M : Nat) (a : Int) : Bool :=
  let n := p.log2 + 1
  if a > 0 then
  -- R_F_1 = 6 if M <= ((floor(log(p, 2) - ((alpha-1)/2.0))) * (t + 1)) else 10 # Statistical
    let rF1 := if M ≤ (floor <| n - 0.5 * (a - 1)) * (t + 1) then 6 else 10
  -- R_F_2 = 1 + ceil(log(2, alpha) * min(M, n)) + ceil(log(t, alpha)) - R_P # Interpolation
    let rF2 := 1 + ceil (log2 a * min M n) + ceil (logBase t a) - rP.toFloat
  -- R_F_3 = 1 + (log(2, alpha) * min(M/float(3), log(p, 2)/float(2))) - R_P
    let rF3 := 1 + (log2 a) * ⟦M.toFloat / 3, 0.5 * n⟧.min - rP.toFloat
  -- R_F_4 = t - 1 + min((log(2, alpha) * M) / float(t+1), ((log(2, alpha)*log(p, 2)) / float(2))) - R_P
    let rF4 := t - 1 + ⟦log2 a * M / (t + 1), log2 a * n / 2⟧.min - rP.toFloat -- log2 vs logBase? <-  Check this
    let rFMax := ⟦rF1, rF2, rF3, rF4⟧.map (toNat ∘ ceil) |>.max
    rF >= rFMax
  else if a == -1 then
    let rF1 := if M ≤ floor (log2 p - 2) * (t + 1) then 6 else 10
    let rP1 := 1 + ceil (0.5 * min M n) + ceil (log2 t) - floor (rF * log2 t)
    -- `rP2 = rP1` in the reference implementation, so this is most certainly wrong
    let rP3 := t - 1 + ceil (log2 t) + ⟦ceil (0.5 * log2 p) - floor (rF * log2 t), ceil $ M / (t + 1)⟧.min
    let rFMax := toNat $ ceil rF1
    let rPMax := ⟦rP1, rP3⟧.map (toNat ∘ ceil) |>.max
    rFMax ≤ rF && rPMax ≤ rP
  else
    false

/--
Taken from the Python implementation
-/
def securityTest' (p t M rF rP : Nat) (a : Int) : Bool :=
  let primeBitLen := p.log2 + 1 -- FIXME : I don't like this `+ 1` fix, but it works for now.
  let c := if a > 0 then log2 (a - 1) else 2
  let fullRoundStat : Float := if M ≤ (floor (primeBitLen) - c) * (t + 1) then 6 else 10
  if a > 0 then
    let fullRoundIter : Float := ceil ((logBase a 2) * min M primeBitLen) 
                               + ceil (logBase a t) - rP.toFloat + 1
    let fullRoundGrob1 : Float := (logBase a 2) * min (M.toFloat/3) (primeBitLen.toFloat/2) 
                                  - rP.toFloat + 1
    let fullRoundGrob2 : Float := min ((logBase a 2) * M / (t + 1)) ((logBase a 2) * M / 2) 
                                  - rP.toFloat + t.toFloat - 1 
    let fullRoundMax := ⟦fullRoundStat, fullRoundIter, 
                         fullRoundGrob1, fullRoundGrob2⟧ |>.map (toNat ∘ ceil)
                                                         |>.max
    rF ≥ fullRoundMax
  else if a == -1 then
    let parRoundIter : Float := ceil (0.5 * min M.toFloat primeBitLen) + ceil (log2 t) 
                                - floor (rF.toFloat * log2 t) + 1
    let parRoundGrob2 : Float := 
      ceil (0.5 * min ( ceil (M.toFloat / (t + 1))) (ceil (0.5 * primeBitLen.toFloat))) 
      + ceil (log2 t) + t - 1 - floor (rF * log2 t)
    let fullRoundMax := (toNat ∘ ceil) fullRoundStat
    let parRoundMax := ⟦parRoundIter, parRoundGrob2⟧ |>.map (toNat ∘ ceil)
                                                     |>.max
    rF ≥ fullRoundMax && rP ≥ parRoundMax 
  else
    false -- Any other value of `a` should be deemed insecure and not return any round numbers

def sBoxCost (rF rP t : Nat) : Nat := t * rF + rP 

def sizeCost (rF rP N t : Nat) : Nat := 
  let n := toNat ∘ ceil <| N.toFloat / t.toFloat
  N * rF + n * rP

def depthCost (rF rP : Nat) : Nat := rF + rP

def findRoundNumbers (p t M : Nat) (a : Int) (secMargin : Bool) : Nat × Nat := Id.run do
  let mut rP := 0
  let mut rF := 0
  let mut cost := 0
  let mut minCost := t * 100 + 500 + 1
  let mut maxRF := 0
  for rPT in [1 : 501] do
    for rFT in [4 : 101 : 2] do
      if securityTest' p t M rFT rPT a then
        let (rFT', rPT') := if secMargin then (rFT + 2, toNat ∘ ceil $ rPT.toFloat * 1.075) 
                                         else (rFT, rPT)
        cost := sBoxCost rFT' rPT' t
        if cost < minCost || (cost == minCost && rFT' ≤ maxRF) then
          rP := rPT'
          rF := rFT'
          minCost := cost
          maxRF := rF
  return (rF, rP)
