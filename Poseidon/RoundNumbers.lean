import YatimaStdLib.NonEmpty
import YatimaStdLib.List
import YatimaStdLib.Nat

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

-- TODO : Move these to YatimaStdLib?

def NEList.min {α : Type _ } [LE α] [DecidableRel (@LE.le α _)] : NEList α → α
  | .uno a     => a
  | .cons a as => if a ≤ as.min then a else as.min

def NEList.max {α : Type _ } [LE α] [DecidableRel (@LE.le α _)] : NEList α → α
  | .uno a     => a
  | .cons a as => if a ≤ as.max then as.max else a

def allProd (as : List α) (bs : List β) : List (α × β) 
  := as.map (fun a => bs.map fun b => (a, b)) |>.join

def List.minWith (f : α → β) [LE β] [DecidableRel (@LE.le β _)] : List α → Option α 
  | [] => .none
  | a :: as => match as.minWith f with
    | .some a' => if f a ≤ f a' then .some a else .some a'
    | .none => .some a

private def Float.toNat : Float → Nat := USize.toNat ∘ Float.toUSize

private instance : Coe Nat Float := ⟨UInt64.toFloat ∘ Nat.toUInt64⟩

private instance : Coe Int Float where
  coe n := match n with
    | .ofNat n   => Nat.toFloat n
    | .negSucc n => - Nat.toFloat n.succ

open Float (log log2 ceil toNat floor)

private def logBase (base arg : Float) : Float := log arg / log base

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
Take from the Rust implementation
Assumes Filecoin/Poseidon parameters, in particular `a = 5`
-/
def securityTest' (p t rF rP M : Nat) : Bool :=
  let n : Float := p.log2 + 1
  let rFStat := if M <= (n - 3.0) * (t + 1) then 6 else 10
  let rFInterp := 0.43 * M.toFloat + t.log2 - rP
  let rFGrob1 := 0.21 * n - rP
  let rFGrob2 := (0.14 * n - 1.0 - rP) / (t - 1)
  let rFMax := ⟦rFStat, rFInterp, rFGrob1, rFGrob2⟧.map (toNat ∘ ceil) |>.max
  rF >= rFMax

def prime64 := 0xfffffffffffffeff
def prime254 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
def prime255 := 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001

/--
Taken from the Python implementation
-/
def securityTest'' (p t M rF rP : Nat) (a : Int) : Bool :=
  let primeBitLen := p.log2 + 1 -- FIXME : I don't like this `+ 1` fix
  let c := if a > 0 then log2 (a - 1) else 2
  let fullRoundStat : Float := if M ≤ (floor (primeBitLen) - c) * (t + 1) then 6 else 10
  if a > 0 then
    let fullRoundIter : Float := ceil ((logBase a 2) * min M primeBitLen) + ceil (logBase a t) - rP.toFloat + 1
    let fullRoundGrob1 : Float := (logBase a 2) * min (M.toFloat/3) (primeBitLen.toFloat/2) - rP.toFloat + 1
    let fullRoundGrob2 : Float := min ((logBase a 2) * M / (t + 1)) ((logBase a 2) * M / 2) - rP.toFloat + t.toFloat - 1 
    let fullRoundMax := ⟦fullRoundStat, fullRoundIter, 
                         fullRoundGrob1, fullRoundGrob2⟧ |>.map (toNat ∘ ceil)
                                                         |>.max
    rF ≥ fullRoundMax
  else if a == -1 then
    let parRoundIter : Float := ceil (0.5 * min M.toFloat primeBitLen) + ceil (log2 t) - floor (rF.toFloat * log2 t) + 1
    let parRoundGrob2 : Float := ceil (0.5 * min ( ceil (M.toFloat / (t + 1))) (ceil (0.5 * primeBitLen.toFloat))) + ceil (log2 t) + t - 1 - floor (rF * log2 t)
    let fullRoundMax := (toNat ∘ ceil) fullRoundStat
    let parRoundMax := ⟦parRoundIter, parRoundGrob2⟧ |>.map (toNat ∘ ceil)
                                                     |>.max
    rF ≥ fullRoundMax && rP ≥ parRoundMax 
  else
    false

#check StateT.get

#eval 40/1.075
#eval 41/1.075

#eval 37*1.075
#eval 38*1.075

#eval securityTest'' prime64 5 128 6 35 3 -- false
#eval securityTest'' prime64 5 128 6 36 3 -- false
#eval securityTest'' prime64 5 128 6 37 3 -- false
#eval securityTest'' prime64 5 128 6 38 3 -- true

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
      if securityTest'' p t M rFT rPT a then
        let (rFT', rPT') := if secMargin then (rFT + 2, toNat ∘ ceil $ rPT.toFloat * 1.075) else (rFT, rPT)
        cost := sBoxCost rFT' rPT' t
        if cost < minCost || (cost == minCost && rFT' ≤ maxRF) then
          rP := rPT'
          rF := rFT'
          minCost := cost
          maxRF := rF
  return (rF, rP)

#eval findRoundNumbers prime64 5 128 3 true  -- Expecting (8, 41) :)

#eval findRoundNumbers prime255 2 128 3 true

-- [8, 56, 80, 20400]
-- [8, 57, 105, 26775]
-- [8, 56, 80, 20320]
-- [8, 57, 105, 26670]
-- [8, 42, 234, 14976]
-- --- Table x^5 WITH security margin ---
-- M     & N      & n     & t   & rF  & rP                     & sBoxCost & sizeCost 
-- $128$ & $1536$ & $768$ & $2$ & $8$ & $56$ & $\mathbb F_{p}$ & $72$ & $55296$ \\
-- $128$ & $1536$ & $384$ & $4$ & $8$ & $56$ & $\mathbb F_{p}$ & $88$ & $33792$ \\
-- $128$ & $1536$ & $256$ & $6$ & $8$ & $57$ & $\mathbb F_{p}$ & $105$ & $26880$ \\
-- $128$ & $1536$ & $192$ & $8$ & $8$ & $57$ & $\mathbb F_{p}$ & $121$ & $23232$ \\
-- $128$ & $1536$ & $96$ & $16$ & $8$ & $42$ & $\mathbb F_{p}$ & $170$ & $16320$ \\
-- $256$ & $1536$ & $768$ & $2$ & $8$ & $116$ & $\mathbb F_{p}$ & $132$ & $101376$ \\
-- $256$ & $1536$ & $384$ & $4$ & $8$ & $116$ & $\mathbb F_{p}$ & $148$ & $56832$ \\
-- $256$ & $1536$ & $256$ & $6$ & $8$ & $117$ & $\mathbb F_{p}$ & $165$ & $42240$ \\
-- $256$ & $1536$ & $192$ & $8$ & $8$ & $86$ & $\mathbb F_{p}$ & $150$ & $28800$ \\
-- $256$ & $1536$ & $96$ & $16$ & $8$ & $42$ & $\mathbb F_{p}$ & $170$ & $16320$ \\
-- --- Table x^5 WITHOUT security margin ---
-- $128$ & $1536$ & $768$ & $2$ & $6$ & $52$ & $\mathbb F_{p}$ & $64$ & $49152$ \\
-- $128$ & $1536$ & $384$ & $4$ & $6$ & $52$ & $\mathbb F_{p}$ & $76$ & $29184$ \\
-- $128$ & $1536$ & $256$ & $6$ & $6$ & $53$ & $\mathbb F_{p}$ & $89$ & $22784$ \\
-- $128$ & $1536$ & $192$ & $8$ & $6$ & $53$ & $\mathbb F_{p}$ & $101$ & $19392$ \\
-- $128$ & $1536$ & $96$ & $16$ & $6$ & $39$ & $\mathbb F_{p}$ & $135$ & $12960$ \\
-- $256$ & $1536$ & $768$ & $2$ & $6$ & $107$ & $\mathbb F_{p}$ & $119$ & $91392$ \\
-- $256$ & $1536$ & $384$ & $4$ & $6$ & $107$ & $\mathbb F_{p}$ & $131$ & $50304$ \\
-- $256$ & $1536$ & $256$ & $6$ & $6$ & $108$ & $\mathbb F_{p}$ & $144$ & $36864$ \\
-- $256$ & $1536$ & $192$ & $8$ & $6$ & $80$ & $\mathbb F_{p}$ & $128$ & $24576$ \\
-- $256$ & $1536$ & $96$ & $16$ & $6$ & $39$ & $\mathbb F_{p}$ & $135$ & $12960$ \\
-- --- Table x^3 WITH security margin ---
-- $128$ & $1536$ & $768$ & $2$ & $8$ & $83$ & $\mathbb F_{p}$ & $99$ & $76032$ \\
-- $128$ & $1536$ & $384$ & $4$ & $8$ & $84$ & $\mathbb F_{p}$ & $116$ & $44544$ \\
-- $128$ & $1536$ & $256$ & $6$ & $8$ & $84$ & $\mathbb F_{p}$ & $132$ & $33792$ \\
-- $128$ & $1536$ & $192$ & $8$ & $8$ & $84$ & $\mathbb F_{p}$ & $148$ & $28416$ \\
-- $128$ & $1536$ & $96$ & $16$ & $8$ & $64$ & $\mathbb F_{p}$ & $192$ & $18432$ \\
-- $256$ & $1536$ & $768$ & $2$ & $8$ & $170$ & $\mathbb F_{p}$ & $186$ & $142848$ \\
-- $256$ & $1536$ & $384$ & $4$ & $8$ & $171$ & $\mathbb F_{p}$ & $203$ & $77952$ \\
-- $256$ & $1536$ & $256$ & $6$ & $8$ & $171$ & $\mathbb F_{p}$ & $219$ & $56064$ \\
-- $256$ & $1536$ & $192$ & $8$ & $8$ & $128$ & $\mathbb F_{p}$ & $192$ & $36864$ \\
-- $256$ & $1536$ & $96$ & $16$ & $8$ & $64$ & $\mathbb F_{p}$ & $192$ & $18432$ \\
-- --- Table x^3 WITHOUT security margin ---
-- $128$ & $1536$ & $768$ & $2$ & $6$ & $77$ & $\mathbb F_{p}$ & $89$ & $68352$ \\
-- $128$ & $1536$ & $384$ & $4$ & $6$ & $78$ & $\mathbb F_{p}$ & $102$ & $39168$ \\
-- $128$ & $1536$ & $256$ & $6$ & $6$ & $78$ & $\mathbb F_{p}$ & $114$ & $29184$ \\
-- $128$ & $1536$ & $192$ & $8$ & $6$ & $78$ & $\mathbb F_{p}$ & $126$ & $24192$ \\
-- $128$ & $1536$ & $96$ & $16$ & $6$ & $59$ & $\mathbb F_{p}$ & $155$ & $14880$ \\
-- $256$ & $1536$ & $768$ & $2$ & $6$ & $158$ & $\mathbb F_{p}$ & $170$ & $130560$ \\
-- $256$ & $1536$ & $384$ & $4$ & $6$ & $159$ & $\mathbb F_{p}$ & $183$ & $70272$ \\
-- $256$ & $1536$ & $256$ & $6$ & $6$ & $159$ & $\mathbb F_{p}$ & $195$ & $49920$ \\
-- $256$ & $1536$ & $192$ & $8$ & $6$ & $119$ & $\mathbb F_{p}$ & $167$ & $32064$ \\
-- $256$ & $1536$ & $96$ & $16$ & $6$ & $59$ & $\mathbb F_{p}$ & $155$ & $14880$ \\
-- --- Table x^(-1) WITH security margin ---
-- $128$ & $1536$ & $768$ & $2$ & $8$ & $65$ & $\mathbb F_{p}$ & $81$ & $62208$ \\
-- $128$ & $1536$ & $384$ & $4$ & $8$ & $60$ & $\mathbb F_{p}$ & $92$ & $35328$ \\
-- $128$ & $1536$ & $256$ & $6$ & $8$ & $57$ & $\mathbb F_{p}$ & $105$ & $26880$ \\
-- $128$ & $1536$ & $192$ & $8$ & $8$ & $54$ & $\mathbb F_{p}$ & $118$ & $22656$ \\
-- $128$ & $1536$ & $96$ & $16$ & $8$ & $32$ & $\mathbb F_{p}$ & $160$ & $15360$ \\
-- $256$ & $1536$ & $768$ & $2$ & $8$ & $134$ & $\mathbb F_{p}$ & $150$ & $115200$ \\
-- $256$ & $1536$ & $384$ & $4$ & $8$ & $128$ & $\mathbb F_{p}$ & $160$ & $61440$ \\
-- $256$ & $1536$ & $256$ & $6$ & $8$ & $126$ & $\mathbb F_{p}$ & $174$ & $44544$ \\
-- $256$ & $1536$ & $192$ & $8$ & $8$ & $89$ & $\mathbb F_{p}$ & $153$ & $29376$ \\
-- $256$ & $1536$ & $96$ & $16$ & $8$ & $32$ & $\mathbb F_{p}$ & $160$ & $15360$ \\
-- --- Table x^(-1) WITHOUT security margin ---
-- $128$ & $1536$ & $768$ & $2$ & $6$ & $60$ & $\mathbb F_{p}$ & $72$ & $55296$ \\
-- $128$ & $1536$ & $384$ & $4$ & $6$ & $55$ & $\mathbb F_{p}$ & $79$ & $30336$ \\
-- $128$ & $1536$ & $256$ & $6$ & $6$ & $53$ & $\mathbb F_{p}$ & $89$ & $22784$ \\
-- $128$ & $1536$ & $192$ & $8$ & $6$ & $50$ & $\mathbb F_{p}$ & $98$ & $18816$ \\
-- $128$ & $1536$ & $96$ & $16$ & $6$ & $29$ & $\mathbb F_{p}$ & $125$ & $12000$ \\
-- $256$ & $1536$ & $768$ & $2$ & $6$ & $124$ & $\mathbb F_{p}$ & $136$ & $104448$ \\
-- $256$ & $1536$ & $384$ & $4$ & $6$ & $119$ & $\mathbb F_{p}$ & $143$ & $54912$ \\
-- $256$ & $1536$ & $256$ & $6$ & $6$ & $117$ & $\mathbb F_{p}$ & $153$ & $39168$ \\
-- $256$ & $1536$ & $192$ & $8$ & $6$ & $82$ & $\mathbb F_{p}$ & $130$ & $24960$ \\
-- $256$ & $1536$ & $96$ & $16$ & $6$ & $29$ & $\mathbb F_{p}$ & $125$ & $12000$ \\