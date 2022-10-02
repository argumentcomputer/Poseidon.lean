def ZMod (_ : Nat) : Type := Int

namespace ZMod

def ofInt (a : Int) : ZMod n := a

def rep (a : ZMod n) : Int := a

instance : Add (ZMod n) where
  add (a b : ZMod n) := (rep a + rep b) % (n : Int)

instance : Mul (ZMod n) where
  mul (a b : ZMod n) := (rep a * rep b) % (n : Int)

instance {n m : Nat} : OfNat (ZMod n) m where
  ofNat := (m : Int)

private def power (a : ZMod n) : Nat → ZMod n
  | 0       => 1
  | .succ n => a * power a n

instance : HPow (ZMod n) Nat (ZMod n) where
  hPow := power

instance : Inhabited (ZMod n) where
  default := 0

private def norm (a : ZMod n) : Nat :=
  let diff := rep a / n
  if rep a < 0 then rep a + diff * (n : Int) |>.toNat else
  if rep a > n then rep a - diff * (n : Int) |>.toNat else
  rep a |>.toNat

-- TODO : Too lazy to show this terminates, use `t < newt`
private partial def inv' (a : ZMod n) : Int := 
  let rec loop (t r newt newr : Int) :=
    dbg_trace s!"r:{r} t:{t} newr:{newr} newt:{newt} "
    if newr != 0 then 
      let quot := r / newr
      dbg_trace s!"quot:{quot}"
      loop newt newr (t - quot * newt) (r - quot * newr) else
    if r > 1 then 0 else if t < 0 then t + n else t 
  loop 0 n 1 (norm a)

def inv (a : ZMod n) : ZMod n := ofInt $ inv' a

instance : Div (ZMod n) where
  div a b := a * inv b

instance : Repr (ZMod n) where
  reprPrec a _ := s!"{norm a}"

end ZMod
