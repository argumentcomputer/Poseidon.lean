import Poseidon.Hash

namespace Poseidon

/--
These are the two domains specified in the Filecoin/Lurk implementation of Poseidon, and do not
constitute of all the possible domains
-/
inductive Domain
  | merkleTree   -- Hashing fixed `arity : Nat` merkle tree` 
  | fixedLength  -- Hashing fixed length inputs

def getInput (prof : HashProfile) 
             (preimage : Array (Zmod prof.p)) 
             (domain : Domain) : Option $ Array $ Zmod prof.p := 
  match domain with
    | .merkleTree => 
      if preimage.size != prof.t - 1 then none else
        let domainTag : Zmod prof.p := .ofNat $ 2^(preimage.size) -1 -- For Lurk: 2^4 - 1
        some $ #[domainTag] ++ preimage
    | .fixedLength  => 
      if preimage.size > prof.t - 1 then none else
        let domainTag : Zmod prof.p := .ofNat $ 2^64 * preimage.size
        let padding : Array $ Zmod prof.p := .mkArray (prof.t - 1 - preimage.size) 0
        some $ #[domainTag] ++ preimage ++ padding

def hash (prof : HashProfile) 
         (context : Hash.Context prof)
         (preimage : Array (Zmod prof.p)) 
         (domain : Domain) : Zmod prof.p := 
  let input? := getInput prof preimage domain
  match input? with
    | none       => 0
    | some input => hashInput prof context input |>.get! 1