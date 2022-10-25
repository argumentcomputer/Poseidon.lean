# Lean 4 Poseidon implementation

This repository contains an implementation of the Poseidon hash function in Lean 4.

## Usage

The main function of this implementation is `Poseidon.hash` found in `Poseidon.HashImpl`. The function has signature:

```lean
def hash (prof : HashProfile) 
         (context : Hash.Context prof)
         (preimage : Array (Zmod prof.p)) 
         (domain : Domain) : Zmod prof.p
```

The parameters to the function can be briefly described as follows:

* `HashProfile` : Contains the parameters prime `p`, width `t`, security parameters `M`, and S-box exponent `a`
* `Hash.Context` : Contains the necessary parameters to compute the Poseidon hash, in particular
  the MDS matrix and the array of round constants.
* `Array (Zmod profile.p)` : The message to hash. If the length of the array does not match the specified arity
  a dummy value of `0` is returned
* `Domain` : The domain in which to hash the function. Right now it is either a fixed-arity Merkle tree hash
  or fixed length input. 

The output is the result of the hash (the second component of the final vector, consistent with the 
Filecoin specification.)

Pre-computed profiles and contexts are available in the `Poseidon.Parameters` folder.

For Lurk specific hashing purposes, the `Poseidon.ForLurk` module contains 
```lean
abbrev F' := Zmod Lurk.Profile.p

def Lurk.hash : F' → F' → F' → F' → F'
```
which computes the arity 4 hashes found in the [lurk-rs](https://github.com/lurk-lang/lurk-rs/). 

### Generating new profiles

Also included in the repository are round number, and round constant generators to generate profiles
and contexts from an input set of parameters. The generated constants and MDS matrices are consistent
with the [Filecoin specification](https://spec.filecoin.io/algorithms/crypto/poseidon/).

## Comparison with other implementations

The aim of this Lean 4 implementation is to maintain consistency with the other major implementations
of the Poseidon hashing protocol. In particular

* [Reference implementation](https://github.com/filecoin-project/neptune)
* [Filecoin rust implementation](https://github.com/filecoin-project/neptune)
* [Python implementation](https://github.com/ingonyama-zk/poseidon-hash)

This is achieved through the test suite described below, and writing the core algorithm agnostic to
implementation details.

## Tests

This repository contains a robust suite of tests that checks that the hashing, round constant
generation, and round number generation match those found in the other implementations.

The test suite contains and expands on the tests in the reference, Python, and Filecoin/rust 
implementations. See the corresponding test in the `Tests` folder to find more about what is being
tested and how the tests were generated.

Included in the test suite are tests that check the parameters contained in the pre-computed profiles
match those that would be computed according to the relevant specification in which they are defined.
