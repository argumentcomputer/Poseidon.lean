import Lake
open Lake DSL

package Poseidon 

@[default_target]
lean_lib Poseidon

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "818538aced05fe563ef95bb3dcdf5ed755896139"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "129fd4ba76d5cb9abf271dc29208a28f45fd981e"

-- Tests
lean_exe Tests.RoundNumbers
lean_exe Tests.RoundConstants
lean_exe Tests.Hash