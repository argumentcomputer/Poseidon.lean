import Lake
open Lake DSL

package Poseidon

@[default_target]
lean_lib Poseidon where
  precompileModules := true

require YatimaStdLib from git
  "https://github.com/argumentcomputer/YatimaStdLib.lean" @ "v4.12.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "v4.12.0"

lean_exe Tests.RoundNumbers
lean_exe Tests.RoundConstants
lean_exe Tests.Hash

