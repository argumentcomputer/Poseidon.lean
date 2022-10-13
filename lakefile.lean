import Lake
open Lake DSL

package Poseidon 

@[defaultTarget]
lean_lib Poseidon

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "02ec0ac2415f2fffcb25638553c69113d28cd47c"

require LSpec from git
   "https://github.com/yatima-inc/LSpec" @ "9c9f3cc9f3148c1b2d6071a35e54e4c5392373b7"
