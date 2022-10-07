import Lake
open Lake DSL

package Poseidon 

@[defaultTarget]
lean_lib Poseidon

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "3cb5f4706cd49c1803cdb7a5aec53ca58e8a8b1a"

require LSpec from git
   "https://github.com/yatima-inc/LSpec" @ "9c9f3cc9f3148c1b2d6071a35e54e4c5392373b7"
