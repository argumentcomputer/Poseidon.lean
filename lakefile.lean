import Lake
open Lake DSL

package Poseidon

@[default_target]
lean_lib Poseidon where
  precompileModules := true

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "92e5f1d578e307668a00036845ddebc7685134a2"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

lean_exe Tests.RoundNumbers
lean_exe Tests.RoundConstants
lean_exe Tests.Hash

-- def ffiC := "ffi.c"
-- def ffiO := "ffi.o"

-- target importTarget (pkg : Package) : FilePath := do
--   let oFile := pkg.oleanDir / ffiO
--   let srcJob ← inputFile $ pkg.dir / ffiC
--   buildFileAfterDep oFile srcJob fun srcFile => do
--     let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
--     compileO ffiC oFile srcFile flags

-- extern_lib ffi (pkg : Package) := do
--   let name := nameToStaticLib "ffi"
--   let job ← fetch <| pkg.target ``importTarget
--   buildStaticLib (pkg.libDir / name) #[job]

-- extern_lib rust_ffi (pkg : Package) := do
--   proc { cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir }
--   let name := nameToStaticLib "rust_ffi"
--   let srcPath := pkg.dir / "target" / "release" / name
--   IO.FS.createDirAll pkg.libDir
--   let tgtPath := pkg.libDir / name
--   IO.FS.writeBinFile tgtPath (← IO.FS.readBinFile srcPath)
--   return (pure tgtPath)
