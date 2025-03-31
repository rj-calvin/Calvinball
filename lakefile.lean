import Lake
open System Lake DSL

package calvinball where version := v!"0.1.0"

lean_lib Calvinball

require "leanprover-community" / "mathlib" @ git "stable"
require "madvorak" / "duality" @ git "v3.0.0"

@[default_target]
lean_exe calvinball where root := `Main
