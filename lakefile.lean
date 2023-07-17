import Lake
open Lake DSL

require Mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

package lazycore {
  -- add package configuration options here
}

--@[defaultTarget]
lean_lib Lazycore {
  roots := #[`Lazycore]
}
