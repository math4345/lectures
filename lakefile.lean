import Lake
open Lake DSL

package «lectures» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Lecture01» {
  -- add any library configuration options here
}

lean_lib «Lecture02» { }

