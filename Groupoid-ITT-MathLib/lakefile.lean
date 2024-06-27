import Lake
open Lake DSL

package «Groupoid-ITT-MathLib» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «AWFS» {
  -- add any library configuration options here
}

lean_lib «Groupoids» {
  -- add any library configuration options here
}

lean_lib «Other» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «GroupoidITTMathLib» where
  -- add any library configuration options here
