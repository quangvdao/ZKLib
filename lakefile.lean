import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DAutoImplicit=false"
]


package «piops» {
  -- add any package configuration options here
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.0"


@[default_target]
lean_lib «Piops» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «Jolt» {
  -- add any library configuration options here
}
