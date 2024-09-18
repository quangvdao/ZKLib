import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DAutoImplicit=false"
]


package «Zklib» {
  -- add any package configuration options here
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]
}


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.0"

require VCVio from git
  "https://github.com/dtumad/VCV-io.git" @ "master"

@[default_target]
lean_lib «ZKLib» {
  -- add any library configuration options here
}

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"