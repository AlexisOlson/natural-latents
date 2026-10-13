import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"a1cf70667112dcffe15faea9f8783e63dd9644e8"
require natural_latents from ".."
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"106ff4fafc74ef4ac99d81dbf3ab399118f497a5"
require plausible from git "https://github.com/leanprover-community/plausible"@"118aa17ee84656b8bd727fef7c458ee8c833385c"

package NaturalLatentsBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib NaturalLatentsBlueprint where
  roots := #[`NaturalLatentsBlueprint]
  globs := #[.one `NaturalLatentsBlueprint, .one `Blueprint,
    .submodules `Chapters]
