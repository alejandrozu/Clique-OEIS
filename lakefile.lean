import Lake
open Lake DSL

package cliqueOEIS where
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

@[default_target]
lean_lib CliqueOEIS where
  roots := #[`DominanceThreshold, `CCImageSequences, `CCRecovery, `CCUnusedRecovery]
