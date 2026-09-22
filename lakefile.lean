import Lake
open Lake DSL

package "bounty_solves" where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib "GuysD19" where
  srcDir := "BountySolves"

lean_lib "ZPhiRing" where
  srcDir := "BountySolves"

lean_lib "VacuumDecoupling" where
  srcDir := "BountySolves"

lean_lib "ErdosDistinctSubsetSums" where
  srcDir := "BountySolves"
