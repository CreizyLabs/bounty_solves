import Lake
open Lake DSL

package "bounty_solves" where
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeanArgs := #["-M", "4096", "-j", "2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib "BountySolves" where
  srcDir := "BountySolves"

lean_lib "StablyCompleteGoldenRatio" where
  srcDir := "BountySolves"

lean_lib "ErdosSimonovitsCompactness" where
  srcDir := "BountySolves"

lean_lib "ErdosGalvinSubsetSums" where
  srcDir := "BountySolves"

lean_lib "SunflowerLemma" where
  srcDir := "BountySolves"

lean_lib "ErdosSidonSets" where
  srcDir := "BountySolves"

lean_lib "LowerBoundMaxElement" where
  srcDir := "BountySolves"

lean_lib "OddCoveringSystems" where
  srcDir := "BountySolves"

lean_lib "AdditiveComplementSquares" where
  srcDir := "BountySolves"

lean_lib "GuysD19" where
  srcDir := "BountySolves"

lean_lib "CatalanMihailescu" where
  srcDir := "BountySolves"

lean_lib "PoincareSphere" where
  srcDir := "BountySolves"
