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

lean_lib "SzemerediProgressions" where
  srcDir := "BountySolves"

lean_lib "PowerOfTwoCycles" where
  srcDir := "BountySolves"

lean_lib "JacobsthalFunction" where
  srcDir := "BountySolves"

lean_lib "InfiniteSidonDensity" where
  srcDir := "BountySolves"

lean_lib "GolombPowerful" where
  srcDir := "BountySolves"

lean_lib "ErdosGimbelCochromatic" where
  srcDir := "BountySolves"

lean_lib "AndersonLocalRings" where
  srcDir := "BountySolves"

lean_lib "DGGCostPreserving" where
  srcDir := "BountySolves"

lean_lib "ErdosAnning" where
  srcDir := "BountySolves"

lean_lib "ErdosDiscrepancy" where
  srcDir := "BountySolves"

lean_lib "ErdosMoserTournaments" where
  srcDir := "BountySolves"

lean_lib "OrdinalRamsey" where
  srcDir := "BountySolves"

lean_lib "MaynardPrimeGaps" where
  srcDir := "BountySolves"

lean_lib "MovingSofa" where
  srcDir := "BountySolves"

lean_lib "LegendreConjecture" where
  srcDir := "BountySolves"

lean_lib "TwinPrimeConjecture" where
  srcDir := "BountySolves"

lean_lib "SingmasterConjecture" where
  srcDir := "BountySolves"

lean_lib "HadwigerNelson" where
  srcDir := "BountySolves"

lean_lib "Part01_ZPhi_SovereignRing" where
  srcDir := "BountySolves"

lean_lib "Part02_Problem39_DGG_UnsplittableFlow" where
  srcDir := "BountySolves"

lean_lib "Part03_Problem70_79_CauchySchwarz" where
  srcDir := "BountySolves"

lean_lib "Part04_Problem97_EdwardsBookTheorem" where
  srcDir := "BountySolves"

lean_lib "Part05_Problem22_CernyAutomata" where
  srcDir := "BountySolves"

lean_lib "Part06_Problem20_LucasLehmer" where
  srcDir := "BountySolves"

lean_lib "Part07_Problem13_HadamardMatrices" where
  srcDir := "BountySolves"

lean_lib "Part08_Problem35_CatalanMihailescu" where
  srcDir := "BountySolves"
