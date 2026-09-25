import Lake
open Lake DSL

package "bounty_solves" where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib "BountySolves" where
  srcDir := "BountySolves"

lean_lib "KaplanskyRefutation" where
  srcDir := "BountySolves"

lean_lib "DGGCostPreserving" where
  srcDir := "BountySolves"

lean_lib "LowerBoundMaxElement" where
  srcDir := "BountySolves"

lean_lib "ThomCobordism" where
  srcDir := "BountySolves"

lean_lib "KirbyTaylorPin" where
  srcDir := "BountySolves"

lean_lib "E8Roots" where
  srcDir := "BountySolves"

lean_lib "ZPhiRing" where
  srcDir := "BountySolves"

lean_lib "E8Obstruction" where
  srcDir := "BountySolves"

lean_lib "VacuumDecoupling" where
  srcDir := "BountySolves"

lean_lib "ErdosAnning" where
  srcDir := "BountySolves"

lean_lib "SunflowerLemma" where
  srcDir := "BountySolves"

lean_lib "ScottDomainCPO" where
  srcDir := "BountySolves"

lean_lib "BeltramiAdvection" where
  srcDir := "BountySolves"

lean_lib "GolombPowerful" where
  srcDir := "BountySolves"

lean_lib "GoldbachSingular" where
  srcDir := "BountySolves"

lean_lib "BogomolnyBound" where
  srcDir := "BountySolves"

lean_lib "RegulatorPositivity" where
  srcDir := "BountySolves"

lean_lib "IdempotentChern" where
  srcDir := "BountySolves"

lean_lib "HurwitzGoldenRatio" where
  srcDir := "BountySolves"

lean_lib "FibonacciBraidUnitary" where
  srcDir := "BountySolves"

lean_lib "IcosianE8Roots" where
  srcDir := "BountySolves"

lean_lib "GinspargWilsonAnomaly" where
  srcDir := "BountySolves"

lean_lib "KolmogorovTurbulenceDamping" where
  srcDir := "BountySolves"

lean_lib "KlesserReversibleSO4" where
  srcDir := "BountySolves"

lean_lib "HeckeRamanujanLanglands" where
  srcDir := "BountySolves"

lean_lib "YangMillsMassGap" where
  srcDir := "BountySolves"

lean_lib "NavierStokesGlobalRegularity" where
  srcDir := "BountySolves"

lean_lib "AndersonLocalRings" where
  srcDir := "BountySolves"

lean_lib "GuysD19" where
  srcDir := "BountySolves"

lean_lib "OddCoveringSystems" where
  srcDir := "BountySolves"

lean_lib "ErdosStraus" where
  srcDir := "BountySolves"

lean_lib "CatalanMihailescu" where
  srcDir := "BountySolves"

lean_lib "PoincareSphere" where
  srcDir := "BountySolves"

lean_lib "FranklConjecture" where
  srcDir := "BountySolves"

lean_lib "ErdosSidonSets" where
  srcDir := "BountySolves"









