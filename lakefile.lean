import Lake
open Lake DSL

package "bounty_solves" where
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeanArgs := #["-M", "4096", "-j", "2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib "JSP_000078_GyarfasOddCycleLengths" where
  srcDir := "bountysolves"

@[default_target]
lean_lib "JSP_000183_SmallStepZ3WalkNoCollinear" where
  srcDir := "bountysolves"

@[default_target]
lean_lib "JSP_000288_StablyCompleteGoldenRatio" where
  srcDir := "bountysolves"

@[default_target]
lean_lib "JSP_000301_GolombPowerful" where
  srcDir := "bountysolves"

@[default_target]
lean_lib "JSP_000490_Erdos603_ForbiddenIntersectionTwo" where
  srcDir := "bountysolves"

@[default_target]
lean_lib "JSP_000690_ErdosLovasz_3CriticalHypergraph" where
  srcDir := "bountysolves"

@[default_target]
lean_lib "JSP_000698_FleischnerStiebitz_CyclePlusTriangles" where
  srcDir := "bountysolves"

@[default_target]
lean_lib "JSP_000746_TriangleFreeSchurTriple" where
  srcDir := "bountysolves"
