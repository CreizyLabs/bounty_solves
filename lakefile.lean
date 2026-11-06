import Lake
open Lake DSL

package "bounty_solves" where
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeanArgs := #["-M", "4096", "-j", "2"]

@[default_target]
lean_lib "LowerBoundMaxElement" where
  srcDir := "BountySolves"
