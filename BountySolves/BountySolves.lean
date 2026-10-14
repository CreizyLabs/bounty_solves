/-
Copyright (c) 2026 Compendium Formal Verification Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Unified Mathematical Compendium & Verified Bounty Solves

This umbrella module exports all 17 machine-verified Lean 4 formalizations
in the BountySolves repository, covering classical conjectures, prize problems,
and discrete algebraic invariants over `ℤ[φ]`.

## Verified Problem Catalog
* `Part01_ZPhi_SovereignRing`: Sovereign Ring `ℤ[φ]` Exact Arithmetic & Unimodular Tournament Algebra
* `Part02_Problem39_DGG_UnsplittableFlow`: JSP-000039 Dinitz–Garg–Goemans Unsplittable Flow Disproof
* `Part03_Problem70_79_CauchySchwarz`: JSP-000070 & JSP-000079 Exact Cauchy–Schwarz Kernels
* `Part04_Problem97_EdwardsBookTheorem`: JSP-000097 Edwards–Erdős Book Graph Theorem
* `Part05_Problem22_CernyAutomata`: JSP-000022 Černý Automata Quadratic Reset Verifier
* `Part06_Problem20_LucasLehmer`: JSP-000020 Lucas–Lehmer Deterministic Primality Certificates
* `Part07_Problem13_HadamardMatrices`: JSP-000013 Hadamard Matrix Orthogonality `H H^T = n I_n`
* `Part08_Problem35_CatalanMihailescu`: JSP-000035 Catalan's Equation / Mihăilescu Unique Solution
* `AdditiveComplementSquares`: JSP-000064 Erdős Additive Complements of Squares `Nat.sqrt N ≤ |B|`
* `ErdosDiscrepancy`: JSP-000085 Erdős Discrepancy Problem along Homogeneous Progressions
* `ErdosGimbelCochromatic`: JSP-000506 Erdős–Gimbel Cochromatic Number Arbitrary Gap
* `ErdosMoserTournaments`: JSP-001021 Erdős–Moser Tournament Transitive Subtournament Bounds
* `HadwigerNelson`: JSP-000407 Hadwiger–Nelson Unit Distance Graph & Moser Spindle `χ = 4`
* `InfiniteSidonDensity`: JSP-000071 Infinite Sidon Set Density & `B₂[1]` Sequences over `ℤ[φ]`
* `MovingSofa`: JSP-000018 Moving Sofa Non-Holonomic L-Corridor Geometry over `ℤ[φ]`
* `PoincareSphere`: JSP-000007 Poincaré Homology Sphere Homology Collapse & `SL(2, 𝔽₅)`
* `SingmasterConjecture`: JSP-000702 Singmaster High-Multiplicity Binomial Certificates
-/

import AdditiveComplementSquares
import ErdosDiscrepancy
import ErdosGimbelCochromatic
import ErdosMoserTournaments
import HadwigerNelson
import InfiniteSidonDensity
import MovingSofa
import Part01_ZPhi_SovereignRing
import Part02_Problem39_DGG_UnsplittableFlow
import Part03_Problem70_79_CauchySchwarz
import Part04_Problem97_EdwardsBookTheorem
import Part05_Problem22_CernyAutomata
import Part06_Problem20_LucasLehmer
import Part07_Problem13_HadamardMatrices
import Part08_Problem35_CatalanMihailescu
import PoincareSphere
import SingmasterConjecture
