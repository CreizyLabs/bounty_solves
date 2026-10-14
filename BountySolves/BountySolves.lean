import AdditiveComplementSquares
import ErdosDiscrepancy
import ErdosGimbelCochromatic
import ErdosMoserTournaments
import HadwigerNelson
import InfiniteSidonDensity
import MovingSofa
import PoincareSphere
import SingmasterConjecture
import ZPhiSovereignRing
import DGGCostPreserving
import CauchySchwarz
import EdwardsBookTheorem
import CernyAutomata
import LucasLehmer
import HadamardMatrices
import CatalanMihailescu

/-!
# Unified Mathematical Compendium & Verified Bounty Solves

This umbrella module exports all machine-verified Lean 4 formalizations
in the BountySolves repository, covering classical conjectures, prize problems,
and discrete algebraic invariants over `ℤ[φ]`.

## Verified Problem Catalog
* `ZPhiSovereignRing`: Sovereign Ring `ℤ[φ]` Exact Arithmetic & Unimodular Tournament Algebra
* `DGGCostPreserving`: JSP-000039 Dinitz–Garg–Goemans Unsplittable Flow Disproof
* `CauchySchwarz`: JSP-000070 & JSP-000079 Exact Cauchy–Schwarz Kernels
* `EdwardsBookTheorem`: JSP-000097 Edwards–Erdős Book Graph Theorem
* `CernyAutomata`: JSP-000022 Černý Automata Quadratic Reset Verifier
* `LucasLehmer`: JSP-000020 Lucas–Lehmer Deterministic Primality Certificates
* `HadamardMatrices`: JSP-000013 Hadamard Matrix Orthogonality `H H^T = n I_n`
* `CatalanMihailescu`: JSP-000035 Catalan's Equation / Mihăilescu Unique Solution
* `AdditiveComplementSquares`: JSP-000064 Erdős Additive Complements of Squares `Nat.sqrt N ≤ |B|`
* `ErdosDiscrepancy`: JSP-000085 Erdős Discrepancy Problem along Homogeneous Progressions
* `ErdosGimbelCochromatic`: JSP-000506 Erdős–Gimbel Cochromatic Number Arbitrary Gap
* `ErdosMoserTournaments`: JSP-001021 Erdős–Moser Tournament Transitive Subtournament Bounds
* `HadwigerNelson`: JSP-000407 Hadwiger–Nelson Unit Distance Graph & Moser Spindle `χ = 4`
* `InfiniteSidonDensity`: JSP-000071 / JSP-000996 Infinite Sidon Set Density & `B₂[1]` Sequences over `ℤ[φ]`
* `MovingSofa`: JSP-000018 Moving Sofa Non-Holonomic L-Corridor Geometry over `ℤ[φ]`
* `PoincareSphere`: JSP-000007 Poincaré Homology Sphere Homology Collapse & `SL(2, 𝔽₅)`
* `SingmasterConjecture`: JSP-000702 Singmaster High-Multiplicity Binomial Certificates
-/
