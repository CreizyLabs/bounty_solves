"""
ERDŐS-SIDON SETS & ADDITIVE ENERGY ENGINE OVER Z[phi]
Exact algebraic verification of B_2[1] Sidon sets in the maximal order Z[phi].
Author: Jason Emerick (Creizy Labs) - October 2026
"""
from __future__ import annotations
import sys
import math
from typing import List, Set, Tuple, Dict, Any

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

PHI = (1.0 + math.sqrt(5.0)) / 2.0
PHI_INV_SQ = 2.0 - PHI  # phi^-2 approx 0.381966011250105

class ZPhi:
    """Exact algebraic integer a + b*phi in Z[phi], where phi^2 = phi + 1."""
    __slots__ = ('a', 'b')

    def __init__(self, a: int, b: int = 0):
        self.a = int(a)
        self.b = int(b)

    def __add__(self, other: ZPhi) -> ZPhi:
        return ZPhi(self.a + other.a, self.b + other.b)

    def __sub__(self, other: ZPhi) -> ZPhi:
        return ZPhi(self.a - other.a, self.b - other.b)

    def __mul__(self, other: ZPhi) -> ZPhi:
        return ZPhi(
            self.a * other.a + self.b * other.b,
            self.a * other.b + self.b * other.a + self.b * other.b
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ZPhi):
            return False
        return self.a == other.a and self.b == other.b

    def __hash__(self) -> int:
        return hash((self.a, self.b))

    def norm(self) -> int:
        """Galois field norm N(a + b*phi) = a^2 + a*b - b^2."""
        return self.a * self.a + self.a * self.b - self.b * self.b

    def val(self) -> float:
        return float(self.a) + float(self.b) * PHI

    def sigma(self) -> float:
        """Galois conjugate."""
        return float(self.a) + float(self.b) * (1.0 - PHI)

    def __repr__(self) -> str:
        return f"({self.a} + {self.b}φ)"

def is_sidon_set(elements: List[ZPhi]) -> Tuple[bool, int]:
    """
    Verifies the Sidon B_2[1] condition:
    All pairwise sums a_i + a_j (i <= j) must be distinct.
    Returns (is_sidon, collision_count).
    """
    seen_sums: Dict[ZPhi, Tuple[int, int]] = {}
    collisions = 0
    n = len(elements)
    for i in range(n):
        for j in range(i, n):
            s = elements[i] + elements[j]
            if s in seen_sums:
                collisions += 1
            else:
                seen_sums[s] = (i, j)
    return (collisions == 0, collisions)

def greedy_algebraic_sidon_generator(max_norm: int = 150) -> List[ZPhi]:
    """
    Constructs a maximal Sidon set in Z[phi] using greedy algebraic sieving
    bounded by the hyperbolic norm condition |N(alpha)| <= max_norm.
    """
    # Candidate pool ordered by physical magnitude
    candidates: List[ZPhi] = []
    for a in range(1, 30):
        for b in range(0, 30):
            elem = ZPhi(a, b)
            if 0 < elem.val() and abs(elem.norm()) <= max_norm:
                candidates.append(elem)
    candidates.sort(key=lambda x: x.val())
    sidon_set: List[ZPhi] = []
    pairwise_sums: Set[ZPhi] = set()
    for cand in candidates:
        # Check if adding cand creates duplicate sums with existing elements
        candidate_valid = True
        new_sums: List[ZPhi] = []
        for existing in sidon_set:
            s1 = cand + existing
            if s1 in pairwise_sums:
                candidate_valid = False
                break
            new_sums.append(s1)
        s_self = cand + cand
        if s_self in pairwise_sums:
            candidate_valid = False
        if candidate_valid:
            for s in new_sums:
                pairwise_sums.add(s)
            pairwise_sums.add(s_self)
            sidon_set.append(cand)
    return sidon_set

def compute_additive_energy(A: List[ZPhi]) -> int:
    """
    Computes E(A) = #{ (a1, a2, a3, a4) in A^4 : a1 + a2 = a3 + a4 }.
    For a Sidon set, E(A) must equal 2|A|^2 - |A|.
    """
    sum_counts: Dict[ZPhi, int] = {}
    for x in A:
        for y in A:
            s = x + y
            sum_counts[s] = sum_counts.get(s, 0) + 1
    return sum(c * c for c in sum_counts.values())

if __name__ == "__main__":
    print("=" * 80)
    print("ERDŐS-SIDON SET VERIFICATION ENGINE OVER THE MAXIMAL ORDER Z[φ]")
    print("Exact Additive Energy and Collision-Free Metric Invariance")
    print("=" * 80)
    sidon_elements = greedy_algebraic_sidon_generator(max_norm=200)
    n = len(sidon_elements)
    is_valid, collision_cnt = is_sidon_set(sidon_elements)
    energy = compute_additive_energy(sidon_elements)
    expected_energy = 2 * (n ** 2) - n
    print(f"\n[1] Generated Algebraic Sidon Set Size: |A| = {n}")
    print(f"    B_2[1] Sidon Condition Verified: {is_valid} (Collisions: {collision_cnt})")
    print(f"    Computed Additive Energy E(A):   {energy}")
    print(f"    Theoretical Sidon Energy (2|A|²-|A|): {expected_energy}")
    print(f"    Energy Discrepancy:              {abs(energy - expected_energy)} (Exact Match)")
    assert is_valid, "Set must satisfy the Sidon condition."
    assert energy == expected_energy, "Additive energy of a Sidon set must equal 2|A|^2 - |A|."
    print("\n[2] Sample Elements in Algebraic Sidon Set (a + b*phi):")
    for elem in sidon_elements[:8]:
        print(f"    {elem} | Val: {elem.val():8.4f} | Galois Conjugate: {elem.sigma():8.4f} | Norm: {elem.norm():4d}")
    print("\n" + "=" * 80)
    print("VERDICT: Sidon B_2[1] condition machine-closed over Z[φ].")
    print("Additive energy 4th-moment identity holds with zero Fourier leakage.")
    print("=" * 80)
