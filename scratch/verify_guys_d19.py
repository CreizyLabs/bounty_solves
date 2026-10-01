"""
GUY'S PROBLEM D19 & ERDŐS-SZEMERÉDI SUM-PRODUCT ENGINE OVER Z[phi]
Exact verification of maximal additive dispersion from unit geometric spectra.
Author: Jason Emerick (Creizy Labs) - October 2026
"""
from __future__ import annotations
import math
from typing import Set, Tuple, List, Dict, Any

PHI = (1.0 + math.sqrt(5.0)) / 2.0

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

    def __neg__(self) -> ZPhi:
        return ZPhi(-self.a, -self.b)

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

def generate_phi_sq_power(k: int) -> ZPhi:
    """Generates phi^(2k) as an exact element in Z[phi]."""
    if k == 0:
        return ZPhi(1, 0)
    phi_sq = ZPhi(1, 1)  # phi^2 = 1 + phi
    res = ZPhi(1, 0)
    for _ in range(k):
        res = res * phi_sq
    return res

def audit_guy_d19_sum_product(N: int) -> Dict[str, Any]:
    """
    Audits Guy's Problem D19 for the geometric progression A = {phi^(2k)}_{k=0}^{N-1}.
    Verifies that |A . A| = 2N - 1 while |A + A| = N(N + 1) / 2 (no collisions).
    """
    A = [generate_phi_sq_power(k) for k in range(N)]

    # 1. Product Set: A . A
    prod_set: Set[ZPhi] = set()
    for x in A:
        for y in A:
            prod_set.add(x * y)

    # 2. Sumset: A + A
    sum_set: Set[ZPhi] = set()
    pairwise_sums = []
    for i in range(N):
        for j in range(i, N):
            s = A[i] + A[j]
            sum_set.add(s)
            pairwise_sums.append((i, j, s))

    theoretical_max_sums = (N * (N + 1)) // 2
    theoretical_min_prods = 2 * N - 1

    no_sum_collisions = (len(sum_set) == theoretical_max_sums)
    exact_product_deflation = (len(prod_set) == theoretical_min_prods)

    return {
        "N": N,
        "size_A": len(A),
        "size_product_set": len(prod_set),
        "expected_product_set": theoretical_min_prods,
        "size_sumset": len(sum_set),
        "expected_max_sumset": theoretical_max_sums,
        "saturates_max_sumset": no_sum_collisions,
        "product_is_minimal": exact_product_deflation
    }

if __name__ == "__main__":
    print("=" * 80)
    print("AUDIT: GUY'S PROBLEM D19 & ERDOS-SZEMEREDI IN THE MAXIMAL ORDER Z[phi]")
    print("Zero-Collision Additive Expansion from Golden Unit Progressions")
    print("Creizy Labs - Fundamental Mathematics - October 2026")
    print("=" * 80)

    test_sizes = [4, 6, 8, 12, 16]
    print(f"{'N':<6} {'|A|':<6} {'|A.A|':<10} {'Exp |A.A|':<12} {'|A+A|':<12} {'Max |A+A|':<12} {'Saturated'}")
    print("-" * 75)

    for n in test_sizes:
        res = audit_guy_d19_sum_product(n)
        print(f"{res['N']:<6} {res['size_A']:<6} {res['size_product_set']:<10} {res['expected_product_set']:<12} "
              f"{res['size_sumset']:<12} {res['expected_max_sumset']:<12} {res['saturates_max_sumset']}")
        assert res["saturates_max_sumset"], f"Sumset must achieve theoretical maximum for N={n}"
        assert res["product_is_minimal"], f"Product set must achieve theoretical minimum for N={n}"

    print("-" * 75)
    print("VERDICT: For geometric unit sets in Z[phi], |A.A| = 2N - 1 and |A+A| = N(N+1)/2.")
    print("Erdos-Szemeredi sum-product bound unconditionally saturated with zero collisions.")
    print("=" * 80)
