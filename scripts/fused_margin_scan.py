#!/usr/bin/env python3
from __future__ import annotations
"""Conditional fused-centre arithmetic scan (no circuit claim).

For h >= 3 this evaluates the exact formulas used by the H16/H17/H18 audit:
  v = C(h,3), d = C(h-3,3) + 3(h-3), N=v^3, I=3v^2,
  W = 2N + I(v*d + h + 1), P=nextpow2(W),
  S = 2N - 4v^2 h^2, Q=Ih.
The one-shear and six-phase ledgers are (S-Q)/(h^3 P) and
(S-6Q)/(h^3 P), respectively. All arithmetic is exact.
"""
from fractions import Fraction
from math import comb

ONE_E9 = Fraction(1, 10**9)

def next_pow2(n: int) -> int:
    return 1 << (n - 1).bit_length()

def row(h: int) -> dict[str, int | Fraction]:
    v = comb(h, 3)
    d = comb(h - 3, 3) + 3 * (h - 3)
    n0 = v**3
    i0 = 3 * v**2
    role = 2*n0 + i0 * (v*d + h + 1)
    pad = next_pow2(role)
    saving = 2*n0 - 4*v**2*h**2
    shear = i0*h
    m1 = saving - shear
    m6 = saving - 6*shear
    den = h**3 * pad
    return {
        "h": h, "v": v, "d": d, "N0": n0, "I0": i0,
        "role": role, "padding": pad, "saving": saving, "shear": shear,
        "margin1": m1, "norm1": Fraction(m1, den),
        "margin6": m6, "norm6": Fraction(m6, den),
    }

def main() -> None:
    for h in range(16, 25):
        r = row(h)
        print("h={h} v={v} d={d} role={role} pad={padding} "
              "save={saving} shear={shear} M1={margin1} norm1={norm1} "
              "M6={margin6} norm6={norm6}".format(**r))
    one = [h for h in range(3, 1001) if row(h)["norm1"] > ONE_E9]
    six = [h for h in range(3, 1001) if row(h)["norm6"] > ONE_E9]
    assert one == list(range(16, 38)), one
    assert six == list(range(18, 38)), six
    best1 = max((row(h)["norm1"], h) for h in range(3, 1001))
    best6 = max((row(h)["norm6"], h) for h in range(3, 1001))
    print(f"one-shear >1e-9 on h={one[0]}..{one[-1]}; best={best1}")
    print(f"six-phase >1e-9 on h={six[0]}..{six[-1]}; best={best6}")

if __name__ == "__main__":
    main()
