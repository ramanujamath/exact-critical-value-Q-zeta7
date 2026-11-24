#!/usr/bin/env python3
"""
Rigorous certificate for

    L_K(Psi, 2) = (49/8) (I_0 I_1 I_2)^2,   K = Q(zeta_7),

from "An exact critical value of a Hecke L-function over Q(zeta_7)"
by Ramanuja.

What this script proves (Section 6 of the manuscript).
  Given Proposition 4.2 (1792 q is an integer), the theorem follows from
  the inequality |1792 q - 32| < 1/100, where q = L(2) / (343 (I0 I1 I2)^2).
  This script proves that inequality by outward-rounded interval
  arithmetic. It also checks the finite algebraic identities used in
  Sections 2-5, by exact integer arithmetic in Z[zeta].

Design.
  * Standard library only (Python >= 3.8). No floating point is used in
    any step that the proof depends on.
  * Real numbers are enclosed in intervals [lo, hi] * 2^-PREC, where lo
    and hi are Python integers. Every operation rounds lo down and hi up.
  * Algebraic numbers are exact vectors in Z[zeta] (basis 1, ..., zeta^5).
  * Prime-ideal generators are found by a search. They are then *verified*
    exactly: an element of norm p^f, with f the residue degree of p,
    generates a prime of norm p^f. So how a generator was found does not
    matter for the proof.

Usage:   python3 certify.py          (runs in about a minute)
"""
from fractions import Fraction
from itertools import product
from math import isqrt, comb
import sys, time

PREC = 320                      # working precision in bits
ONE = 1 << PREC
NMAX = 10_000                   # Dirichlet coefficients used, as in the paper
T_TAIL = 12                     # exponent t in the tail bound (25)
MSER = 90                       # terms of the kernel series (24): m = 0..89

# ---------------------------------------------------------------------
#  Interval arithmetic on fixed-point integers
# ---------------------------------------------------------------------
def _fdiv(a, b):  # floor(a/b), b > 0
    return a // b
def _cdiv(a, b):  # ceil(a/b), b > 0
    return -((-a) // b)

class I:
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi=None):
        self.lo = lo; self.hi = lo if hi is None else hi
        assert self.lo <= self.hi
    @staticmethod
    def q(fr):                       # enclosure of a rational number
        fr = Fraction(fr)
        return I(_fdiv(fr.numerator * ONE, fr.denominator),
                 _cdiv(fr.numerator * ONE, fr.denominator))
    def __add__(s, o):
        o = o if isinstance(o, I) else I.q(o)
        return I(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__
    def __neg__(s):
        return I(-s.hi, -s.lo)
    def __sub__(s, o):
        return s + (-(o if isinstance(o, I) else I.q(o)))
    def __rsub__(s, o):
        return (-s) + o
    def __mul__(s, o):
        if not isinstance(o, I):
            o = Fraction(o)
            if o.denominator == 1:
                k = o.numerator
                return I(s.lo * k, s.hi * k) if k >= 0 else I(s.hi * k, s.lo * k)
            o = I.q(o)
        p = (s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi)
        return I(min(p) >> PREC, -((-max(p)) >> PREC))
    __rmul__ = __mul__
    def __truediv__(s, o):
        if not isinstance(o, I):
            o = Fraction(o)
            if o.denominator == 1 and o.numerator > 0:
                k = o.numerator
                return I(_fdiv(s.lo, k), _cdiv(s.hi, k))
            o = I.q(o)
        assert o.lo > 0, "division by an interval containing 0"
        c = [(a * ONE, b) for a in (s.lo, s.hi) for b in (o.lo, o.hi)]
        return I(min(_fdiv(a, b) for a, b in c), max(_cdiv(a, b) for a, b in c))
    def __rtruediv__(s, o):
        return I.q(o) / s
    def __pow__(s, k):
        r = I(ONE)
        for _ in range(k):
            r = r * s
        return r
    def widen(s, err):               # add [-err, err], err a Fraction >= 0
        e = _cdiv(Fraction(err).numerator * ONE, Fraction(err).denominator)
        return I(s.lo - e, s.hi + e)
    def contains_only_in(s, a, b):   # True if the whole interval lies in (a, b)
        return I.q(a).hi < s.lo and s.hi < I.q(b).lo
    def __repr__(s):
        return f"[{s.lo / ONE:.16g}, {s.hi / ONE:.16g}]"
    def frac(s):
        return Fraction(s.lo, ONE), Fraction(s.hi, ONE)

def iroot(n, k):                     # floor(n^(1/k)) for integers n >= 0
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x ** k > n:
        x -= 1
    while (x + 1) ** k <= n:
        x += 1
    return x

def root_of_rational(fr, k):         # enclosure of fr^(1/k), fr > 0 rational
    fr = Fraction(fr)
    # fr^(1/k) * 2^PREC = (fr * 2^(k PREC))^(1/k)
    num, den = fr.numerator * ONE ** k, fr.denominator
    lo = iroot(num // den, k)
    hi = iroot(_cdiv(num, den), k) + 1
    return I(lo, hi)

# ---- pi (Machin) ----------------------------------------------------
def arctan_inv(k, terms=None):
    """Enclosure of arctan(1/k) by the alternating series with remainder."""
    s = Fraction(0); i = 0
    while True:
        t = Fraction(1, (2 * i + 1) * k ** (2 * i + 1))
        if t < Fraction(1, 1 << (PREC + 20)):
            return I.q(s).widen(t)   # |remainder| <= first omitted term
        s += t if i % 2 == 0 else -t
        i += 1

PI = arctan_inv(5) * 16 - arctan_inv(239) * 4

# ---- logarithms -------------------------------------------------------
def _atanh_sum(t_fr):
    """log((1+t)/(1-t)) = 2 sum t^(2k+1)/(2k+1) for 0 <= t <= 1/3, rational t."""
    t = Fraction(t_fr); assert 0 <= t <= Fraction(1, 3)
    if t == 0:
        return I(0)
    s = I(0); tp = I.q(t); t2 = I.q(t * t); k = 0
    M = PREC // 3 + 10
    for k in range(M):
        s = s + tp / (2 * k + 1)
        tp = tp * t2
    rem = 2 * t ** (2 * M + 1) / ((2 * M + 1) * (1 - t * t))
    s = s * 2
    return I(s.lo, s.hi + _cdiv(rem.numerator * ONE, rem.denominator))

LOG2 = _atanh_sum(Fraction(1, 3))

def log_rational(y):
    """Enclosure of log(y) for a positive rational y."""
    y = Fraction(y); assert y > 0
    k = 0
    while y >= 2:
        y /= 2; k += 1
    while y < 1:
        y *= 2; k -= 1
    return LOG2 * k + _atanh_sum((y - 1) / (y + 1))

def log_interval(x):
    """Enclosure of log over a positive interval (log is increasing)."""
    lo, hi = x.frac(); assert lo > 0
    return I(log_rational(lo).lo, log_rational(hi).hi)

# ---- Euler's constant (Euler-Maclaurin) ------------------------------
def bernoulli(nmax):
    B = [Fraction(0)] * (nmax + 1); B[0] = Fraction(1)
    for m in range(1, nmax + 1):
        B[m] = -sum(comb(m + 1, k) * B[k] for k in range(m)) / (m + 1)
    return B

def euler_gamma(n=1024, m=24):
    B = bernoulli(2 * m + 2)
    rat = sum(Fraction(1, j) for j in range(1, n + 1)) - Fraction(1, 2 * n)
    rat += sum(B[2 * k] / (2 * k * Fraction(n) ** (2 * k)) for k in range(1, m + 1))
    R = abs(B[2 * m + 2]) / ((2 * m + 2) * Fraction(n) ** (2 * m + 2))
    return (I.q(rat) - log_rational(n)).widen(R)

GAMMA_E = euler_gamma()
ZETA2 = PI * PI / 6
SQRT2 = root_of_rational(2, 2)
SQRT7 = root_of_rational(7, 2)
Q = SQRT7 * 49 / (PI * PI * PI)          # Q = 7^(5/2) / pi^3

# ---------------------------------------------------------------------
#  Exact arithmetic in Z[zeta_7]
# ---------------------------------------------------------------------
def red(c):                      # coefficient list (any length) -> basis 1..z^5
    w = [0] * 7
    for i, x in enumerate(c):
        w[i % 7] += x
    return tuple(w[j] - w[6] for j in range(6))

def zmul(a, b):
    w = [0] * 7
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                w[(i + j) % 7] += x * y
    return tuple(w[j] - w[6] for j in range(6))

def zadd(a, b): return tuple(x + y for x, y in zip(a, b))
def zsub(a, b): return tuple(x - y for x, y in zip(a, b))
def zscal(k, a): return tuple(k * x for x in a)
def zpow_zeta(k): return red([0] * (k % 7) + [1])
ZONE = red([1]); ZZERO = (0,) * 6; ZETA = zpow_zeta(1)

def sigma(a, r):                 # sigma_r(zeta) = zeta^r
    w = [0] * 7
    for j, x in enumerate(a):
        w[(r * j) % 7] += x
    return tuple(w[j] - w[6] for j in range(6))

def zprod(lst):
    r = ZONE
    for x in lst:
        r = zmul(r, x)
    return r

def norm(a):                     # exact norm N_{K/Q}, an integer
    n = zprod(sigma(a, r) for r in range(1, 7))
    assert all(x == 0 for x in n[1:]), n
    return n[0]

def trace(a):                    # Tr(zeta^0) = 6, Tr(zeta^j) = -1 (j != 0)
    return 6 * a[0] - sum(a[1:])

S = (1, 4, 5); SIGMA = (2, 3, 6)
def P(a, T): return zprod(sigma(a, r) for r in T)

# ---- the finite character nu (residues in F_8 x F_8) ---------------
G1 = (1, 1, 0, 1)     # X^3 + X + 1
G2 = (1, 0, 1, 1)     # X^3 + X^2 + 1
def _mod2(c, g):
    c = [x % 2 for x in c]
    while len(c) >= len(g):
        if c[-1]:
            s = len(c) - len(g)
            for i, gi in enumerate(g):
                c[s + i] ^= gi
        c.pop()
    return tuple(c + [0] * (len(g) - 1 - len(c)))
def _dlog(g):
    return {_mod2([0] * A + [1], g): A for A in range(7)}
DL1, DL2 = _dlog(G1), _dlog(G2)

def nu(a):
    r1, r2 = _mod2(list(a), G1), _mod2(list(a), G2)
    if r1 not in DL1 or r2 not in DL2:
        return None              # not a unit modulo 2
    return zpow_zeta(4 * (DL1[r1] + DL2[r2]))

def Psi(a):                      # Psi((a)) = nu(a) P_S(a)^2, exact in Z[zeta]
    n = nu(a); assert n is not None
    ps = P(a, S)
    return zmul(n, zmul(ps, ps))

# ---------------------------------------------------------------------
#  Part A: exact algebraic checks (Sections 2-5)
# ---------------------------------------------------------------------
def check(cond, msg):
    print(("  ok   " if cond else "  FAIL ") + msg)
    if not cond:
        sys.exit(1)

def part_A():
    print("Part A: exact identities in Z[zeta_7]")
    z = ZETA; opz = zadd(ZONE, z)
    sq = lambda x: zmul(x, x)
    check(nu(z) == z and sq(P(z, S)) == zpow_zeta(6), "nu(zeta)=zeta, P_S(zeta)^2=zeta^6")
    check(nu(opz) == zpow_zeta(4) and sq(P(opz, S)) == zpow_zeta(3),
          "nu(1+zeta)=zeta^4, P_S(1+zeta)^2=zeta^3   (unit invariance, Sec. 2.1)")
    lam = zsub(ZONE, z)
    check(Psi(lam) == red([-7]), "Psi((1-zeta)) = -7   (eq. (5))")
    # Galois covariance of nu: nu(sigma_r a) = sigma_r nu(a), all 49 units mod 2
    units = [c for c in product((0, 1), repeat=6) if nu(c) is not None]
    check(len(units) == 49, "49 residue units modulo 2")
    ok = all(nu(sigma(c, r)) == sigma(nu(c), r) for c in units for r in range(1, 7))
    check(ok, "nu(sigma_r a) = sigma_r nu(a) on all residue units   (eq. (4))")
    # Finite Fourier inversion (19) on all 64 residues
    ok = True
    for a in product((0, 1), repeat=6):
        rhs = ZZERO
        for b in units:
            nb = nu(b); inv = sigma(nb, 6)            # nu(b)^{-1} = conj
            sign = -1 if trace(zmul(a, b)) % 2 else 1
            rhs = zadd(rhs, zscal(sign, inv))
        lhs = nu(a) if nu(a) is not None else ZZERO
        ok &= (zscal(8, lhs) == rhs)
    check(ok, "Fourier inversion (19): 8 nu(a) = sum_b nu(b)^-1 (-1)^Tr(ab), all 64 residues")
    # Period identity in (7)
    w = zprod([zsub(z, ZONE), zsub(zpow_zeta(2), ZONE), zsub(zpow_zeta(3), ZONE)])
    check(zmul(w, w) == zscal(-7, zpow_zeta(6)), "((z-1)(z^2-1)(z^3-1))^2 = -7 z^6   (eq. (7))")
    # Galois multipliers (Prop. 4.1)
    ok = True
    for r in range(1, 7):
        u = red([1] * r); v = sigma(u, 5)
        ok &= norm(u) == 1 and sq(P(u, S)) == zpow_zeta(3 * (r - 1))
        ok &= nu(u) == zpow_zeta(4 * (r - 1)) and nu(v) == zpow_zeta(1 - r)
        ok &= zmul(sigma(u, 6), zpow_zeta(r - 1)) == u          # u_r / conj(u_r) = zeta^(r-1)
        ok &= zmul(sq(P(v, SIGMA)), ZONE) == nu(v)
    check(ok, "Galois multipliers: P_S(u_r)^2, nu(u_r), nu(v_r), prod_Sigma sigma_a(v_r)^2 = nu(v_r)")
    # Smoothing ideals (Sec. 4.2)
    a29 = red([-1, -1, -1, -1, 1]); a43 = red([-1, -1, -1, -1, -1, 1])
    check(norm(a29) == 29 and norm(a43) == 43, "N(a29)=29, N(a43)=43")
    def A(a):
        # A_c = N c - chi(c)^{-1},  chi(c) = Psi(c) / N(c)^2.  Since N(a) = P_S(a) P_Sigma(a),
        # chi(c)^{-1} = P_Sigma(a)^2 / nu(a) = conj(nu(a)) P_Sigma(a)^2  (nu(a) a root of unity).
        n = norm(a)
        inv_nu = sigma(nu(a), 6)
        return zsub(red([n]), zmul(inv_nu, sq(P(a, SIGMA))))
    Astar = zsub(zscal(3, A(a29)), zscal(2, A(a43)))
    U = (26, 6, 27, 17, 21, 15)
    check(Astar == zscal(-4, U), "A* = 3A_c29 - 2A_c43 = -4U   (eq. (15))")
    check(_mod2(list(U), G1) != (0, 0, 0) and _mod2(list(U), G2) != (0, 0, 0),
          "U is a unit at both primes above 2")
    # lambda-adic expansion of U
    lamexp = [112, -270, 354, -251, 96, -15]
    acc = ZZERO; lp = ZONE
    for c in lamexp:
        acc = zadd(acc, zscal(c, lp)); lp = zmul(lp, lam)
    check(acc == U, "U = 112 - 270 l + 354 l^2 - 251 l^3 + 96 l^4 - 15 l^5, l = 1 - zeta")
    # Tensor coefficients at seven (Sec. 4.4): e0=T^5 w1, e1=T^3(w2-w1), e2=T(w3-2w2+w1)
    E = {0: (5, (1, 0, 0)), 1: (3, (-1, 1, 0)), 2: (1, (1, -2, 1))}
    det = 1  # det of the coefficient matrix (lower triangular, unit diagonal)
    from itertools import permutations, combinations_with_replacement
    table = {}
    for idx in combinations_with_replacement(range(3), 3):
        perms = set(permutations(idx))
        coef = 0
        for pm in perms:   # orbit sum: each distinct ordering once
            # coefficient of w1 (x) w2 (x) w3 in e_pm0 (x) e_pm1 (x) e_pm2
            coef += E[pm[0]][1][0] * E[pm[1]][1][1] * E[pm[2]][1][2]
        tpow = sum(E[i][0] for i in idx) + 9   # + det factor T^(5+3+1)
        if coef:
            table[idx] = (coef * det, tpow)
    expect = {(0, 1, 2): (1, 18), (0, 2, 2): (-2, 16), (1, 1, 2): (-1, 16),
              (1, 2, 2): (3, 14), (2, 2, 2): (-2, 12)}
    check(table == expect, "ten tensor coefficients at seven (table in Sec. 4.4)")
    print()

# ---------------------------------------------------------------------
#  Part B: exact Dirichlet coefficients a_n, n <= NMAX
# ---------------------------------------------------------------------
def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0:2] = b"\x00\x00"
    for i in range(2, isqrt(N) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]

def find_generator(p, f):
    """Search for an element of norm p^f (verified exactly by the caller)."""
    if f == 3:   # generator from Z[(1+sqrt(-7))/2], w = -(z^3+z^5+z^6)
        w = red([0, 0, 0, -1, 0, -1, -1])
        for x in range(-isqrt(4 * p) - 2, isqrt(4 * p) + 3):
            for y in range(-isqrt(p) - 2, isqrt(p) + 3):
                if x * x + x * y + 2 * y * y == p:
                    return zadd(red([x]), zscal(y, w))
    if f == 2:   # generator in Z[eta], eta = z + z^-1
        eta = red([0, 1, 0, 0, 0, 0, 1]); eta2 = zmul(eta, eta)
        for x, y, zz in product(range(-15, 16), repeat=3):
            g = zadd(zadd(red([x]), zscal(y, eta)), zscal(zz, eta2))
            if abs(norm(g)) == p ** 2:
                return g
    if f == 1:   # short vectors of the ideal lattice (p, zeta - r)
        r = next(x for x in range(2, p) if pow(x, 7, p) == 1)
        B = [[p, 0, 0, 0, 0, 0]] + [[-pow(r, i, p)] + [0] * (i - 1) + [1] + [0] * (5 - i)
                                   for i in range(1, 6)]
        B = lll(B)
        for c in product(range(-1, 2), repeat=6):
            g = tuple(sum(c[i] * B[i][j] for i in range(6)) for j in range(6))
            if any(g) and abs(norm(g)) == p:
                return g
    raise RuntimeError(f"no generator found for p={p}")

def lll(B):
    """Plain LLL for the T2 form (exact rationals). Only used to *find*
    candidates; correctness is checked by exact norms."""
    def gram(u, v):   # Tr(u * conj(v))
        return trace(zmul(u, sigma(v, 6)))
    B = [tuple(b) for b in B]; n = len(B)
    def gso(B):
        mu = [[Fraction(0)] * n for _ in range(n)]; Bs = [Fraction(0)] * n
        for i in range(n):
            for j in range(i):
                mu[i][j] = (gram(B[i], B[j]) - sum(mu[i][k] * mu[j][k] * Bs[k] for k in range(j))) / Bs[j]
            Bs[i] = gram(B[i], B[i]) - sum(mu[i][k] ** 2 * Bs[k] for k in range(i))
        return mu, Bs
    k = 1
    while k < n:
        mu, Bs = gso(B)
        for j in range(k - 1, -1, -1):
            qq = round(mu[k][j])
            if qq:
                B[k] = tuple(x - qq * y for x, y in zip(B[k], B[j])); mu, Bs = gso(B)
        if Bs[k] >= (Fraction(3, 4) - mu[k][k - 1] ** 2) * Bs[k - 1]:
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]; k = max(k - 1, 1)
    return B

def local_series(ideals, p, N):
    """ideals: list of (norm, Psi value in Z[zeta]). Returns dict p^k -> exact
    coefficient (must be a rational integer)."""
    kmax = 0
    while p ** (kmax + 1) <= N:
        kmax += 1
    coeffs = [ZZERO] * (kmax + 1); coeffs[0] = ZONE
    for nrm, psi in ideals:
        f = 0; t = nrm
        while t > 1:
            t //= p; f += 1
        new = [ZZERO] * (kmax + 1)
        for k in range(kmax + 1):
            if coeffs[k] == ZZERO:
                continue
            pw = ZONE; j = 0
            while k + f * j <= kmax:
                new[k + f * j] = zadd(new[k + f * j], zmul(coeffs[k], pw))
                pw = zmul(pw, psi); j += 1
        coeffs = new
    out = {}
    for k, c in enumerate(coeffs):
        assert all(x == 0 for x in c[1:]), (p, k, c)   # rational integer
        out[p ** k] = c[0]
    return out

def part_B():
    print(f"Part B: exact Dirichlet coefficients a_n for n <= {NMAX}")
    local = {}
    nprimes = 0
    for p in primes_upto(NMAX):
        if p == 2:
            continue                               # Euler factor 1 at two
        if p == 7:
            ideals = [(7, Psi(zsub(ZONE, ZETA)))]
        else:
            f = next(k for k in range(1, 7) if pow(p, k, 7) == 1)
            if p ** f > NMAX:
                continue
            if f == 6:
                g = red([p])
                reps = (1,)
            else:
                g = find_generator(p, f)
                reps = {1: range(1, 7), 2: (1, 2, 3), 3: (1, 3)}[f]
            # exact verification: norm p^f  =>  (g) is a prime of residue degree f
            assert abs(norm(g)) == p ** f, (p, g)
            ideals = [(p ** f, Psi(sigma(g, r))) for r in reps]
        nprimes += len(ideals)
        local[p] = local_series(ideals, p, NMAX)
    # multiplicativity
    a = [0] * (NMAX + 1); a[1] = 1
    spf = list(range(NMAX + 1))
    for i in range(2, isqrt(NMAX) + 1):
        if spf[i] == i:
            for j in range(i * i, NMAX + 1, i):
                if spf[j] == j:
                    spf[j] = i
    for n in range(2, NMAX + 1):
        p = spf[n]; m = n; pk = 1
        while m % p == 0:
            m //= p; pk *= p
        a[n] = a[m] * local.get(p, {}).get(pk, 0)
    nz = [n for n in range(1, NMAX + 1) if a[n]]
    print(f"  verified {nprimes} prime-ideal generators by exact norms")
    print(f"  {len(nz)} nonzero coefficients; a_7 = {a[7]}, a_29 = {a[29]}, a_43 = {a[43]}")
    ok = all(abs(a[n]) <= n * d6(n) for n in nz)
    check(ok, "|a_n| <= n d_6(n) for all n <= NMAX   (eq. (22))")
    print()
    return a

def d6(n):
    r = 1; m = n; p = 2
    while p * p <= m:
        e = 0
        while m % p == 0:
            m //= p; e += 1
        r *= comb(e + 5, 5); p += 1
    if m > 1:
        r *= 6
    return r

# ---------------------------------------------------------------------
#  Part C: interval evaluation of L(2) and of the period
# ---------------------------------------------------------------------
def H_kernel(r, x):
    """Enclosure of H_r(x) by the series (24), truncated at m = MSER-1,
    plus the rigorous truncation bound of Section 6.2 (valid for
    1/5 < x < 2500 and m >= 90)."""
    lx = log_interval(x)
    tot = I(0); h = Fraction(0); h2 = Fraction(0); fact = 1
    xp = x ** r
    for m in range(MSER):
        if m > 0:
            h += Fraction(1, m); h2 += Fraction(1, m * m); fact *= m
        A = (I.q(h) - GAMMA_E) * 3 - lx
        br = A * A / 2 + A / I.q(m + r) + I.q(Fraction(1, (m + r) ** 2)) \
             + (ZETA2 + I.q(h2)) * Fraction(3, 2)
        term = xp * br / I.q(fact ** 3 * (m + r))
        tot = tot + (term if m % 2 == 1 else -term)
        xp = xp * x
    # truncation bound: first omitted majorant x^(90+r) 90^2 / ((90!)^3 (90+r)),
    # geometric with ratio < 1/290  ->  multiply by 290/289.
    m = MSER
    xhi = x.frac()[1]
    f90 = 1
    for j in range(2, m + 1):
        f90 *= j
    bound = xhi ** (m + r) * m * m / (Fraction(f90) ** 3 * (m + r)) * Fraction(290, 289)
    return (tot + 1).widen(bound)

def part_C(a):
    print("Part C: interval evaluation")
    print(f"  pi      in {PI}")
    print(f"  gamma_E in {GAMMA_E}")
    print(f"  Q       in {Q}")
    nz = [n for n in range(1, NMAX + 1) if a[n]]
    L = I(0)
    for n in nz:
        x = I.q(n) / Q
        lo, hi = x.frac()
        assert Fraction(1, 5) < lo and hi < 2500, "kernel bound range"
        t = H_kernel(2, x) / (n * n) + H_kernel(1, x) / (Q * n)
        L = L + t * a[n]
    # outer tail (25) with t = 12, N = NMAX
    t = T_TAIL; N = NMAX
    fact = lambda k: 1 if k < 2 else k * fact(k - 1)
    tail = (ZETA2 ** 6) * ((Q ** t) * I.q(Fraction(fact(t + 1) ** 3, N ** (t - 1)))
                           + (Q ** (t - 1)) * I.q(Fraction(fact(t) ** 3, N ** (t - 2))))
    tail_hi = tail.frac()[1]
    print(f"  outer tail bound (25): {float(tail_hi):.3e}")
    L = L.widen(tail_hi)
    print(f"  L(2)    in {L}")
    # periods I_j = (1/7) B((j+1)/7, 1/2), Appendix A
    Ms = 200
    Ivals = []
    for j in range(3):
        a_ = Fraction(j + 1, 7)
        two_neg_a = 1 / root_of_rational(Fraction(2) ** (j + 1), 7)   # 2^{-a}
        s1 = Fraction(0); s2 = Fraction(0); ck = Fraction(1); dk = Fraction(1)
        for k in range(Ms):
            s1 += ck / (Fraction(2) ** k * (7 * k + j + 1))
            s2 += dk / (Fraction(2) ** k * (2 * k + 1))
            ck = ck * (2 * k + 1) / (2 * k + 2)          # binom(2k,k)/4^k
            dk = dk * (1 - a_ + k) / (k + 1)              # (1-a)_k/k!
        t1 = Fraction(2, 2 ** Ms * 7 * Ms)                # tail bounds, coefficients <= 1
        t2 = Fraction(2, 2 ** Ms * (2 * Ms + 1))
        Ij = two_neg_a * I.q(s1).widen(t1) + SQRT2 * I.q(s2).widen(t2) / 7
        Ivals.append(Ij)
        print(f"  I_{j}     in {Ij}")
    Pr = (Ivals[0] * Ivals[1] * Ivals[2]) ** 2 * 343
    q = L / Pr
    v = q * 1792
    print(f"  q       in {q}")
    print(f"  1792 q  in {v}")
    check(v.contains_only_in(Fraction(3199, 100), Fraction(3201, 100)),
          "|1792 q - 32| < 1/100   (eq. (26))")
    print()
    return L, q

if __name__ == "__main__":
    t0 = time.time()
    print(f"Certificate for L_K(Psi,2), K = Q(zeta_7); precision {PREC} bits\n")
    part_A()
    a = part_B()
    part_C(a)
    print("Conclusion: with Proposition 4.2 (1792 q in Z), q = 32/1792 = 1/56,")
    print("            so L_K(Psi,2) = (49/8)(I_0 I_1 I_2)^2.")
    print(f"Total time {time.time() - t0:.1f} s")
