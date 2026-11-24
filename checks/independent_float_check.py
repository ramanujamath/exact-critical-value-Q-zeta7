"""Independent (non-rigorous) double-precision check of L_K(Psi,2) for the septic CM character.
Builds Psi from definition (1) of the manuscript, computes a_n, and evaluates
L(2) by the approximate functional equation with two different splitting
parameters (this also tests the functional equation and root number)."""
import numpy as np
from fractions import Fraction
from itertools import product
from scipy.special import loggamma, gamma

Z7 = np.exp(2j*np.pi/7)

def emb(v, a):
    return sum(int(v[j])*Z7**(a*j % 7) for j in range(6))

def norm(v):
    return round(np.prod([emb(v, a) for a in range(1, 7)]).real)

def reduce_phi(coeffs):  # list of ints, any length -> length 6 in basis 1..z^5
    c = [0]*7
    for i, x in enumerate(coeffs):
        c[i % 7] += x
    return [c[j]-c[6] for j in range(6)]

# ---- nu: residues mod 2 in F8 x F8 -----
def polmod2(c, g):  # c over F2 as list low->high, g monic
    c = [x % 2 for x in c]
    while len(c) >= len(g):
        if c[-1]:
            s = len(c)-len(g)
            for i, gi in enumerate(g):
                c[s+i] ^= gi
        c.pop()
    return tuple(c + [0]*(len(g)-1-len(c)))

G1 = [1, 1, 0, 1]  # X^3+X+1
G2 = [1, 0, 1, 1]  # X^3+X^2+1
def dlog_table(g):
    t = {}
    for A in range(7):
        t[polmod2([0]*A+[1], g)] = A
    return t
DL1, DL2 = dlog_table(G1), dlog_table(G2)

def nu(v):
    r1, r2 = polmod2(list(v), G1), polmod2(list(v), G2)
    if r1 not in DL1 or r2 not in DL2:
        return 0
    return Z7**(4*(DL1[r1]+DL2[r2]) % 7)

S = (1, 4, 5)
def Psi(v):
    PS = np.prod([emb(v, a) for a in S])
    return nu(v)*PS**2

# ---- LLL on Gram matrix of T2 form ----
def T2gram(B):
    E = np.array([[emb(b, a) for a in range(1, 7)] for b in B])
    G = (E @ E.conj().T).real
    return np.rint(G).astype(object)

def lll(B):
    B = [list(b) for b in B]
    n = len(B)
    def gso(B):
        G = T2gram(B)
        mu = [[Fraction(0)]*n for _ in range(n)]
        Bs = [Fraction(0)]*n
        for i in range(n):
            for j in range(i):
                mu[i][j] = (Fraction(int(G[i][j])) - sum(mu[i][k]*mu[j][k]*Bs[k] for k in range(j)))/Bs[j]
            Bs[i] = Fraction(int(G[i][i])) - sum(mu[i][k]**2*Bs[k] for k in range(i))
        return mu, Bs
    k = 1
    while k < n:
        mu, Bs = gso(B)
        for j in range(k-1, -1, -1):
            q = round(mu[k][j])
            if q:
                B[k] = [x-q*y for x, y in zip(B[k], B[j])]
                mu, Bs = gso(B)
        if Bs[k] >= (Fraction(3, 4)-mu[k][k-1]**2)*Bs[k-1]:
            k += 1
        else:
            B[k], B[k-1] = B[k-1], B[k]
            k = max(k-1, 1)
    return B

def generator_split(p, r):
    B = [[p]+[0]*5] + [[-(pow(r, i, p))] + [0]*(i-1) + [1] + [0]*(5-i) for i in range(1, 6)]
    B = lll(B)
    best = None
    for c in product(range(-1, 2), repeat=6):
        v = [sum(c[i]*B[i][j] for i in range(6)) for j in range(6)]
        if any(v) and abs(norm(v)) == p:
            return v
    raise RuntimeError(p)

def primes(N):
    s = bytearray([1])*(N+1); s[0:2] = b'\x00\x00'
    for i in range(2, int(N**0.5)+1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]

def _gal(v, a):
    c = [0]*7
    for j in range(6):
        c[(a*j) % 7] += v[j]
    return [c[j]-c[6] for j in range(6)]

NMAX = 20000
a = np.zeros(NMAX+1, dtype=complex); a[1] = 1
def mult_euler(local):  # local: dict power-> coefficient for prime power series
    global a
    new = np.zeros_like(a)
    for n in range(1, NMAX+1):
        if a[n] == 0: continue
        for m, c in local.items():
            if n*m > NMAX: break
            new[n*m] += a[n]*c
    a = new

for p in primes(NMAX):
    if p == 2:
        continue  # Euler factor 1 at two (conductor)
    if p == 7:
        lam = [1, -1, 0, 0, 0, 0]
        vals = [(7, Psi(lam))]
    else:
        f = next(k for k in range(1, 7) if pow(p, k, 7) == 1)
        if p**f > NMAX:
            continue
        if f == 1:
            r = next(x for x in range(2, p) if pow(x, 7, p) == 1)
            g = generator_split(p, r)
            vals = [(p, Psi(_gal(g, s))) for s in range(1, 7)]
        elif f == 6:
            vals = [(p**6, Psi([p, 0, 0, 0, 0, 0]))]
        elif f == 3:  # generator from Q(sqrt(-7)): w=(1+sqrt-7)/2 = -(z^3+z^5+z^6)
            w = reduce_phi([0, 0, 0, -1, 0, -1, -1])
            sol = next((x, y) for x in range(-200, 200) for y in range(-200, 200) if x*x+x*y+2*y*y == p)
            g = [sol[0]*(i == 0) + sol[1]*w[i] for i in range(6)]
            assert abs(norm(g)) == p**3
            vals = [(p**3, Psi(g)), (p**3, Psi(_gal(g, 3)))]
        elif f == 2:  # generator in K^+ = Z[eta], eta = z + z^6
            eta = reduce_phi([0, 1, 0, 0, 0, 0, 1])
            eta2 = reduce_phi([2, 0, 1, 0, 0, 1, 0])
            g = None
            for x, y, z in product(range(-12, 13), repeat=3):
                v = [x*(i == 0)+y*eta[i]+z*eta2[i] for i in range(6)]
                if abs(norm(v)) == p**2:
                    g = v; break
            vals = [(p**2, Psi(_gal(g, s))) for s in (1, 2, 3)]
    for q, psi in vals:
        local = {1: 1}
        k = 1
        while q**k <= NMAX:
            local[q**k] = psi**k; k += 1
        mult_euler(local)

print("max |Im a_n| =", np.abs(a.imag).max())
an = np.rint(a.real)
print("max |a_n - round| =", np.abs(a.real-an).max())
print("first a_n:", [int(x) for x in an[1:30]])

Q = 7**2.5/np.pi**3
def H(r, x, c=1.5, T=40, M=40001):
    t = np.linspace(-T, T, M); z = c+1j*t
    f = np.exp(3*loggamma(r+z) - z*np.log(x))/z
    return (np.trapezoid(f, t)/(2*np.pi)).real

def L2(A):
    tot = 0.0
    for n in range(1, NMAX+1):
        if an[n] == 0: continue
        x = n/Q
        t1 = H(2, x/A)/n**2 if x/A < 6000 else 0
        t2 = H(1, x*A)/(Q*n) if x*A < 6000 else 0
        tot += an[n]*(t1+t2)
    return tot

I = [gamma((j+1)/7)*gamma(0.5)/gamma((j+1)/7+0.5)/7 for j in range(3)]
P = 343*(I[0]*I[1]*I[2])**2
for A in (1.0, 1.25):
    v = L2(A)
    print(f"A={A}: L(2)={v:.14f}  q=L/P={v/P:.14f}  1/56={1/56:.14f}")
