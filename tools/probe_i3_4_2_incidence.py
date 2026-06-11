#!/usr/bin/env python3
"""Feasibility probe for F4c: incidence-matrix CNF for I3(l=4,t=2) at B rows
over n=B*4 points. NOT the certified generator - solver feasibility only.

Encoding:
  x[i][p]   row i contains point p
  exactly-4 per row via sequential counters (atmost-4 true + atleast-4 true)
  c[i][j][p] <-> x[i][p] & x[j][p]   (common point)
  per pair: atleast-1 c (intersecting), atmost-2 c (cap)
  per triple (i,j,k): some p where pairwise commons differ (SF-free):
    u = c_ij xor c_ik, v = c_ij xor c_jk, clause OR_p (u_p | v_p)
  symmetry: row0 = {0,1,2,3}; rows lex-decreasing.
"""
import sys, subprocess

B = int(sys.argv[1]) if len(sys.argv) > 1 else 13
L, T = 4, 2
N = B * L

nv = 0
def newvar():
    global nv; nv += 1; return nv

clauses = []
def add(*lits): clauses.append(list(lits))

x = [[newvar() for p in range(N)] for i in range(B)]

def atmost_seq(lits, k):
    """sequential counter: at most k of lits true"""
    n = len(lits)
    if k >= n: return
    s = [[newvar() for j in range(k)] for i in range(n)]
    add(-lits[0], s[0][0])
    for j in range(1, k): add(-s[0][j])
    for i in range(1, n):
        add(-lits[i], s[i][0])
        add(-s[i-1][0], s[i][0])
        for j in range(1, k):
            add(-lits[i], -s[i-1][j-1], s[i][j])
            add(-s[i-1][j], s[i][j])
        add(-lits[i], -s[i-1][k-1])

def exactly(lits, k):
    atmost_seq(lits, k)
    atmost_seq([-v for v in lits], len(lits) - k)

for i in range(B):
    exactly(x[i], L)

c = {}
for i in range(B):
    for j in range(i+1, B):
        cij = []
        for p in range(N):
            v = newvar()
            add(-v, x[i][p]); add(-v, x[j][p]); add(v, -x[i][p], -x[j][p])
            cij.append(v)
        c[(i,j)] = cij
        add(*cij)                # intersecting
        atmost_seq(cij, T)       # cap

def xorvar(a, b):
    u = newvar()
    add(-u, a, b); add(-u, -a, -b); add(u, a, -b); add(u, -a, b)
    return u

for i in range(B):
    for j in range(i+1, B):
        for k in range(j+1, B):
            ws = []
            for p in range(N):
                ws.append(xorvar(c[(i,j)][p], c[(i,k)][p]))
                ws.append(xorvar(c[(i,j)][p], c[(j,k)][p]))
            add(*ws)             # not a sunflower

# precedence: point p (>= L+1) first used only after p-1 has appeared
# u[p][i]: point p used somewhere in rows 0..i
u = {}
for pp in range(L, N):
    for i in range(B):
        u[(pp,i)] = newvar()
        if i == 0:
            add(-u[(pp,0)], x[0][pp]); add(-x[0][pp], u[(pp,0)])
        else:
            add(-u[(pp,i)], u[(pp,i-1)], x[i][pp])
            add(-u[(pp,i-1)], u[(pp,i)]); add(-x[i][pp], u[(pp,i)])
for pp in range(L+1, N):
    for i in range(B):
        add(-x[i][pp], u[(pp-1,i)])

# symmetry: row0 fixed
for p in range(N):
    add(x[0][p] if p < L else -x[0][p])
# lex-decreasing rows: row_i >=lex row_{i+1}
for i in range(B-1):
    a, b = x[i], x[i+1]
    eq = None
    for p in range(N):
        if eq is None:
            add(a[p], -b[p])
            ne = newvar()
            add(-ne, a[p]); add(-ne, -b[p])  # ne -> a&~b ... actually ne means strictly greater here
            # eq_p = a_p == b_p prefix tracking
            e = newvar()
            add(-e, a[p], -b[p]); add(-e, -a[p], b[p])
            eq = e
        else:
            # eq so far -> a_p >= b_p
            add(-eq, a[p], -b[p])
            e = newvar()
            add(-e, eq); 
            add(-e, a[p], -b[p]); add(-e, -a[p], b[p])
            eq = e

fn = f"/tmp/i3_4_2_B{B}.cnf"
with open(fn, "w") as f:
    f.write(f"p cnf {nv} {len(clauses)}\n")
    for cl in clauses:
        f.write(" ".join(map(str, cl)) + " 0\n")
print(f"{fn}: {nv} vars, {len(clauses)} clauses", flush=True)
