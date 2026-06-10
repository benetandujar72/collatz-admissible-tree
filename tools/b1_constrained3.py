"""
B1 -- Constrained vs unconstrained trap reachability, EXHAUSTIVE (no cap), faithful r>g.

For each (r,g) with r>g, fix a level cap J (max j) and EXHAUST the reachable set within
levels [r+g, r+g+J] for BOTH:
  (U) unconstrained
  (C) constrained: precise vertices (c==1 mod 3^(r+j)) are terminal (not expanded)
Report: trap (c==4) reachable in U? in C? and the minimal j of a constrained trap.

We pick (r,g,J) so the level r+g+J stays <= ~13 (3^13 ~ 1.6M reps/level) => fully enumerable.
This DIRECTLY answers: does requiring 'trap before any precise vertex' change reachability?

Key faithful cases keep g close to r-? . Use g=r-1 and g=r-2 (real is g=22, r=24 => g=r-2).
"""
import sys
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]
from collections import deque

def exhaust(r, g, J, constrain):
    base=r+g
    c0=(1+3**g) % 3**base
    start=(0,c0)
    def precise(j,c): return c % 3**(r+j) == 1
    seen={start}; dq=deque([start]); trap_js=[]
    while dq:
        j,c=dq.popleft(); L=base+j
        if c==4: trap_js.append(j)
        if constrain and precise(j,c): continue
        M=3**L; inv2=(M+1)//2
        for a in X:
            cp=(pow(inv2,tau_a(a),M)*c)%M
            if cp%9==a and (j,cp) not in seen:
                seen.add((j,cp)); dq.append((j,cp))
        if j+1<=J:
            Mp=3**(L+1); inv2p=(Mp+1)//2
            bb=(3*c+1)%Mp
            for a in X:
                cp=(pow(inv2p,tau_a(a),Mp)*bb)%Mp
                if cp%9==a and (j+1,cp) not in seen:
                    seen.add((j+1,cp)); dq.append((j+1,cp))
    return (len(trap_js)>0, sorted(set(trap_js)), len(seen))

print("=== EXHAUSTIVE constrained vs unconstrained (r>g, faithful) ===", flush=True)
print(f"{'r':>2} {'g':>2} {'J':>2} | {'U:trap?':>8} {'U:trap_js':>12} {'U:states':>9} | {'C:trap?':>8} {'C:trap_js':>12} {'C:states':>9}", flush=True)
cases = [(3,2,8),(3,1,9),(4,2,7),(4,3,6),(5,3,5),(5,4,5),(6,4,4),(6,5,4),(7,5,4),(2,1,10)]
for r,g,J in cases:
    if g>=r: continue
    Ut,Uj,Un = exhaust(r,g,J,False)
    Ct,Cj,Cn = exhaust(r,g,J,True)
    flag = "" if (Ut==Ct) else "  <<< CONSTRAINT CHANGES TRAP REACHABILITY"
    print(f"{r:>2} {g:>2} {J:>2} | {str(Ut):>8} {str(Uj):>12} {Un:>9} | {str(Ct):>8} {str(Cj):>12} {Cn:>9}{flag}", flush=True)
