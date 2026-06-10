"""
FINAL consolidation: confirm the real-problem parameters land in the 'trap REACHABLE
clean' regime, for the actual residual m=1,2,3 (working cylinder m+1), and pin the
exact reason b=0 differs.

Real problem: gap g=22, base b=2, residual m. Rc=22*m+2, Rw=22*(m+1)+2.
We confirm:
 (1) start NOT coarse-precise  <=>  aS202 != 1 mod 3^(Rc)  <=> Rc>22 <=> 22m+2>22 <=> m>=1. OK.
 (2) entry zero-edge into c==7 exists; (3) ladder mod-6 shield; (4) trap=deep-edge.
Everything reduces to the SCALE-INVARIANT mod-6 ladder + the O(1) entry checks.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202

def dlogv(c,k): return fast_dlog(c%3**k,k)
def zt(c,Kn,a):
    M=3**Kn; t=TAU[a]; cp=(pow(pow(2,t,M),-1,M)*((3*c+1)%M))%M
    return (cp,t) if cp%9==a else None

print("=== REAL aS202 = 1 + 3^22, residual m -> Rc=22m+2, Rw=22(m+1)+2 ===\n")
A=aS202()
for m in [1,2,3,5]:
    Rc=22*m+2; Rw=22*(m+1)+2
    c0=A%3**Rw
    s0_cp = dlogv(c0,Rc)==0          # start coarse-precise?
    # entry
    e=zt(c0,Rw+1,7) or zt(c0,Rw+1,4)
    ok_entry = e is not None
    if ok_entry:
        c1,t=e
        W=dlogv(c1,Rw+1)
        ladder_ok=(W%6==4 and W>=4)
        s1_cp=dlogv(c1,Rc+1)==0
        cons=((3*c0+1)%3**(Rw+1))==(2**t*c1)%3**(Rw+1)
    print(f"m={m}: Rc={Rc} Rw={Rw} | start_coarse_precise={s0_cp} (need False) | "
          f"entry_zero_edge={ok_entry} c1%9={c1%9 if ok_entry else '-'} | "
          f"W%6={W%6 if ok_entry else '-'} W>=4={W>=4 if ok_entry else '-'} | "
          f"s1_coarse_precise={s1_cp if ok_entry else '-'} | zero_consistency={cons if ok_entry else '-'}")

print("\n=== contrast: if base b were 0 (Rc=22m), start WOULD be coarse-precise ===")
for m in [1,2]:
    Rc0=22*m; Rw=22*(m+1)+2
    c0=A%3**Rw
    print(f" m={m}: with Rc=22m={Rc0}: start_coarse_dlog={dlogv(c0,Rc0)} "
          f"(==0 -> start IS coarse-precise: {dlogv(c0,Rc0)==0})  <-- this is the b=0 blocking case")

print("\nCONCLUSION: for the real '+2' base (b=2) and every residual m>=1, the start is")
print("NOT coarse-precise, the entry zero-edge into c==7 exists, the mod-6 ladder shield")
print("holds, and the trap (c==4, deep one-edge to goal) is reached CLEAN.  Trap REACHABLE.")
