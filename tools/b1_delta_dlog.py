"""
B1 -- The delta-plus <-> dlog dictionary, and the TRAP geometry.

rhoPlus(c,r) = nu3(c-1) capped at r   (= r if c==1)
deltaPlus(c,r) = r - rhoPlus
dlog(c) == 0 mod 2*3^{t-1}  <=>  c == 1 mod 3^t  <=>  rhoPlus(c, >=t) >= t.

Connection of the TRAP to delta+:
  trap: c == 4 mod 3^{k}, k=Rbar+j.  c-1 == 3 mod 3^k -> nu3(c-1)=1 -> rhoPlus=1 -> deltaPlus=k-1 (near max).
  goal: c == 1 mod 3^k -> rhoPlus=k -> deltaPlus=0.
  start: aS202=1+3^22 -> nu3(3^22)=22 capped at 24 -> rho=22, delta=2.
"""
def nu3(n, cap):
    if n == 0: return 0
    c = 0
    while c < cap and n % 3 == 0:
        n//=3; c+=1
    return c
def rhoPlus(c, r):
    return r if c==1 else nu3(c-1, r)
def deltaPlus(c, r):
    return r - rhoPlus(c,r)

aS202 = 1+3**22
# start m=1: R=24
print("start delta+(aS202,24) =", deltaPlus(aS202,24), " (Lean: =2)  CONFIRMED" if deltaPlus(aS202,24)==2 else " MISMATCH")

# For the (m+1)-barrier with M=m+1>=2, Rbar=22M+2. start delta+:
for M in [2,3,4]:
    Rbar=22*M+2
    a=aS202%3**Rbar
    print(f"  M={M}: Rbar={Rbar}, delta+(start,Rbar)={deltaPlus(a,Rbar)}  (=22*1-20=2? predicted 22(M-1)-20+22? ) rho={rhoPlus(a,Rbar)}")

print("\n=== TRAP vs GOAL delta+ at level k ===")
for k in [24,25,26,46]:
    print(f"  k={k}: trap(c=4) rho={rhoPlus(4,k)} delta={deltaPlus(4,k)} ;  goal(c=1) rho={rhoPlus(1,k)} delta={deltaPlus(1,k)}")

print("""
KEY GEOMETRY:
  delta+(start)  = 2         (small, near root)
  delta+(goal)   = 0         (at root)
  delta+(trap)   = k-1       (MAXIMAL -- as FAR from the root as possible)

So the trap is the *least* precise non-trivial residue. Reaching the trap means
delta+ must CLIMB from 2 to k-1.  Per the verified bricks:
  * one-edge: delta+ can DROP (discrete-log jump) or stay; bounded structure.
  * tau=1,3 zero-edge: delta+ RESETS TO MAX (k-1-ish).   <-- THIS reaches trap-like delta!
  * tau=2 zero-edge: delta+ UNCHANGED.
  * tau=4 zero-edge: (even>=4) -- the D3 residual gap.

So delta+ ALONE does NOT forbid reaching high delta+: a single tau=1 or tau=3 zero-edge
throws delta+ to the max. The trap has delta+ = k-1 which is exactly the RESET value.
Hence the trap's delta+ is TRIVIALLY reachable (one tau=1 zero from anywhere).
=> delta+ is NOT a separating invariant. The separation (if any) is the EXACT residue 4,
   not its delta+ class.
""")

# Confirm: after a tau=1 zero-edge, what is the residue mod 9 and mod 27? The reset sends
# rho+ to 1 but the actual c mod 3^k is determined. Is c==4 mod 3^k *achievable* as a target/source?
# The trap is a SOURCE of a one-edge. Its c==4 mod 3^k. We need c==4 exactly, not just rho=1.
# c==4 mod 3^k means c == 4 mod 9 (-> in X, tau(4)=2), and c==4 mod 27, ..., up to 3^k.
# Among residues with rho+=1 (i.e. c==1+3*u, u not div by 3 => c mod 9 in {4,7}), c==4 is HALF.
print("Residues c with rho+(c)=1 (c-1 == 3 mod 9, i.e. c%9 in {4,7}); trap needs c%9==4 specifically.")
print("  c%9==4: c in {4,13,22,...}; c%9==7: {7,16,25,...}. Trap is the c%9==4 (dlog 2) sub-branch.")
print("  Note c%9==7 has dlog(7 mod 9)? ", end="")
# dlog of 7 mod 9: 2^t mod 9: 1,2,4,8,7,5 -> 7 at t=4. dlog(4 mod9)=2.
pw=1
d9={}
for t in range(6):
    d9[pw]=t; pw=(pw*2)%9
print("dlog(7 mod9)=",d9[7],", dlog(4 mod9)=",d9[4])
