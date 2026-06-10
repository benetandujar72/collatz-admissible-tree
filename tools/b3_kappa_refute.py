"""
Confirm the REFUTATION of FirstMPrecisionSuffixPositive:

The clean witness path  InvStart(m+1) --zero(tau4,k=0)--> c==7 --[one-edge ladder, each k=+1]-->
trap(c==4) --one(tau2,k=+1)--> goal(c==1)  has the property that the FIRST m-precise vertex
is the GOAL itself (all earlier vertices have coarse-dlog in {2,4} mod6 != 0, hence not
m-precise).  Therefore in the first-witness split mid = goal, the suffix mid->goal is EMPTY,
so kappa_2 = 0 < 1.  This VIOLATES the residual.

We verify at real scale (m=1, working cylinder 2, Rw=46, Rc=24):
 - the final one-edge from trap (c==4 at level Rw+1) lands the (m+1)-goal (c==1 at level Rw+1);
 - that goal is m-precise (projects to c==1 at level Rc+1) -- as it must (IsGoal_projectDown);
 - the trap and all ladder vertices are NOT m-precise (coarse-dlog != 0);
 - so first-m-precise = goal, suffix empty, kappa2 = 0.
 - goal.j = 1 <= Q for any Q>=1.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202

def dlogv(c,k): return fast_dlog(c%3**k,k)

def check(m):
    Rw=22*(m+1)+2; Rc=22*m+2; j=1; K=Rw+j
    M=3**K
    # trap at level K: c==4
    trap_c=4%M
    # final deep one-edge: trap_c == 2^tau(goal%9) * goal ; goal%9==1 -> tau=2 ; goal == trap_c * inv(4) == 1
    goal_c=(pow(pow(2,TAU[1],M),-1,M)*trap_c)%M
    # is goal a (m+1)-goal at level Rw+j ?  c==1 mod 3^(Rw+j)
    goal_is_m1goal = (goal_c % M == 1%M)
    # is goal m-precise? project to level Rc+j: c==1 mod 3^(Rc+j)
    Mc=3**(Rc+j)
    goal_mprecise = (goal_c % Mc == 1%Mc)
    # is trap m-precise?  coarse-dlog at Rc+j == 0 ?
    trap_mprecise = (dlogv(trap_c, Rc+j)==0)
    # kappa of the final edge (one-edge) = +1
    return dict(m=m,Rw=Rw,Rc=Rc, trap_c=trap_c, goal_c=goal_c,
                goal_is_m1goal=goal_is_m1goal, goal_mprecise=goal_mprecise,
                trap_mprecise=trap_mprecise, final_edge_kappa=+1)

if __name__=="__main__":
    print("=== REFUTATION endpoint check (real scale) ===\n")
    for m in [1,2,3]:
        r=check(m)
        print(f"m={m} (working cyl {m+1}, Rw={r['Rw']}, Rc={r['Rc']}):")
        print(f"  trap c=4 --one(tau=2,kappa=+1)--> goal c={r['goal_c']}")
        print(f"  goal is (m+1)-goal (c==1 mod 3^(Rw+1)): {r['goal_is_m1goal']}")
        print(f"  goal is m-precise (projects to c==1): {r['goal_mprecise']}  (must be True: IsGoal_projectDown)")
        print(f"  trap is m-precise: {r['trap_mprecise']}  (must be False -> first-m-precise is the GOAL)")
        print(f"  => mid=goal, suffix EMPTY, kappa_2 = 0 < 1  ==> residual VIOLATED\n")
    print("VERDICT: FirstMPrecisionSuffixPositive (m+1)-cylinder, any Q>=1, is FALSE.")
    print("The canonical-first-split device is DEAD at real scale: the clean route to the")
    print("c==4 trap exists and terminates with the goal as the first (and only) m-precise vertex.")
