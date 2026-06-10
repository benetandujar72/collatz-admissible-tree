"""
B1 -- HOW trap-reachability kills the canonical-first-split device (kappa accounting).

The device (FirstMPrecisionSuffixPositive): on a goal-reaching (m+1)-path, split at the FIRST
m-precise vertex 'mid'; claim the suffix mid->goal has kappa2 >= 1.

The trap c=4 (class 4, tau=2) is the SOURCE of a DEEP one-edge: a one-edge c=4 -> c'=1 (alpha=1,
tau=2) since 4 == 2^2 * 1 (mod 3^(R+j)) means c'==1, a GOAL (c'==1 mod 3^(R+j)). Check: is the
one-edge from c=4 with alpha=1 landing on c'==1 mod 3^(R+j) (a goal AND m-precise)?
  one-edge: c' = invMod2Pow(tau(1)=2, M) * 4 % M = 2^{-2}*4 = 1 mod M. YES, c'==1. GOAL.
So from the trap (j, c=4) a single one-edge reaches (j, c'=1) = a GOAL at level R+j.

Now the goal c'=1 is m-precise (c'==1 mod 3^(R-22+j) trivially). The trap c=4 is NOT m-precise.
And we showed: a path start -> trap exists with NO m-precise vertex before the trap.
=> Along start -> trap -> goal, the FIRST m-precise vertex is the GOAL itself (mid = goal).
=> The split's suffix mid->goal is EMPTY (length 0), so kappa2 = 0, NOT >= 1.
=> FirstMPrecisionSuffixPositive FAILS on this path. The device is DEAD at real scale.

We confirm the deep one-edge trap->goal at R=46 and the precision facts.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
def tau(n): return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
aS202=1+3**22; R=46

# deep one-edge from trap (j, c=4): pick j (say j=1), level L=R+j=47
for j in [1,2,3]:
    L=R+j; M=3**L; inv2=(M+1)//2
    c=4
    cp=(pow(inv2,tau_a(1),M)*c)%M   # alpha=1, tau=2
    is_goal = (cp % M == 1 % M)
    is_mprec_goal = (cp % 3**(R-22+j) == 1)  # m-precise
    trap_mprec = (c % 3**(R-22+j) == 1)
    print(f"j={j}, L={L}: trap c=4 --one-edge(alpha=1,tau=2)--> c'={cp}  is_goal(c'==1)={is_goal}  "
          f"goal_is_mprecise={is_mprec_goal}  trap_is_mprecise={trap_mprec}")

print("""
=> The trap c=4 sits ONE deep one-edge below a goal (c'=1). The deep one-edge is the
   tau=2/alpha=1 edge (S240's unique deep-jump edge). The goal is m-precise; the trap is not;
   and the trap is reachable with no earlier m-precise vertex. Therefore on the path
   start ->...-> trap -> goal, the FIRST m-precise vertex is the goal, the suffix is empty,
   kappa2 = 0, and FirstMPrecisionSuffixPositive is FALSE.  VERDICT: barrier device dead.
""")
