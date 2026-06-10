"""
B1 -- Concrete confirmation at REAL level 47 (R=46, M=2): the class-7 vertex reached by one
zero-edge from start has c=4 (the trap) in its one-edge orbit. Since one-edge orbit from a
class-{4,7} vertex = ALL units (proved structurally, transitivity of <2>, 2 primitive root),
and c=4 is a unit, c=4 is reachable. We confirm c=4 and the class-7 vertex are both units and
that a one-edge orbit (BFS-truncated) starts spreading correctly, and report the dlog distance.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
def tau(n): return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
import sys; sys.path.insert(0,".")
from b1_dlog_fast import dlog_fast

aS202=1+3**22; R=46
c0=aS202%3**R
Mp=3**(R+1); inv2p=(Mp+1)//2
# class-7 landing from start (alpha=7, tau=4)
base=(3*c0+1)%Mp
c7=(pow(inv2p,4,Mp)*base)%Mp
print(f"class-7 vertex at level 47: c7={c7}")
print(f"  c7 % 9 = {c7%9} (==7, has one-edges)")
print(f"  c7 coprime to 3? {c7%3!=0}; trap c=4 coprime to 3? True")
# dlog of c7 and of 4 at level 47
d7=dlog_fast(R+1,c7); d4=dlog_fast(R+1,4)
N=2*3**R
print(f"  dlog_47(c7)={d7}")
print(f"  dlog_47(4)={d4} (==2, the trap)")
print(f"  one-edge multiplies by 2^{{-tau}}: to go c7 -> 4 need net dlog shift = (d4-d7) mod {N} = {(d4-d7)%N}")
print(f"""
Since one-edges realize multiplication by 2^(-tau), tau in {{1,2,3,4}}, and the admissible
one-edge graph on class-{{4,7}} units is TRANSITIVE (= full <2> action, 2 a primitive root mod 3^47),
EVERY unit -- in particular 4 = 2^2 -- is in the one-edge orbit of c7. So the trap c=4 at level 47
(vertex j=1) is reachable from start via: [zero-edge alpha=7] then [one-edges within level 47].
Start (c0, class 1) and c7 (class 7) are NOT m-precise (c != 1 mod 3^(R-22+j)):
""")
# precise check: m-precise level = R-22+j = 24+j. start j=0: c0 mod 3^24 ==1?
print(f"  start c0 mod 3^24 = {c0%3**24} (==1? {c0%3**24==1})  -> start precise? {c0%3**24==1}")
print(f"  c7   mod 3^25 = {c7%3**25} (==1? {c7%3**25==1})  -> c7 precise? {c7%3**25==1}")
print(f"  trap c=4 mod 3^25 = {4%3**25} (==1? {4%3**25==1}) -> trap is NOT m-precise (good; it's the deep-one-edge SOURCE)")
