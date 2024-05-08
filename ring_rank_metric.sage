  #####################################################################
  #  On the Generalizations of the Rank Metric Over
  #              Finite Chain Rings  
  #####################################################################

           # H. T. Kamche (hermann.tchatchiem@gmail.com) and
           # H. T. Kalachi  (hervekalachi@gmail.com)



"""
In this source code, we implement the formula that allows counting the numbers of matrices and modules over finite chain rings.

The settings:
q is the cardinality of the residue field
nu is the nilpotence index
m is the degree of Galois extension
k is the dimension of the linear code
n is the length of the linear code
"""

#
def CountingSubModuleShape(L1,L2,q,nu):
    # This function counts the number of submodules of shape L1 contained in a module of shape L2.
    return prod([q^(L1[i+1]*(L2[i]-L1[i]))*q_binomial(L2[i]-L1[i+1],L1[i]-L1[i+1],q)  for i in range(nu)])

#
def CountingSubModuleGenerator(q,nu,r,u):
    # This function counts the number of submodules with a minimum number of generators r contained in a free module of rank u.
    P1=PartitionsInBox(r,nu) 
    P2=[P1[i] for i in range(len(P1)) if P1[i].length()==r] 
    lp=len(P2)
    P3=[P2[i].conjugate() for i in range(lp)]
    P4=[P3[i]+[0 for j in range(nu+1-len(P3[i]))] for i in range(lp)]
    L=[u for i in range(nu)]
    return sum([CountingSubModuleShape(P4[i],L,q,nu) for i in range(lp)])
#
def CountingSubModuleLength(q,nu,r,u):
    # This function counts the number of submodules of length r contained in a free module of rank u.
    P1=PartitionsInBox(nu,r) 
    P2=[P1[i]  for i in range(len(P1)) if P1[i].size()==r]
    lp=len(P2)
    P3=[P2[i]+[0 for j in range(nu+1-len(P2[i]))] for i in range(lp)]
    L=[u for i in range(nu)]
    return sum([CountingSubModuleShape(P3[i],L,q,nu) for i in range(lp)])
#
def CountingMatrixBallGenerator(q,nu,r,m,n):
    # This function calculates the cardinality of the ball of radius r with 
    # the metric d_g defined with a minimum number of generators of modules.
    P1=PartitionsInBox(r,nu) 
    lp=len(P1)
    P2=[P1[i].conjugate() for i in range(lp)]
    P3=[P2[i]+[0 for j in range(nu+1-len(P2[i]))] for i in range(lp)]
    L=[n for i in range(nu)]
    k1=[sum(P3[i]) for i in range(lp)]
    k2=[P3[i][0] for i in range(lp)]
    return sum([q^(m*k1[i])*prod([(1-q^(l-m)) for l in range(k2[i])])*CountingSubModuleShape(P3[i],L,q,nu) for i in range(lp)])
#
def CountingMatrixBallLength(q,nu,r,m,n):
    # This function calculates the cardinality of the ball of radius r with 
    # the metric d_l defined with the length of modules.
    P1=PartitionsInBox(nu,r) 
    P2=[P1[i]  for i in range(len(P1)) if P1[i].size()<=r]
    lp=len(P2)
    P3=[P2[i]+[0 for j in range(nu+1-len(P2[i]))] for i in range(lp)]
    L=[n for i in range(nu)]
    k1=[sum(P3[i]) for i in range(lp)]
    k2=[P3[i][0] for i in range(lp)]
    return sum([q^(m*k1[i])*prod([(1-q^(l-m)) for l in range(k2[i])])*CountingSubModuleShape(P3[i],L,q,nu) for i in range(lp)])
#
def ComplexityGenerator(q,nu,m,n,k,r):
    # This function calculates the average complexity  of the Error Support Attack with the metric d_g. 
    u=floor(m*(n-k)/n)
    prob=q^(nu*r*(u-m))
    return ceil(log(m*(n-k)*u^2*n^2/prob,2).n())
#
def ComplexityLength(q,nu,m,n,k,r):
    # This function calculates the average complexity  of the Error Support Attack with the metric d_l. 
    u=floor(m*(n-k)/n)
    prob=q^(r*(u-m))
    return ceil(log(m*(n-k)*u^2*n^2/prob,2).n())
#
def ProbabilityGenerator(q,nu,m,n,k,r):
    # This function compares the probability of the error support attack with the metric d_g and its approximation .
    u=floor(m*(n-k)/n)
    ProbaReal=(CountingSubModuleGenerator(q,nu,r,u)/CountingSubModuleGenerator(q,nu,r,n)).n()
    ProbaApprox=(q^(nu*r*(u-m))).n()
    return [ProbaReal,ProbaApprox,ProbaApprox/ProbaReal]
#
def ProbabilityLength(q,nu,m,n,k,r):
    # This function compares the probability of the error support attack with the metric d_l and its approximation .
    u=floor(m*(n-k)/n)
    ProbaReal=(CountingSubModuleLength(q,nu,r,u)/CountingSubModuleLength(q,nu,r,n)).n()
    ProbaApprox=(q^(r*(u-m))).n()
    return [ProbaReal,ProbaApprox,ProbaApprox/ProbaReal]


######
# Example of computation of the cardinalities of balls. 
######

# The following example was given in Example 4 of the article.

print( "|B_{d_g}(0,r)-{0}|=",CountingMatrixBallGenerator(q=2,nu=2,r=2,m=6,n=6)-1)

print( "|B_{d_g}(0,r)-{0}|=",CountingMatrixBallLength(q=2,nu=2,r=2,m=6,n=6)-1)

"""
|B_{d_g}(0,r)-{0}|= 2674147519575
|B_{d_g}(0,r)-{0}|= 10675287
"""


######
# Example on the average complexity  of the Error Support Attack
###### 

# The following example was given in Table 1 of the article.

L=[[2,1],[2,2], [2,3],[2,4], [4,1], [4,2]]
C=[]
for [q,nu] in L:
    C=C+[[ComplexityLength(q,nu,m=32,n=32,k=16,r=4),ComplexityGenerator(q,nu,m=32,n=32,k=16,r=4)]]
print("Average Complexities of the Error Support Attack:")
print(C)
"""
Average Complexities of the Error Support Attack:
[[91, 91], [91, 155], [91, 219], [91, 283], [155, 155], [155, 283]]
"""


######
# Example on the probability  of the Error Support Attack with the metric d_g
###### 

# In the following, we compare the probability of the error support attack with the metric d_g and its approximation 

Pg=[]
for [q,nu] in L:
    Pg=Pg+[ProbabilityGenerator(q,nu,m=32,n=32,k=16,r=4)]
print("Comparison of the probability and its approximation with the d_g metric:")
print(Pg)

"""
Comparison of the probability and its approximation with the d_g metric:
[[5.41977019878713e-20, 5.42101086242752e-20, 1.00022891443638], [2.94882878628801e-39, 2.93873587705572e-39, 0.996577315957026], [1.59857469000227e-58, 1.59309191113245e-58, 0.996570207883244], [8.66589087962539e-78, 8.63616855509444e-78, 0.996570194000385], [2.93873581889636e-39, 2.93873587705572e-39, 1.00000001979060], [8.63621213842903e-78, 8.63616855509444e-78, 0.999994953420100]]
"""


######
# Example on the probability  of the Error Support Attack with the metric d_l
###### 

# In the following, we compare the probability of the error support attack with the metric d_l and its approximation 

Pl=[]
for [q,nu] in L:
    Pl=Pl+[ProbabilityLength(q,nu,m=32,n=32,k=16,r=4)]
print("Comparison of the probability and its approximation with the d_l metric:")
print(Pl)
"""
Comparison of the probability and its approximation with the d_l metric:
[[5.41977019878713e-20, 5.42101086242752e-20, 1.00022891443638], [5.42064963866488e-20, 5.42101086242752e-20, 1.00006663846342], [5.42074004197763e-20, 5.42101086242752e-20, 1.00004996005117], [5.42085576980969e-20, 5.42101086242752e-20, 1.00002861035682], [2.93873581889636e-39, 2.93873587705572e-39, 1.00000001979060], [2.93873587279168e-39, 2.93873587705572e-39, 1.00000000145098]]
"""
print("End")

