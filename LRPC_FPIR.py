# I.1. Program
#
def HenselLiftOfPrimitivePolynomial(p,nu,m):
    """
    Input: `p` the characteristic of the residue field,
    `m` the dimension of the Galois extension,
    `nu` the nilpotency index.
    Output: a monic polynomial `h` in `Z_ {p ^ nu}[z]` of degree `m`
    such that `h`  divises `z^(p^m-1)-1` and
    the projection of `h` in `GF(p)[z]` is a primitive polynomial.
    """
    Zpz.<z>=QQ[]
    Hensel=Zpz(z^(p^m-1)-1).hensel_lift(p, nu)
    Conway=conway_polynomial(p,m)
    Fpz.<z>=GF(p)[]
    i=0
    while  Fpz(Conway)!=Fpz(Hensel[i]) :
        i=i+1
    return Hensel[i]
#
#
def InverseOf(u):
    """
    Input: `u` an inverse element in `S=R[a]`
    Output: the inverse of `u`
    """
    S=parent(u)
    Rz=S.cover_ring()
    R=Rz.base_ring()
    P=S(u).charpoly(z)
    mu=R.order()
    d0=ZZ(P[0])
    d1=xgcd(d0,mu)[1]
    d2=R(d1)
    Q=ZZ['z'](P)
    v=ZZ['z']((Q-Q[0])*ZZ(d2))//z
    return S(-v(u))
#    
def SmithNormalFormOf(A):
    """
    Input: a matrix `A`
    Output: [D,P,Q,af]
    Where `af` is a freerank of `A`, `D=diag(d_1,…,d_r)` is a
    Smith normal form of `A` such that `d_1=1`, . . ., `d_af=1`,
    and `P`, `Q` are the invertible matrices such that `D=PAQ`.
    """
    R=A.base_ring()
    mu=R.order()
    L=matrix(ZZ,A)
    D=matrix(R,L.smith_form()[0])
    P=matrix(R,L.smith_form()[1])
    Q=matrix(R,L.smith_form()[2])
    af=0
    r=min(D.nrows(),D.ncols())
    u0=R(1)
    while af<r and R(D[af,af]).is_unit() :
        u0=ZZ(D[af,af])
        u1=xgcd(u0,mu)[1]
        u2=R(u1)
        D[af,af]=u2*D[af,af]
        for j in [0..P.nrows()-1]: P[af,j]=u2*P[af,j]
        af=af+1
    return [D,P,Q]
#
def ValuationOf(u,p,nu):
    """
    Input: `u:=p^j*v` where `v` is a unit
    Output: `j`
    """
    S=parent(u)
    i=0;
    while S((p^i)*u)!=S(0) :
        i=i+1
    return nu-i
#
#
def NormOf(u,p,nu):
    """
    Input: `u:=p^j*v` where v is a unit
    Output: `p^j`
    """
    S=parent(u)
    i=0;
    while S((p^i)*u)!=S(0) :i=i+1;
    return p^(nu-i)
#
def UnitOf(u,p,nu):
    """
    Input: `u:=p^j*v`
    where `v` is a unit in the ring `S= Z_ {p ^nu}[a]`
    Output: `v`
    """
    S=parent(u)
    a=S.gen()
    v=S(1)
    if S(u)==S(0):
        v=1
    else :
        w=ZZ['z'](S(u).lift())//NormOf(u,p,nu)
        v=w(a)
    return S(v)
#
def InvFra(A,p,nu):
    R=A.base_ring()
    L=matrix(ZZ,A)
    D=matrix(R,L.smith_form()[0])
    r=min(D.nrows(),D.ncols())
    ar=0
    while ar<r and R(D[ar,ar])!=R(0):
        ar=ar+1
    T=[ValuationOf(R(D[i,i]),p,nu) for i in [0..ar-1]]
    return T
#    
# V. Vector representation of matrices
#
# V.1. Program
#
def CoefficientOf(u):
    """
    Input:`u` in `S=R[a]`
    Output: the list of coefficent of `u`
    in the basis `(1,a,...,a^(m-1))`
    """
    S=parent(u)
    Rz=S.cover_ring()
    a=S.gen()
    m=S(a).charpoly(Rz.gen()).degree()
    u1=S(u).lift()
    u2=[u1[i] for i in [0..Rz(u1).degree()]]
    u3=[0 for i in [0..m-Rz(u1).degree()-2]]
    return u2+u3
#
def MatrixRepresentationOf(v):
    """
    Input:`v` a list with coefficient in `S=R[a]`
    Output: the matrix representation of `v` in the
    ring `R` relative to the basis `(1,a,...,a^(m-1))`
    """
    S=parent(v[0])
    Rz=S.cover_ring()
    R=Rz.base_ring()
    a=S.gen()
    m=S(a).charpoly(Rz.gen()).degree()
    return matrix(R,len(v),m,[CoefficientOf(v[j]) for j in [0..len(v)-1]]).transpose()
#
def VectorRepresentationOf(V,S):
    """
    Input:`V` a matrix of `m` rows with coefficient in `R`
    Output: the vector representation of `V` in the
    ring `S=R[a]` relative to the basis `(1,a,...,a^(m-1))`
    """
    a=S.gen()
    Rz=S.cover_ring()
    R=Rz.base_ring()
    m=S(a).charpoly(Rz.gen()).degree()
    Bs=matrix(S,1,m,[a^i for i in [0..m-1]])
    V1=matrix(S,V)
    v=Bs*V1
    return [v[0,i] for i in [0..v.ncols()-1]]
#
def RankOf(A):
    R=A.base_ring()
    ar=0
    D=SmithNormalFormOf(A)[0]
    r=min(D.nrows(),D.ncols())
    while ar<r and R(D[ar,ar])!=R(0) :
        ar=ar+1
    return ar
#
def FreeModuleOf(A):
    R=A.base_ring()
    mu=R.order()
    L=matrix(ZZ,A).smith_form()
    D=L[0]
    P=L[1]
    B=matrix(R,P^-1)
    r=min(D.nrows(),D.ncols())
    ar=0
    while ar<r and R(D[ar,ar])!=R(0) :
        ar=ar+1
    return matrix(R,B[:,:ar])
#
#
def GenModuleOf(A):
    R=A.base_ring()
    mu=R.order()
    L=matrix(ZZ,A).smith_form()
    D=L[0]
    P=L[1]
    Q=L[2]
    B=matrix(R,P^-1)
    C=matrix(R,Q^-1)
    ar=0
    D=SmithNormalFormOf(A)[0]
    r=min(D.nrows(),D.ncols())
    while ar<r and R(D[ar,ar])!=R(0) :
        ar=ar+1
    return [matrix(R, B*D[:,:ar]), C[:ar,:]]
#
def ParityCheckMatrixOf5_2(A):
    R=A.base_ring()
    mu=R.order()
    L=matrix(ZZ,A).smith_form()
    D=L[0]
    Q=L[2]
    r=min(D.nrows(),D.ncols())
    af=0
    while af<r and R(D[af,af]).is_unit() :
        af=af+1
    if af==D.ncols():
        return false
    else:
        ar=af
        while ar<r and R(D[ar,ar])!=R(0) :
            ar=ar+1
        B=Q
        n=Q.nrows()
        for j in [af..ar-1]:
            d=D[j,j]
            d1=ZZ(R(d))
            b=R(mu/d1)
            for i in [0..n-1]:
                B[i,j]=b*B[i,j]
        return matrix(R,B[:,af:])
#
def ProductOfModule(a,b):
    c=[]
    for i in [0..len(a)-1]:
        for j in [0..len(b)-1]:
            c=c+[a[i]*b[j]]
    return c
#
def IntersectionOf5_2(a,b):
    S=parent(a[0])
    Rz=S.cover_ring()
    R=Rz.base_ring()
    A=MatrixRepresentationOf(a)
    B=MatrixRepresentationOf(b)
    HA=ParityCheckMatrixOf5_2(matrix(R,A.transpose()))
    HB=ParityCheckMatrixOf5_2(matrix(R,B.transpose()))
    if HA==False or HB==False:
        return False
    else:
         HAB=block_matrix([[HA,HB]])
         HHAB=ParityCheckMatrixOf5_2(matrix(R,HAB.transpose()))
         if  HHAB==False:
             return False
         else:
             return VectorRepresentationOf(HHAB,S)
#
def MultiIntersectionOf5_2(b,u):
    a=ProductOfModule([b[0]],u)
    update=True
    i=1
    while i<len(b) and update==True:
        c=IntersectionOf5_2(a,ProductOfModule([b[i]],u))
        if c==False:
            update=False
        else:
            a=c
            i=i+1
    if update==False:
        return False
    else:
        return a
#
def CoordOf(a,b):
    n=len(b)
    A=MatrixRepresentationOf(a)
    B=MatrixRepresentationOf(b)
    [D,P,Q]=matrix(ZZ,B).smith_form()
    return Q*(P*A)[0:n,:]
    
 #
def MatrixExtensionOf(A,B):
    nr=A.nrows()
    nc=A.ncols()
    return block_matrix(B, [[block_matrix(B,[[MatrixRepresentationOf([A[i,j]]) for j in range(nc)] ])] for i in range(nr)])
#
#
def NormOf(u,p,nu):
    """
    Input: `u:=p^j*v` where v is a unit
    Output: `p^j`
    """
    S=parent(u)
    i=0;
    while S((p^i)*u)!=S(0) :
        i=i+1
    return p^(nu-i)
#
def UnitOf2(u,p,nu):
    """
    Input: `u:=p^j*v`
    where `v` is a unit in the ring `S= Z_ {p ^nu}[a]`
    Output: `v`
    """
    R=parent(u)
    if R(u)==R(0):
        return R(1)
    else:
        v=ZZ(u)//ZZ(NormOf(u,p,nu))
        return R(v)
#
#
def UnitTestOf(u,nu):
    """
    Input: `u:=p^j*v` where `v` is a unit
    Output: `j`
    """
    R=parent(u)
    i=1;
    while R(u)!=R(0) and i<nu+1 :
        i=i+1
        u=R(u*u)
    if R(u)!=R(0):
        return True
    else:
        return False
#
#
def LeftInverseOf1_5(A1,nu):
    R=A1.base_ring()
    ma=A1.nrows()
    na=A1.ncols()
    A=matrix(R,A1)
    P=identity_matrix(R,ma)
    h=0; k=0
    while h<ma and k<na :
        l=h 
        PivotIsUnit=false
        while PivotIsUnit==false and l<ma:
            if UnitTestOf(R(A[l,k]),nu)==true:
                PivotIsUnit=true
            else:
                l=l+1
        A.swap_rows(h,l)
        P.swap_rows(h,l)
        v=A[h,k]^-1
        A[h,k]=R(1)
        for j in [k+1..na-1]:
            A[h,j]=R(v*A[h,j])
        for j in [0..ma-1]:
            P[h,j]=R(v*P[h,j])
        for i in [h+1..ma-1]:
            w=-A[i,k]
            for j in [k+1..na-1]:
                A[i,j]=R(A[i,j]+w*A[h,j])
            for j in [0..ma-1]:
                P[i,j]=R(P[i,j]+w*P[h,j])
            A[i,k]=R(0)
        h=h+1
        k=k+1
    for j in range(na-1,0,-1):
        for i in [0..j-1]:
            w=-A[i,j]
            for k in [0..ma-1]:
                P[i,k]=R(P[i,k]+w*P[j,k])  
    return P
#
    
def SolveLinearEquationOverZpn(A,Y,p,nu):
    R=A.base_ring()
    nr=A.nrows()
    nc=A.ncols()
    r=min(nr,nc)
    [D,P,Q]=matrix(ZZ,A).smith_form()
    ar=0
    while ar<r and R(D[ar,ar])!=R(0):
        ar=ar+1
    Y_1=P*Y
    v_1=[ValuationOf(R(D[i,i]),p,nu) for i in range(ar)]+[nu for i in [ar..nr-1] ]
    v_2=[ValuationOf(R(Y_1[i,0]),p,nu) for i in [0..nr-1]]
    if [v_1[i]<=v_2[i] for i in range(nr)]!=[true for _ in range(nr)]:
        return false
    else:
        Y_2=matrix(R,r,1,[(p^(v_2[i]-v_1[i]))*UnitOf2(Y_1[i,0],p,nu)*UnitOf2(R(D[i,i]),p,nu)^-1 for i in [0..r-1]])
        if nc <=nr:
            Y_3=Q*Y_2[0:nc]
        else:
            Y_3=Q*block_matrix(R,[[Y_2,],[matrix(R,nc-nr,1,[0 for i in range(nc-nr)])]])
        return Y_3
#
#
def CoordOf2(a,b):
    n=len(b)
    A=MatrixRepresentationOf(a)
    B=MatrixRepresentationOf(b)
    [D,P,Q]=matrix(ZZ,B).smith_form()
    return Q*(P*A)[0:n,:]
    
def CoordOverZpn(A,Y,p,nu):
    R=A.base_ring()
    yc=Y.ncols()
    nr=A.nrows()
    nc=A.ncols()
    r=min(nr,nc)
    [D,P,Q]=matrix(ZZ,A).smith_form()
    ar=0
    while ar<r and R(D[ar,ar])!=R(0):
        ar=ar+1
    Y_1=P*Y
    v_1=[ValuationOf(R(D[i,i]),p,nu) for i in range(ar)]+[nu for i in [ar..nr-1] ]
    v_2=[[ValuationOf(R(Y_1[i,j]),p,nu) for i in [0..nr-1]] for j in range(yc)]
    TestOfValu=true
    j1=0
    while TestOfValu==true and j1<yc:
        if [v_1[i]<=v_2[j1][i] for i in range(nr)]!=[true for _ in range(nr)]:
            TestOfValu=false
        else:
            TestOfValu=true
            j1=j1+1
            
    if TestOfValu==false:
        return false
    else:
        Y_2=matrix(R,nr,yc)
        for i in range(r):
            d=UnitOf2(R(D[i,i]),p,nu)^-1
            for j in range(yc):
                Y_2[i,j]=(p^(v_2[j][i]-v_1[i]))*UnitOf2(Y_1[i,j],p,nu)*d
        if nc <=nr:
            Y_3=Q*Y_2[0:nc,:]
        else:
            Y_3=Q*block_matrix(R,[[Y_2],[matrix(R,nc-nr,yc)]])
        return Y_3
#
def RandomMatrixOfRankt(R,m,n,t):
    E_1=random_matrix(R,m,t)
    E_2=random_matrix(R,t,n)
    E=E_1*diagonal_matrix([R.random_element() for i in [0..t-1]])*E_2 
    while RankOf(E)!=t:
        E_1=random_matrix(R,m,t)
        E_2=random_matrix(R,t,n)
        E=E_1*diagonal_matrix([R.random_element() for i in [0..t-1]])*E_2
    return E




p=2    # the characteristic of finite field
m=30 #30   #20 #6 the degree of Galois extension
nu=3
k=16 #8
n=32 #20
v=2
R=Integers(ZZ(p^nu))    # base ring
Rz.<z>=R[]
Conway=Rz(conway_polynomial(p,m))
S.<s>=Rz.quotient(Conway)    # Galois extension of 'GF(P)'
O_1=matrix(S,n-k,1)
#
v_2=v*(v+1)/2
Good_f=True
while Good_f:
    f=[S(1)]+[S.random_element() for _ in range(v-1)]
    ff=ProductOfModule(f,f)
    FF=MatrixRepresentationOf(ff)
    if rank(matrix(GF(p),FF))==v_2:
        Good_f=False
f_1=[InverseOf(f[i]) for i in range(len(f))]
#
Z=Integers(p)
def ListOfH(f):
    L=[]
    for i in [0..(n-k)*n-1]:
        a=[Z.random_element() for _ in range(v)]
        c=sum([S(a[j])*f[j] for j in range(v)])
        L=L+[c]
    return L
Good_H=True
while Good_H:
    H=matrix(S,n-k,n,ListOfH(f))
    if H[:,:n-k].det().charpoly(z)[0].is_unit():
        Hext=block_matrix([[CoordOf(list(H[i]),f)] for i in [0..n-k-1] ])
        if rank(matrix(GF(p),Hext))==n:
            if [rank(matrix(GF(p), MatrixRepresentationOf(list(H[i])))) for i in [0..n-k-1]]==[v for _ in range(n-k)]:
                Hext_1=LeftInverseOf1_5(Hext,nu)
                Good_H=false



def DecodingOf(e):
    sy=H*e.transpose()
    if sy==O_1:
        return False
    else:
        sy_1=list((sy.transpose())[0])
        e_5=MultiIntersectionOf5_2(f_1,sy_1)
        if e_5==False:
            return False
        else:
            E_5=MatrixRepresentationOf(e_5)
            VE_5=FreeModuleOf(E_5)
            ve_5=VectorRepresentationOf(VE_5,S)
            fve_5=ProductOfModule(ve_5,f)
            FVE_5=MatrixRepresentationOf(fve_5)
            SY=MatrixRepresentationOf(sy_1)
            SY_1=CoordOverZpn(FVE_5,SY,p,nu)
            if SY_1==False:
                return False
            else:
                t_1=len(ve_5)
                SY_2=block_matrix([[SY_1[v*j:v*(j+1),i] for j in [0..t_1-1]] for i in [0..n-k-1]])
                E_6=Hext_1*SY_2
                if (n-k)*v!=n and E_6[n:,:]!=matrix(R,(n-k)*v-n, SY_2.ncols()):
                    return False
                else:
                    E_7=E_6[0:n,:]
                    if matrix(S,ve_5)*(E_7.transpose())!=e:
                        return False
                    else:
                        return True


def FailisProbability(N,t):
    N1=0
    for _ in range(N):
        E=RandomMatrixOfRankt(R,m,n,t)
        e=matrix(S,[[s^i for i in [0..m-1]]])*matrix(S,E)
        if DecodingOf(e):
            N1=N1+1
    return RR((N-N1)/N)



time FailisProbability(1,7)
