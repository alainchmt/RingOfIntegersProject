#!/usr/bin/env python
# coding: utf-8

# In[2]:


## Computes a basis for the ring of integer of a number field such that, 
## when writting the elements as columns on a matrix with respect to the power basis, 
## it is upper triangular. 

## The basis given in the LMFDB is already of this form, so when using this basis this 
## step is not necessary. 

## Input: 
## T : a defining polynomial for the number field. 

## Output: 
## A matrix C with integer entries and a denominator d. The basis matrix is (1/d) * C. 

def BasisUpperTriangular(T): 
    n = T.degree()
    K.<a> = NumberField(T)
    O = K.maximal_order()
    B = O.basis()
    MZ =MatrixSpace(ZZ, n)
    L = [i.list()[:: -1] for i in B]
    M1 = matrix(L[:: -1])
    d = 1
    for i in range(n):
        for j in range(n):
            d = lcm(d, denominator(M1[i,j]))
    M = MZ(d * matrix(L[:: -1])).echelon_form()
    C = (M[::-1, ::-1]).transpose()
    return C , d


# In[3]:


# Express a basis as a matrix and common denominator. 

# Input: a basis B given as a list, with the elements written as polynomials over a root of T.

# Output: a matrix C with integer entries and and integer d. 

# Writting the basis B as columns of a matrix gives (1/d) * C.  

def BasisToMatrix(B): 
    n = len(B)
    d = 1
    L = [i.list() + (n - len(i.list())) * [0] for i in B]
    M = matrix(L).transpose()
    for i in range(n):
        for j in range(n):
            d = lcm(d, denominator(M[i,j]))
    return d * M, d    


# ## Subalgebra Builder

# In[4]:


# Builds a term of type SubalgebraBuilderLists which is used to construct the subalgebra with a given basis
# in Lean. The basis, as a matrix, is B = (1/d) * C

# Input : 
# T : a polynomial 
# C : the matrix with coefficients of a basis 
# d : the common denominator 
# f : the files where the Lean code will be written 

#Output: 
# A : the times table of the subalgebra 
# v : a vector such that B * v = (0,1,0,...,0)

def SubalgebraBuilderF(T, C, d, f):
    n = T.degree()
    K.<a> = NumberField(T)
    S.<X>=PolynomialRing(ZZ)
    #Columns of this matrix are basis for Ok in terms of 1, a^2, ..., a^n. It is upper triangular. 
    MM = (1/d) * C
    MMinv = MM.inverse()
    A = [[[] for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            A[i][j] = (MMinv * matrix ([(K(MM.column(i))*K(MM.column(j))).list()]).transpose()).transpose().list()

    s = [[- S(C.column(i).list())*S(C.column(j).list()) // T for j in range(n)] for i in range(n)] 
    B = [S(C.column(i).list()) for i in range(n)]
    c = [[C[i,j] for j in range(n)] for i in range(n)]

    s = [[s[i][j].list() for j in range(n)] for i in range(n)]
    

    print('noncomputable def BQ : SubalgebraBuilderLists',n,'ℤ', ' ℚ K T l where', file = f)
    print(' d := ', d, file = f)
    print(' hlen := rfl', file = f)
    print(' htr := rfl', file = f)
    print(' hofL := T_ofList.symm', file = f)
    print(' hm := rfl', file = f)
    print(' B := ![', end="", file = f)
    for item in ['!' + str(B[i].list() + [0] * (n - len(B[i].list()))) for i in range(n-1)]:
        print(item, end=", ", file = f)
    print('!' + str(B[n-1].list() + [0] * (n - len(B[n-1].list()))) + ']', file = f)

    print(' a := ![', end = "", file = f)
    stra = " "
    for i in range(n):
        stra = stra + '!['
        for j in range(n):
            if j != n - 1:
                stra = stra + '!' + str(A[i][j]) + ','
            else : 
                stra = stra + '!' + str(A[i][j])
        if i != n - 1:
            stra = stra + '], \n'
        else :
            stra = stra + ']'
    stra = stra + "]"
    print(stra, file = f)

    strs =""
    print(' s := ![',end="", file = f)
    for i in range(n):
        if i != n - 1:
            strs = strs + '!' + str(s[i]) + ','
        else :
            strs = strs + '!' + str(s[i])
    strs = strs + "]"
    print(strs, file = f)
    print(""" h := Adj
 honed := rfl
 hd := by norm_num
 hcc := by decide 
 hin := by decide
 hsymma := by decide
 hc_le := by decide """, file = f)
    return A , C.inverse() * (d * vector([0 if i != 1 else 1 for i in range(n)]))


# ## Certificate Dedekind at p

# In[12]:


# If T satisfies Dedekind criterion at p, it writes the Lean certificate. 

# Input: 
# T : a polynomial 
# p : a prime 
# fi : the file where the Lean code will be written. 

def CertificateDedekindCriterionF (T , p, fi):
    S.<X>=PolynomialRing(ZZ)
    R.<x>=PolynomialRing(GF(p))
    g = radical(R(T))
    F = R(T).factor()
    kl = len(F)
    n = max ([F[i][1] for i in range(kl)])
    t ,ap, bp = xgcd(g,derivative(g))
    k = R((g ^ n)/R(T))
    h = S(R(R(T)/g))
    f = (S(g) * h - T)/p
    gcd, at , bt = xgcd(R(f), g)
    gcd2, at2, c = xgcd(gcd, R(h))
    a = at2 * at
    b = at2 * bt 
    c = c

    if gcd2 == 1:
        print("def CD" + str(p) + ": CertificateDedekindCriterionLists l",p, "where", file = fi)
        print(' n := ', n, file = fi)
        print(' a\' :=', ap.list(), file = fi)
        print(' b\' := ', bp.list() , file = fi)
        print(' k :=', k.list(), file = fi)
        print(' f :=', f.list(), file = fi)
        print(' g := ', g.list(), file = fi)
        print(' h := ', h.list(), file = fi)
        print(' a := ', a.list(), file = fi)
        print(' b := ', b.list(), file = fi)
        print(' c := ', c.list(), file = fi)
        print(' hdvdpow := rfl', file = fi)
        print(' hcop := rfl', file = fi)
        print(' hf := by rfl', file =fi)
        print(' habc := by rfl \n', file = fi)
        return True


# ## Certificate Dedekind at almost all primes

# In[6]:


# It writes a Lean certificate proving that T satisfies Dedekind criterion at all primes except the ones 
# in the list 'bad'. 

# Input: 
# T : a polynomial (must be separable)
# f : the files ehere the Lean code will be written. 


def CertificateDedekindF(T, f):
    D, a, b = xgcd (T, derivative(T))
    if D < 0 :
        a = -a
        b = -b
    F = factor(D)
    n = len(F)
    pl = [t[0] for t in F]
    exp = [t[1] for t in F]
    
    for p in set(pl):
        print(f'instance hp{p}: Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)', file = f)
    print('', file = f)

    good = []

    for p in pl: 
        if CertificateDedekindCriterionF (T, p, f):
            good = good + [p]

    bad = list (set(pl)-set(good))

    print('noncomputable def D : CertificateDedekindAlmostAllLists T l',bad,'where', file = f)
    print(' n := '+ str(len(pl)), file = f)
    print(' p :=' + " !"+ str(pl), file = f)
    print(' exp :=' + " !"+ str(exp), file = f)
    print(' pdgood :=',good, file = f)
    print(' hsub := by decide', file = f)
    print(""" hp := by
  intro i ; fin_cases i """, file = f)
    for p in pl:
        print(f'  exact hp{p}.out', file = f)
    print(' a :=', a.list(), file = f)
    print(' b :=', b.list(), file = f)
    print(' hab := by decide', file = f)
    print(""" hd := by 
  intro p hp 
  fin_cases hp """, file = f)
    for p in good:
        print('  exact satisfiesDedekindCriterion_of_certificate_lists T l', p,'T_ofList CD' + str(p), file = f)
    print('', file = f)
    return(bad)


# ## Certificate p-maximality

# In[7]:


def CertificatePMaximalityF (T , C, denom , p, Table, F):
    d=T.degree()
    t = 0
    while p ^ t < d : 
        t = t + 1
    K.<a> = NumberField(T)
    O = K.maximal_order()

    #Columns of this matrix are basis for Ok in terms of 1, a^2, ..., a^n. It is upper triangular. 
    M = (1/denom) * C
    #print(M)
    B = [K(M.column(i).list()) for i in range(d)]

    MFrob = matrix([(i^(p^t)).list() for i in B]).transpose()
    Coeff = M.inverse() * MFrob
    MS=MatrixSpace(GF(p),d)
    CoeffMod = MS(Coeff)
    #print(CoeffMod)

    m = CoeffMod.right_nullity()
    n = d - m

    v = CoeffMod.right_kernel().matrix().rows()
    v_ind = CoeffMod.right_kernel().matrix().pivots()
    w_ind = CoeffMod.transpose().echelon_form().pivots()
    X = CoeffMod.solve_right (CoeffMod.transpose().echelon_form().transpose())
    wFrob = [CoeffMod.transpose().echelon_form().transpose().column(i) for i in range(n)]
    w = [X.column(i) for i in range(n)]
    
    flag = 0 
    flagW = 0
    
    if m == 0 :
        # This is the case for p unramified
        flag = 1
        print('noncomputable def M'+ str(p) +' : MaximalOrderCertificateOfUnramifiedLists ' + str(p) + ' O Om hm where', file = f)
        print (' n := ' + str(n), file = f)
        print (' t := ', t, file = f)
        print(' hpos := by decide', file = f)
        print(f" TT := timesTableO", file = f)
        print(' B\' := B\'', file = f)
        print(' T := Table', file = f)
        print(' heq := timesTableT_eq_Table', file = f)
        strT = ""
        print(' TMod := ![', end = "", file = f)
        for i in range(d):
            if i != d -1 :
                strT = strT + '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)]) + ', \n'
            else : 
                strT = strT + '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)])
        print(strT + ']', file = f)
        #print(strT)
        print(' hTMod := by decide', file = f)
        print(' hle := by decide', file = f)
        strw = ""
        for i in range(n):
            if i != n -1 :
                strw = strw + '!' + str(w[i].list()) + ','
            else : 
                strw = strw + '!' + str(w[i].list())
        print(' w := ![' + strw + ']', file = f)

        strF = ""
        print(' wFrob := ![', end = "", file = f)
        for i in range(n):
            if i != n -1 :
                strF = strF + '!' + str(wFrob[i].list()) + ','
            else : 
                strF = strF + '!' + str(wFrob[i].list())
        print(strF + ']', file = f)
        print (' w_ind := !' + str([w_ind[i] for i in range(n)]), file = f)
        print(""" hindw := by decide
 hwFrobComp := by intro i ; fin_cases i <;> rfl """, file = f)
    else : 
        MQQ=MatrixSpace(ZZ, d)
        MQ1=MatrixSpace(ZZ, m, d)
        MQ2=MatrixSpace(ZZ, n , d)
        if m > 0 : 
            Brad = MQ1(matrix(v)).transpose().augment(p * MQ2(matrix(w)).transpose())
        else:
            Brad = p * MQ2(matrix(w)).transpose()
        Brad2 = M * Brad

        ListBasisRad = [K(Brad2.column(i)) for i in range(d)]
                
        # Matrix for the endomorphism Ip/pIp -> Ip/pIp given my multiplication by B[i]
        def MatrixEndoMul (j) :
            return (MS (Brad2.inverse() * matrix([(B[j]*ListBasisRad[i]).list() for i in range(d)]).transpose()))

        # We look for a witness for linear independence
        
        for i in range(100):
            W = random_vector(ZZ, d, floor(d/2))
            LII = matrix([(MatrixEndoMul(i) * W).list() for i in range(d)]).transpose()
            if LII.is_singular() == False : 
                flagW = 1
                break 
        if flagW == 1 : 
            LII = matrix([(MatrixEndoMul(i) * W).list() for i in range(d)]).transpose()
            # The witness as an element in the number field
            Wit = K((Brad2 * W).list())
            G = LII.inverse()
            
            # Represents elements in O in terms of the basis v_1, ..., v_m, w_1, ..., w_n
            g = [[ZZ(G[i][j]) for i in range(d)] for j in range(d)]
            
            #Expresses g_i * W in terms of the basis I_p/pI_p
            def Endo(j) :
                return Brad2.inverse() * vector(((K((M * matrix(g[j]).transpose()).list())) * Wit).list())

            # We clear denominators in g 
            # Note that denominators with a factor of p will never appear
            for j in range(d):
                denom = LCM([(Endo(j)[k]).denominator() for k in range(d)])
                g[j] = [denom * g[j][i] for i in range(d)]

            # These are the coefficients of g_i * W (with updated g's).
            def a_aux (i) :
                return [Endo(i)[k] for k in range(m)]
            def c_aux (i) :
                return [Endo(i)[m + k] for k in range(n)] 

            a = [a_aux (i) for i in range(d)] 
            c = [c_aux (i) for i in range(d)]
            
            def ac_ind_aux (i) : 
                if i < m : 
                    return 'Sum.inl ' + str(i)
                else : 
                    return 'Sum.inr ' + str(i - m)
                  
        else : 
            # If we couldn't find a witness, we certify the linear independence of the endomorphisms 
            # by finding full expressions for the corresponding matrices. 

            # Write the endomorphisms as a matrix d x d ^ 2
            MM = matrix ([(MatrixEndoMul (j)).list() for j in range(d)])

            ab_aux = MM.echelon_form().pivots()
            gm = MQQ((MM.transpose().solve_right (MM.echelon_form().transpose()))).columns()
            
            # Represents elements in O in terms of the basis v_1, ..., v_m, w_1, ..., w_n
            g = [[gm[j][i] for i in range(d)] for j in range(d)]
            
            # The endomorphism varphi(g_i) as a matrix with respect to the basis for I_p/pI_p
            def Endo(j) :
                return Brad2.inverse() * (matrix([((K((M * matrix(g[j]).transpose()).list())) * ListBasisRad[i]).list() for i in range(d)]).transpose())

            # We clear denominators 
            for j in range(d):
                denom = LCM([LCM([(Endo(j)[i][k]).denominator() for k in range(d)]) for i in range(d)])
                g[j] = [denom * g[j][i] for i in range(d)]

            def a_aux (i, j) :
                return [Endo(i).column(j)[k] for k in range(m)]
            def c_aux (i, j) :
                return [Endo(i).column(j)[m + k] for k in range(n)] 

            a = [[a_aux (i ,j) for j in range(m)] for i in range(d)]
            c = [[c_aux (i ,j) for j in range(m)] for i in range(d)]
            dl = [[a_aux (i ,m + j) for j in range(n)] for i in range(d)]
            e = [[c_aux (i ,m + j) for j in range(n)] for i in range(d)]

            def index_adjust (i, m, n) :
                d = m + n
                r = i % d
                s = floor(i/d)
                if r < m :
                    col = 'Sum.inl ' + str(r)
                else:
                    col = 'Sum.inr ' + str(r - m)

                if s < m: 
                    row = 'Sum.inl ' + str(s)
                else: 
                    row = 'Sum.inr ' + str(s - m)
                return (col, row)

            ab_ind = [index_adjust(i, m ,n) for i in ab_aux]
        if flagW == 1:
            print('noncomputable def M'+ str(p) +' : MaximalOrderCertificateWLists ' + str(p) + ' O Om hm where', file = f)
        else : 
            print('noncomputable def M'+ str(p) +' : MaximalOrderCertificateLists ' + str(p) + ' O Om hm where', file = f)
        print (' m := ' + str(m), file = f)
        print (' n := ' + str(n), file = f)
        print (' t := ', t, file = f)
        print(' hpos := by decide', file = f)
        print(f" TT := timesTableO", file = f)
        print(' B\' := B\'', file = f)
        print(' T := Table', file = f)
        print(' heq := timesTableT_eq_Table', file = f)
        strT = ""
        print(' TMod := ![', end = "", file = f)
        for i in range(d):
            if i != d -1 :
                strT = strT + '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)]) + ', \n'
            else : 
                strT = strT + '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)])
        print(strT + ']', file = f)
        #print(strT)
        print(' hTMod := by decide', file = f)
        print(' hle := by decide', file = f)
        strv = ""
        print(' b1 := ![', end = "", file = f)
        for i in range(m):
            if i != m -1 :
                strv = strv + '!' + str(v[i].list()) + ','
            else : 
                strv = strv + '!' + str(v[i].list())
        print(strv + ']', file = f)
        strw = ""
        print(' b2 := ![', end = "", file = f)
        for i in range(n):
            if i != n -1 :
                strw = strw + '!' + str(w[i].list()) + ','
            else : 
                strw = strw + '!' + str(w[i].list())
        print(strw + ']', file = f)

        print(' v := ![' + strv + ']', file = f)
        print(' w := ![' + strw + ']', file = f)

        strF = ""
        print(' wFrob := ![', end = "", file = f)
        for i in range(n):
            if i != n -1 :
                strF = strF + '!' + str(wFrob[i].list()) + ','
            else : 
                strF = strF + '!' + str(wFrob[i].list())
        print(strF + ']', file = f)

        print (' v_ind := !' + str([v_ind[i] for i in range(m)]), file = f)
        print (' w_ind := !' + str([w_ind[i] for i in range(n)]), file = f)
        print(""" hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl """, file = f)
        strg = ""
        print(' g := ![', end = "", file = f)
        for i in range(d):
            if i != d -1 :
                strg = strg + '!' + str(g[i]) + ','
            else : 
                strg = strg + '!' + str(g[i])
        print(strg + ']', file = f)

        if flagW == 1:
            print (' w1 := !' + str([W[i] for i in range(m)]), file = f)
            print (' w2 := !' + str([W[m + i] for i in range(n)]), file = f)
            stra = ""
            print(' a := ![', end = "", file = f)
            for i in range(d):
                if i != d -1 :
                    stra = stra + '!' + str(a[i]) + ','
                else : 
                    stra = stra + '!' + str(a[i])
            print(stra + ']', file = f)
            strc = ""
            print(' c := ![', end = "", file = f)
            for i in range(d):
                if i != d -1 :
                    strc = strc + '!' + str(c[i]) + ','
                else : 
                    strc = strc + '!' + str(c[i])
            print(strc + ']', file = f)
            print (' hmulw := by decide ', file = f)
            strac_indw = ""
            print(' ac_indw := ![', end = "", file = f)
            for i in range(d):
                if i != d -1 :
                    strac_indw = strac_indw + ac_ind_aux(i) + ', '
                else : 
                    strac_indw = strac_indw + ac_ind_aux(i)
            print(strac_indw + ']', file = f)
            print(' hacindw := by decide ', file = f)
            print("", file = f)
        else : 
            stra = ""
            for i in range(d):
                stra = stra + '!['
                for j in range(m):
                    if j != m - 1:
                        stra = stra + '!' + str(a[i][j]) + ','
                    else : 
                        stra = stra + '!' + str(a[i][j])
                if i != d - 1:
                    stra = stra + '],'
                else :
                    stra = stra + ']'
            print(' a := ![' + stra + ']', file = f)

            strc = ""
            for i in range(d):
                strc = strc + '!['
                for j in range(m):
                    if j != m - 1:
                        strc = strc + '!' + str(c[i][j]) + ','
                    else : 
                        strc = strc + '!' + str(c[i][j])
                if i != d - 1:
                    strc = strc + '],'
                else :
                    strc = strc + ']'
            print(' c := ![' + strc + ']', file = f)

            strd = ""
            for i in range(d):
                strd = strd + '!['
                for j in range(n):
                    if j != n - 1:
                        strd = strd + '!' + str(dl[i][j]) + ','
                    else : 
                        strd = strd + '!' + str(dl[i][j])
                if i != d - 1:
                    strd = strd + '],'
                else :
                    strd = strd + ']'
            print(' d := ![' + strd + ']', file = f)


            stre = ""
            for i in range(d):
                stre = stre + '!['
                for j in range(n):
                    if j != n - 1:
                        stre = stre + '!' + str(e[i][j]) + ','
                    else : 
                        stre = stre + '!' + str(e[i][j])
                if i != d - 1:
                    stre = stre + '],'
                else :
                    stre = stre + ']'
            print(' e := ![' + stre + ']', file = f)

            strind = ""
            for i in range(d):
                if i != d - 1: 
                    strind = strind + '(' + ab_ind[i][0] + ', ' + ab_ind[i][1] + '),'
                else : 
                    strind = strind + '(' + ab_ind[i][0] + ', ' + ab_ind[i][1] + ')'
            print(' ab_ind := ![' + strind + ']', file = f)

            print(""" hindab := by decide
 hmul1 := by decide
 hmul2 := by decide
            """, file = f)
    return flag , flagW


# In[8]:


# Writes a Lean proof for the ring of integers of a number field, given an integral basis. 

# Input: 
# T : a monic irreducible polynomial defining the number field
# basis : an integral basis for the ring of integers of K, written as a list of polynomials (over a root of T)
# f : the file where the Lean code will be written. 
# nameIrr : the name of the file which contains a proof irreducible_T proving the irreducibility of T
# comment : comment in the beginning of the file 

def LeanProof(T, basis, f, nameIrr, comment):
    d = T.degree()
    C , denom = BasisToMatrix(basis)
    print(f"""
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.{nameIrr}

{comment}

open Polynomial

noncomputable def T : ℤ[X] := {T} 
lemma T_def : T = {T} := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => {T.list()}

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
""", file = f)
    print(f"-- We build the subalgebra with integral basis {basis} ", file = f)
    print("", file = f)
    Table, auxTemp = SubalgebraBuilderF(T, C, denom, f)

    print(f"""
lemma T_degree : T.natDegree = {T.degree()} := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B : Basis (Fin {T.degree()}) ℤ O := basisOfBuilderLists T l BQ
noncomputable def B' : Basis (Fin {T.degree()}) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin {T.degree()}) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ """, file = f)

    strTa = ""
    print(f'def Table : Fin {T.degree()} → Fin {T.degree()} → List ℤ := \n ![', end = "", file = f)
    for i in range(d):
        if i != d -1 :
            strTa = strTa + ' !' + str(Table[i]) + ', \n'
        else : 
            strTa = strTa + ' !' + str(Table[i]) 
    print(strTa + ']', file = f)

    print(f"""
lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ !{auxTemp.list()} [] rfl
""", file=f)

    bad = CertificateDedekindF(T, f)
    flagl = []
    flaglW = []
    for p in bad:
        flagp , flagW = CertificatePMaximalityF(T, C, denom, p, Table, f)
        flagl = flagl + [(p, flagp)] 
        flaglW = flaglW + [(p, flagW)]
    flagl = dict(flagl)
    flaglW = dict(flaglW)
    print("", file = f)
    print(f""" instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible """, file = f)
    print(f"""
theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ {bad}
  · fin_cases hc""", file = f)
    for p in bad:
        if flagl[p] == 0:
            if flaglW[p] == 1:
                print(f'    exact pMaximal_of_MaximalOrderCertificateWLists {p} O Om hm M{p}', file = f)
            else : 
                print(f'    exact pMaximal_of_MaximalOrderCertificateLists {p} O Om hm M{p}', file = f)
        else : 
            print(f'    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists {p} O Om hm M{p}', file = f)
    print(f"""  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList {bad} D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']
""", file = f)
    print("", file = f)
    print(f"""theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    """, file = f)
    f.close()


# In[18]:


#EXAMPLE 

#load('IrreducibilityLeanProofWriter.sage')
#R.<X>= PolynomialRing(ZZ)
#K.<a>= PolynomialRing(QQ)
#B = 1, a, 1/2*a^2, 1/4*a^3, 1/112*a^4 + 5/56*a^3 - 3/28*a^2 - 1/4*a - 5/14
#T = X^5 - 20*X^2 + 240*X - 48
#f = open(f"Example0.lean", "w")
#doc = open(f"IrreducibleExample0.lean", "w")
#LeanProof(T,B,f,'IrreducibleExample0', '--Label 5.1.227812500.1 in the LMFDB')
#LeanProofIrreducible(T, doc)

