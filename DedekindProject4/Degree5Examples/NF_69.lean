
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible69

-- Number field with label 5.1.632812500.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 50*X^2 - 225*X - 270 
lemma T_def : T = X^5 - 50*X^2 - 225*X - 270 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-270, -225, -50, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 + 1/4*a - 1/2, 1/24*a^4 - 1/8*a^3 - 1/8*a^2 + 7/24*a + 1/4] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  24
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![24, 0, 0, 0, 0], ![0, 24, 0, 0, 0], ![0, -12, 12, 0, 0], ![-12, 6, 0, 6, 0], ![6, 7, -3, -3, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 1, 2, 0, 0],![1, -1, -1, 2, 0],![0, -2, 2, 3, 6],![11, 13, 4, -2, -3]], 
![![0, 0, 1, 0, 0],![1, -1, -1, 2, 0],![-1, -1, 2, 1, 6],![34, 35, 11, -1, -3],![-20, -14, 1, 5, 0]], 
![![0, 0, 0, 1, 0],![0, -2, 2, 3, 6],![34, 35, 11, -1, -3],![6, 27, 29, 13, 3],![-4, -23, -7, 10, 13]], 
![![0, 0, 0, 0, 1],![11, 13, 4, -2, -3],![-20, -14, 1, 5, 0],![-4, -23, -7, 10, 13],![35, 42, 10, -9, -4]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-24]],![[], [], [], [-72], [48, -12]],![[], [], [-72], [0, -36], [12, 18, -6]],![[], [-24], [48, -12], [12, 18, -6], [-82, -3, 6, -1]]]
 h := Adj
 honed := rfl
 hd := by norm_num
 hcc := by decide 
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B : Basis (Fin 5) ℤ O := basisOfBuilderLists T l BQ
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ 
def Table : Fin 5 → Fin 5 → List ℤ := 
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [1, -1, -1, 2, 0], [0, -2, 2, 3, 6], [11, 13, 4, -2, -3]], 
 ![[0, 0, 1, 0, 0], [1, -1, -1, 2, 0], [-1, -1, 2, 1, 6], [34, 35, 11, -1, -3], [-20, -14, 1, 5, 0]], 
 ![[0, 0, 0, 1, 0], [0, -2, 2, 3, 6], [34, 35, 11, -1, -3], [6, 27, 29, 13, 3], [-4, -23, -7, 10, 13]], 
 ![[0, 0, 0, 0, 1], [11, 13, 4, -2, -3], [-20, -14, 1, 5, 0], [-4, -23, -7, 10, 13], [35, 42, 10, -9, -4]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] rfl

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [54, 45, 10]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [4]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![14, 6, 9]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-288900000000, 48600000000, -24300000000, 10800000000]
 b := [243000000000, 122580000000, -9720000000, 4860000000, -2160000000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t :=  3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 1, 0, 0], [0, 0, 0, 1, 0], [1, 1, 0, 0, 1]], 
![[0, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 1, 1], [0, 0, 1, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 1]], 
![[0, 0, 0, 0, 1], [1, 1, 0, 0, 1], [0, 0, 1, 1, 0], [0, 1, 1, 0, 1], [1, 0, 0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 1, 0, 0]]
 v := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 1, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![1, 0, 0, 1, 0],![1, 0, 0, 0, 1],![1, 1, 0, 1, 0],![0, 0, 0, 1, 0],![0, 1, 1, 0, 1]]
 w1 := ![1, 0]
 w2 := ![0, 1, 0]
 a := ![![31, -2],![-2, 7],![32, 0],![30, -2],![6, -2]]
 c := ![![-28, 2, 14],![26, 20, 2],![-27, 8, 18],![-28, 1, 14],![20, 40, 17]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t :=  2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [1, 2, 2, 2, 0], [0, 1, 2, 0, 0], [2, 1, 1, 1, 0]], 
![[0, 0, 1, 0, 0], [1, 2, 2, 2, 0], [2, 2, 2, 1, 0], [1, 2, 2, 2, 0], [1, 1, 1, 2, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 2, 0, 0], [1, 2, 2, 2, 0], [0, 0, 2, 1, 0], [2, 1, 2, 1, 1]], 
![[0, 0, 0, 0, 1], [2, 1, 1, 1, 0], [1, 1, 1, 2, 0], [2, 1, 2, 1, 1], [2, 0, 1, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 1, 0, 2],![0, 1, 1, 0, 0],![0, 0, 0, 1, 2]]
 b2 := ![![1, 0, 0, 0, 0],![2, 2, 0, 0, 0]]
 v := ![![1, 0, 1, 0, 2],![0, 1, 1, 0, 0],![0, 0, 0, 1, 2]]
 w := ![![1, 0, 0, 0, 0],![2, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0]]
 v_ind := ![0, 1, 3]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![4, 4, 0, 4, 2],![8, 4, 4, 4, 0],![2, 1, 0, 1, 2],![2, 0, 2, 0, 1],![0, 2, 2, 1, 2]]
 w1 := ![1, 0, 1]
 w2 := ![0, 0]
 a := ![![-64, 252, 162],![-174, 370, 288],![15, 84, 10],![-15, 87, 21],![-24, 174, 45]]
 c := ![![162, 15],![216, -63],![30, 33],![13, 0],![54, 19]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
