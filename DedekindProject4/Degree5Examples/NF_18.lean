
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible18

-- Number field with label 5.1.25312500.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 30*X^2 - 135*X - 252 
lemma T_def : T = X^5 - 30*X^2 - 135*X - 252 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-252, -135, -30, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/3*a^3, 1/246*a^4 - 3/82*a^3 + 27/82*a^2 - 7/82*a + 9/41] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  246
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![246, 0, 0, 0, 0], ![0, 246, 0, 0, 0], ![0, 0, 246, 0, 0], ![0, 0, 0, 82, 0], ![54, -21, 81, -9, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 3, 0],![-18, 7, -27, 9, 82],![3, 0, 3, 0, -9]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 3, 0],![-54, 21, -81, 27, 246],![84, 45, 10, 0, 0],![-27, 3, -27, 9, 81]], 
![![0, 0, 0, 1, 0],![-18, 7, -27, 9, 82],![84, 45, 10, 0, 0],![0, 28, 15, 10, 0],![27, 12, 1, 0, 3]], 
![![0, 0, 0, 0, 1],![3, 0, 3, 0, -9],![-27, 3, -27, 9, 81],![27, 12, 1, 0, 3],![-12, 0, -9, 3, 27]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-246]],![[], [], [], [-20172], [2214, -246]],![[], [], [-20172], [0, -6724], [-6642, 738, -82]],![[], [-246], [2214, -246], [-6642, 738, -82], [1470, -243, 18, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 3, 0], [-18, 7, -27, 9, 82], [3, 0, 3, 0, -9]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 3, 0], [-54, 21, -81, 27, 246], [84, 45, 10, 0, 0], [-27, 3, -27, 9, 81]], 
 ![[0, 0, 0, 1, 0], [-18, 7, -27, 9, 82], [84, 45, 10, 0, 0], [0, 28, 15, 10, 0], [27, 12, 1, 0, 3]], 
 ![[0, 0, 0, 0, 1], [3, 0, 3, 0, -9], [-27, 3, -27, 9, 81], [27, 12, 1, 0, 3], [-12, 0, -9, 3, 27]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] rfl

instance hp41: Fact $ Nat.Prime 41 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [51, 29, 9, 2, 1]
 g :=  [3, 1]
 h :=  [1, 3, 4, 2, 1]
 a :=  [3]
 b :=  [1, 4, 3, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [41, 2, 3] where
 n := 4
 p := ![2, 3, 5, 41]
 exp := ![4, 8, 7, 2]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp41.out
 a := [-55586250000, 21323250000, -6105375000, 1093500000]
 b := [1640250000, 15053850000, -4264650000, 1221075000, -218700000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M41 : MaximalOrderCertificateOfUnramifiedLists 41 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 3, 0], [23, 7, 14, 9, 0], [3, 0, 3, 0, 32]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 3, 0], [28, 21, 1, 27, 0], [2, 4, 10, 0, 0], [14, 3, 14, 9, 40]], 
![[0, 0, 0, 1, 0], [23, 7, 14, 9, 0], [2, 4, 10, 0, 0], [0, 28, 15, 10, 0], [27, 12, 1, 0, 3]], 
![[0, 0, 0, 0, 1], [3, 0, 3, 0, 32], [14, 3, 14, 9, 40], [27, 12, 1, 0, 3], [29, 0, 32, 3, 27]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![40, 6, 16, 7, 0],![37, 20, 24, 28, 0],![16, 2, 31, 12, 0],![18, 4, 28, 38, 40]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [1, 1, 1, 1, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 1, 1, 1, 1], [1, 0, 1, 0, 1], [0, 0, 1, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 1, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 0, 1],![0, 0, 0, 1, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![0, 1, 1, 0, 0],![1, 0, 1, 1, 1],![0, 0, 1, 1, 1],![0, 1, 1, 0, 1],![1, 0, 1, 0, 0]]
 w1 := ![0, 1]
 w2 := ![1, 0, 0]
 a := ![![135, -96],![118, -69],![118, -70],![170, -122],![96, -68]]
 c := ![![6, 194, -30],![58, 148, 18],![57, 148, 18],![6, 247, -40],![16, 138, -15]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 1], [0, 0, 1, 0, 0], [0, 1, 0, 1, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 2, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 2, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 2]]
 v_ind := ![1, 2, 4]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![2, 0, 2, 0, 4],![0, 1, 0, 0, 0],![2, 0, 2, 1, 1],![0, 0, 0, 0, 1],![0, 0, 2, 0, 0]]
 w1 := ![1, 0, 0]
 w2 := ![1, 1]
 a := ![![830, 162, 48],![45, -161, 492],![789, 198, 94],![72, 9, 12],![540, 126, 0]]
 c := ![![558, 3],![-36, 9],![387, 15],![55, 0],![336, 1]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [41, 2, 3]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 41 O Om hm M41
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [41, 2, 3] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
