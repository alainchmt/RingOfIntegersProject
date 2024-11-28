
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible100

-- Number field with label 5.3.1822500000.3 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 45*X^3 - 10*X^2 + 150*X + 228 
lemma T_def : T = X^5 - 45*X^3 - 10*X^2 + 150*X + 228 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [228, 150, -10, -45, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/6*a^3 - 1/6*a^2, 1/72*a^4 - 5/72*a^3 - 5/18*a^2 + 1/4*a - 1/6] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  72
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![72, 0, 0, 0, 0], ![0, 72, 0, 0, 0], ![0, 0, 72, 0, 0], ![0, 0, -12, 12, 0], ![-12, 18, -20, -5, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 1, 6, 0],![2, -3, 4, 4, 12],![-4, -1, -1, 0, -5]], 
![![0, 0, 1, 0, 0],![0, 0, 1, 6, 0],![12, -18, 25, 30, 72],![-40, -22, 5, 40, -12],![20, 1, 3, -6, 25]], 
![![0, 0, 0, 1, 0],![2, -3, 4, 4, 12],![-40, -22, 5, 40, -12],![28, -21, 25, 25, 92],![-22, 2, -8, 0, -37]], 
![![0, 0, 0, 0, 1],![-4, -1, -1, 0, -5],![20, 1, 3, -6, 25],![-22, 2, -8, 0, -37],![12, 0, 4, -2, 18]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-72]],![[], [], [], [-864], [360, -72]],![[], [], [-864], [288, -144], [-360, 72, -12]],![[], [-72], [360, -72], [-360, 72, -12], [204, -30, 10, -1]]]
 h := Adj
 honed := by native_decide
 hd := by norm_num
 hcc := by native_decide 
 hin := by native_decide
 hsymma := by native_decide
 hc_le := by native_decide 

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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 6, 0], [2, -3, 4, 4, 12], [-4, -1, -1, 0, -5]], 
 ![[0, 0, 1, 0, 0], [0, 0, 1, 6, 0], [12, -18, 25, 30, 72], [-40, -22, 5, 40, -12], [20, 1, 3, -6, 25]], 
 ![[0, 0, 0, 1, 0], [2, -3, 4, 4, 12], [-40, -22, 5, 40, -12], [28, -21, 25, 25, 92], [-22, 2, -8, 0, -37]], 
 ![[0, 0, 0, 0, 1], [-4, -1, -1, 0, -5], [20, 1, 3, -6, 25], [-22, 2, -8, 0, -37], [12, 0, 4, -2, 18]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-45, -28, 5, 11, 1]
 g :=  [3, 1]
 h :=  [1, 3, 4, 2, 1]
 a :=  [2]
 b :=  [2, 3, 4, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![13, 12, 7]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [2121390000000, -1022058000000, -88209000000, 38637000000]
 b := [-957031200000, -695466000000, 343504800000, 17641800000, -7727400000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t :=  3
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 0, 1, 0, 0]]
 v_ind := ![1, 4]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 0, 1, 0, 0],![1, 1, 1, 0, 0],![1, 1, 1, 1, 1],![0, 1, 1, 0, 0],![0, 1, 1, 0, 1]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![15, 2],![24, 21],![60, 126],![24, 20],![10, -46]]
 c := ![![-30, 44, -72],![-30, 48, -84],![-31, 76, -152],![-30, 47, -84],![-50, 46, -75]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t :=  2
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [2, 0, 1, 1, 0], [2, 2, 2, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [2, 2, 2, 1, 0], [2, 1, 0, 0, 1]], 
![[0, 0, 0, 1, 0], [2, 0, 1, 1, 0], [2, 2, 2, 1, 0], [1, 0, 1, 1, 2], [2, 2, 1, 0, 2]], 
![[0, 0, 0, 0, 1], [2, 2, 2, 0, 1], [2, 1, 0, 0, 1], [2, 2, 1, 0, 2], [0, 0, 1, 1, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 1, 1],![0, 1, 0, 2, 1],![0, 0, 1, 2, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 1, 1],![0, 1, 0, 2, 1],![0, 0, 1, 2, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1, 2]
 w_ind := ![0, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 1, 1, 0, 2],![0, 1, 2, 1, 0],![1, 0, 2, 1, 0],![0, 1, 0, 2, 1],![0, 2, 2, 2, 1]]
 w1 := ![1, 1, 0]
 w2 := ![1, 0]
 a := ![![-341, 228, 3],![213, -71, 126],![174, -45, 115],![582, -324, 120],![450, -201, 183]]
 c := ![![57, -96],![-111, -42],![-96, -48],![-182, 66],![-192, -20]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by native_decide 


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
    
