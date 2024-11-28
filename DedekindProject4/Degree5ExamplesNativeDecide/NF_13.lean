
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible13

-- Number field with label 5.1.15000000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 10*X^3 - 20*X^2 + 45*X + 108 
lemma T_def : T = X^5 - 10*X^3 - 20*X^2 + 45*X + 108 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [108, 45, -20, -10, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/4*a^3 - 1/2*a^2 - 1/4*a, 1/12*a^4 - 1/12*a^2 - 1/6*a] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  12
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![12, 0, 0, 0, 0], ![0, 12, 0, 0, 0], ![0, 0, 12, 0, 0], ![0, -3, -6, 3, 0], ![0, -2, -1, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 2, 4, 0],![0, 0, -1, -2, 3],![-9, -3, 3, 3, 0]], 
![![0, 0, 1, 0, 0],![0, 1, 2, 4, 0],![0, 2, 1, 0, 12],![-27, -10, 9, 9, -6],![0, -6, 0, 6, 9]], 
![![0, 0, 0, 1, 0],![0, 0, -1, -2, 3],![-27, -10, 9, 9, -6],![27, 5, -9, -4, 9],![-18, -3, 3, 0, 0]], 
![![0, 0, 0, 0, 1],![-9, -3, 3, 3, 0],![0, -6, 0, 6, 9],![-18, -3, 3, 0, 0],![-12, -9, 3, 6, 3]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-12]],![[], [], [], [-36], [0, -12]],![[], [], [-36], [36, -9], [-24, 6, -3]],![[], [-12], [0, -12], [-24, 6, -3], [-16, -8, 0, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 2, 4, 0], [0, 0, -1, -2, 3], [-9, -3, 3, 3, 0]], 
 ![[0, 0, 1, 0, 0], [0, 1, 2, 4, 0], [0, 2, 1, 0, 12], [-27, -10, 9, 9, -6], [0, -6, 0, 6, 9]], 
 ![[0, 0, 0, 1, 0], [0, 0, -1, -2, 3], [-27, -10, 9, 9, -6], [27, 5, -9, -4, 9], [-18, -3, 3, 0, 0]], 
 ![[0, 0, 0, 0, 1], [-9, -3, 3, 3, 0], [0, -6, 0, 6, 9], [-18, -3, 3, 0, 0], [-12, -9, 3, 6, 3]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by native_decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by native_decide)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-21, -7, 7, 4, 1]
 g :=  [3, 1]
 h :=  [1, 3, 4, 2, 1]
 a :=  [1]
 b :=  [4, 1, 4, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![14, 3, 7]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [128000000, 96000000, 144000000, -16000000]
 b := [460800000, 51200000, -32000000, -28800000, 3200000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 1], [1, 1, 1, 1, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 1, 1, 0, 1], [0, 1, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [1, 1, 1, 1, 0], [0, 0, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 1, 1, 0, 1],![1, 1, 0, 1, 1],![1, 1, 0, 0, 0],![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![19, 48],![40, 7],![6, 4],![34, 4],![6, 32]]
 c := ![![-80, 14, -52],![-24, -12, 2],![1, -2, 4],![-24, -9, -2],![-42, 12, -33]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 1
 n := 4
 t :=  2
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 2, 1, 0], [0, 0, 2, 1, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 2, 1, 0], [0, 2, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 2, 1, 0], [0, 2, 0, 0, 0], [0, 2, 0, 2, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 2, 1, 0],![0, 1, 2, 2, 0],![0, 1, 1, 0, 0]]
 v := ![![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 2, 1, 0],![0, 1, 2, 2, 0],![0, 1, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![4]
 w_ind := ![0, 1, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 2, 2, 0, 1],![0, 1, 2, 2, 2],![0, 1, 1, 2, 0],![0, 0, 0, 1, 0],![0, 2, 1, 2, 0]]
 w1 := ![1]
 w2 := ![1, 1, 0, 1]
 a := ![![304],![363],![90],![-9],![99]]
 c := ![![-99, 99, -6, -123],![-257, 285, -72, -330],![-150, 154, -42, -165],![-60, 66, -23, -69],![-153, 153, -36, -167]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
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
    