
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible63

-- Number field with label 5.1.421875000.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 75*X - 180 
lemma T_def : T = X^5 + 75*X - 180 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-180, 75, 0, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/48*a^4 - 3/16*a^3 - 5/16*a^2 - 3/16*a + 1/4] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  48
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![48, 0, 0, 0, 0], ![0, 48, 0, 0, 0], ![0, 0, 48, 0, 0], ![0, -24, 0, 24, 0], ![12, -9, -15, -9, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-6, 9, 7, 9, 24],![6, -5, -3, -4, -9]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-12, 18, 15, 18, 48],![90, -38, 0, -1, 0],![-30, 12, -6, -6, -15]], 
![![0, 0, 0, 1, 0],![-6, 9, 7, 9, 24],![90, -38, 0, -1, 0],![6, 36, -26, -9, -24],![-30, -5, 9, -1, 0]], 
![![0, 0, 0, 0, 1],![6, -5, -3, -4, -9],![-30, 12, -6, -6, -15],![-30, -5, 9, -1, 0],![18, -1, -1, 4, 7]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-48]],![[], [], [], [-1152], [432, -48]],![[], [], [-1152], [0, -576], [384, 216, -24]],![[], [-48], [432, -48], [384, 216, -24], [-252, -51, 18, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-6, 9, 7, 9, 24], [6, -5, -3, -4, -9]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-12, 18, 15, 18, 48], [90, -38, 0, -1, 0], [-30, 12, -6, -6, -15]], 
 ![[0, 0, 0, 1, 0], [-6, 9, 7, 9, 24], [90, -38, 0, -1, 0], [6, 36, -26, -9, -24], [-30, -5, 9, -1, 0]], 
 ![[0, 0, 0, 0, 1], [6, -5, -3, -4, -9], [-30, 12, -6, -6, -15], [-30, -5, 9, -1, 0], [18, -1, -1, 4, 7]]]

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
 f := [36, -15]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [1]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![13, 5, 9]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-18225000000, -6075000000, -2025000000, -675000000]
 b := [8100000000, 3645000000, 1215000000, 405000000, 135000000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 1
 n := 4
 t :=  3
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![1]
 w_ind := ![0, 1, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 1, 1, 1, 0],![1, 1, 1, 1, 0],![0, 1, 0, 0, 1],![0, 1, 0, 1, 0],![0, 1, 1, 0, 0]]
 w1 := ![1]
 w2 := ![1, 0, 0, 0]
 a := ![![25],![26],![-8],![8],![18]]
 c := ![![36, 36, -52, 16],![37, 36, -52, 16],![-12, -11, 20, -4],![42, 12, -29, 6],![-6, 24, -22, 11]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 0, 0, 0], [0, 1, 0, 2, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 2, 0], [0, 0, 0, 0, 0], [0, 1, 0, 2, 0], [0, 2, 2, 1, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 2]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 2, 2]]
 v_ind := ![1, 2, 3]
 w_ind := ![0, 1]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 2, 0, 1, 1],![0, 2, 0, 2, 0],![1, 2, 2, 1, 1],![0, 1, 2, 2, 1],![0, 1, 1, 2, 2]]
 w1 := ![0, 0, 1]
 w2 := ![0, 1]
 a := ![![-47, 9, -21],![-30, 34, -60],![21, -63, -95],![48, -24, -96],![3, 15, -36]]
 c := ![![-12, -6],![-96, -18],![-72, -36],![-140, -36],![-84, -14]]
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
    
