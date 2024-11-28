
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible49

-- Number field with label 5.1.225000000.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 70*X^2 + 60*X - 24 
lemma T_def : T = X^5 + 15*X^3 - 70*X^2 + 60*X - 24 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-24, 60, -70, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/24*a^4 - 1/12*a^3 - 5/24*a^2 - 1/2*a - 1/2] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  24
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![24, 0, 0, 0, 0], ![0, 24, 0, 0, 0], ![0, 0, 24, 0, 0], ![0, -12, 0, 12, 0], ![-12, -12, -5, -2, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![6, 7, 2, 2, 12],![0, -5, 2, -2, -2]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![12, 14, 5, 4, 24],![12, -38, 35, -16, 0],![-12, -2, -13, 4, -20]], 
![![0, 0, 0, 1, 0],![6, 7, 2, 2, 12],![12, -38, 35, -16, 0],![-51, -36, -36, 18, -102],![12, 54, -18, 12, 45]], 
![![0, 0, 0, 0, 1],![0, -5, 2, -2, -2],![-12, -2, -13, 4, -20],![12, 54, -18, 12, 45],![6, -18, 18, -10, 1]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-24]],![[], [], [], [-288], [48, -24]],![[], [], [-288], [0, -144], [252, 24, -12]],![[], [-24], [48, -24], [252, 24, -12], [-126, 21, 4, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [6, 7, 2, 2, 12], [0, -5, 2, -2, -2]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [12, 14, 5, 4, 24], [12, -38, 35, -16, 0], [-12, -2, -13, 4, -20]], 
 ![[0, 0, 0, 1, 0], [6, 7, 2, 2, 12], [12, -38, 35, -16, 0], [-51, -36, -36, 18, -102], [12, 54, -18, 12, 45]], 
 ![[0, 0, 0, 0, 1], [0, -5, 2, -2, -2], [-12, -2, -13, 4, -20], [12, 54, -18, 12, 45], [6, -18, 18, -10, 1]]]

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
 f := [5, -11, 15, -2, 1]
 g :=  [1, 1]
 h :=  [1, 4, 1, 4, 1]
 a :=  [4]
 b :=  [1, 3, 2, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![14, 4, 8]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-65340000000, 20790000000, 540000000, 2430000000]
 b := [-17496000000, 32832000000, -7074000000, -108000000, -486000000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 4]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 1, 0, 1, 0],![1, 1, 1, 1, 1],![1, 1, 0, 1, 1],![0, 1, 1, 0, 0],![0, 1, 0, 0, 1]]
 w1 := ![1, 1]
 w2 := ![0, 1, 1]
 a := ![![33, -22],![26, 5],![24, -10],![2, 24],![-10, 20]]
 c := ![![-12, 38, 16],![-2, 14, 20],![-1, 34, 28],![2, -25, -4],![14, -10, 15]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t :=  2
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 2, 2, 0], [0, 1, 2, 1, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, 2, 1, 0], [0, 1, 2, 2, 0], [0, 1, 2, 1, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 2, 2, 0], [0, 1, 2, 2, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 2, 1, 1], [0, 1, 2, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 2, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 0, 0, 0, 2]]
 v := ![![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 0, 0, 0, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 0, 0, 1, 2]]
 v_ind := ![1, 3]
 w_ind := ![0, 1, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 2, 2, 1, 1],![1, 2, 1, 2, 1],![0, 0, 0, 2, 2],![0, 2, 4, 4, 0],![0, 0, 0, 2, 1]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![-44, 54],![-93, 139],![-42, 90],![-339, 432],![-90, 144]]
 c := ![![-6, 51, -48],![27, 186, -129],![58, 174, -90],![-24, 449, -393],![42, 213, -137]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
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
    
