
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5ExamplesNativeDecide.Irreducible26

-- Number field with label 5.1.48600000.3 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 10*X^2 - 30*X - 12 
lemma T_def : T = X^5 + 15*X^3 - 10*X^2 - 30*X - 12 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-12, -30, -10, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/6*a^4 + 1/6*a^3 - 1/3*a^2] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  6
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![6, 0, 0, 0, 0], ![0, 6, 0, 0, 0], ![0, 0, 6, 0, 0], ![0, 0, -3, 3, 0], ![0, 0, -2, 1, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 1, 2, 0],![0, 0, 0, -2, 3],![2, 5, -1, -6, 1]], 
![![0, 0, 1, 0, 0],![0, 0, 1, 2, 0],![0, 0, 1, -2, 6],![6, 15, -3, -14, -3],![2, 7, 3, 4, -17]], 
![![0, 0, 0, 1, 0],![0, 0, 0, -2, 3],![6, 15, -3, -14, -3],![-6, -12, 9, 27, -21],![-18, -45, 12, 48, 6]], 
![![0, 0, 0, 0, 1],![2, 5, -1, -6, 1],![2, 7, 3, 4, -17],![-18, -45, 12, 48, 6],![-8, -26, -5, -4, 54]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-6]],![[], [], [], [-18], [-6, -6]],![[], [], [-18], [18, -9], [54, 0, -3]],![[], [-6], [-6, -6], [54, 0, -3], [24, 18, -2, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [0, 0, 0, -2, 3], [2, 5, -1, -6, 1]], 
 ![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [0, 0, 1, -2, 6], [6, 15, -3, -14, -3], [2, 7, 3, 4, -17]], 
 ![[0, 0, 0, 1, 0], [0, 0, 0, -2, 3], [6, 15, -3, -14, -3], [-6, -12, 9, 27, -21], [-18, -45, 12, 48, 6]], 
 ![[0, 0, 0, 0, 1], [2, 5, -1, -6, 1], [2, 7, 3, 4, -17], [-18, -45, 12, 48, 6], [-8, -26, -5, -4, 54]]]

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
 f := [3, 8, 5, -1, 1]
 g :=  [3, 1]
 h :=  [1, 3, 4, 2, 1]
 a :=  [3]
 b :=  [4, 4, 2, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![10, 7, 5]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-4762800000, 4406400000, -307800000, 469800000]
 b := [1671840000, 1885680000, -1445040000, 61560000, -93960000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1], [0, 1, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 1, 1, 1], [0, 1, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 1, 0]]
 v := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 1, 0, 1, 0],![0, 1, 0, 1, 1],![1, 0, 0, 1, 0],![0, 1, 0, 0, 1],![0, 1, 1, 0, 0]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![-1, 12],![44, 7],![0, 10],![44, -2],![-20, 10]]
 c := ![![-4, -24, 14],![-6, -46, 8],![-5, -30, 16],![0, -15, -8],![2, 16, 1]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [0, 0, 0, 1, 0], [2, 2, 2, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [2, 1, 0, 1, 1]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [2, 2, 2, 0, 1], [2, 1, 0, 1, 1], [0, 0, 0, 0, 0], [1, 1, 1, 2, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 2, 0, 2],![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 2, 0, 2],![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 2, 0]]
 v_ind := ![0, 1, 3]
 w_ind := ![0, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 1, 2, 0, 1],![2, 4, 0, 0, 2],![4, 0, 2, 2, 2],![0, 2, 4, 2, 0],![0, 0, 0, 2, 0]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![16, 6, 15],![63, -37, 42],![33, 18, 176],![-30, 81, 84],![-9, 30, 120]]
 c := ![![-3, 6],![-27, -3],![-27, -42],![14, -9],![-9, -38]]
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
    
