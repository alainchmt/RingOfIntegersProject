
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible67

-- Number field with label 5.1.607500000.5 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 25*X^3 - 70*X^2 + 90*X - 88 
lemma T_def : T = X^5 + 25*X^3 - 70*X^2 + 90*X - 88 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-88, 90, -70, 25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/7*a^3 + 3/7*a^2 + 1/7*a + 2/7, 1/14*a^4 - 1/14*a^2 + 3/7*a - 3/7] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  14
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![14, 0, 0, 0, 0], ![0, 14, 0, 0, 0], ![0, 0, 14, 0, 0], ![4, 2, 6, 2, 0], ![-6, 6, -1, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![-2, -1, -3, 7, 0],![0, -1, -1, 3, 2],![10, -5, 11, -13, 0]], 
![![0, 0, 1, 0, 0],![-2, -1, -3, 7, 0],![6, -6, 1, 0, 14],![22, -12, 21, -24, 6],![-22, 12, -25, 38, -26]], 
![![0, 0, 0, 1, 0],![0, -1, -1, 3, 2],![22, -12, 21, -24, 6],![12, -6, 11, -10, -4],![-38, 18, -43, 54, 0]], 
![![0, 0, 0, 0, 1],![10, -5, 11, -13, 0],![-22, 12, -25, 38, -26],![-38, 18, -43, 54, 0],![94, -48, 104, -138, 41]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-14]],![[], [], [], [-28], [0, -14]],![[], [], [-28], [-24, -4], [50, -6, -2]],![[], [-14], [0, -14], [50, -6, -2], [-82, 27, 0, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [-2, -1, -3, 7, 0], [0, -1, -1, 3, 2], [10, -5, 11, -13, 0]], 
 ![[0, 0, 1, 0, 0], [-2, -1, -3, 7, 0], [6, -6, 1, 0, 14], [22, -12, 21, -24, 6], [-22, 12, -25, 38, -26]], 
 ![[0, 0, 0, 1, 0], [0, -1, -1, 3, 2], [22, -12, 21, -24, 6], [12, -6, 11, -10, -4], [-38, 18, -43, 54, 0]], 
 ![[0, 0, 0, 0, 1], [10, -5, 11, -13, 0], [-22, 12, -25, 38, -26], [-38, 18, -43, 54, 0], [94, -48, 104, -138, 41]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [2]
 b' :=  [0, 1, 1]
 k := [1, 0, 2, 0, 1]
 f := [30, -29, 25, -7, 1]
 g :=  [2, 1, 2, 1]
 h :=  [1, 1, 1]
 a :=  [2, 1, 2]
 b :=  [2, 1, 2, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [18, -17, 16, -3, 1]
 g :=  [2, 1]
 h :=  [1, 2, 4, 3, 1]
 a :=  [1]
 b :=  [4, 4, 0, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![7, 5, 7, 4]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
 a := [-89302500000, -32413500000, -7938000000, -1323000000]
 b := [-22491000000, 22623300000, 9128700000, 1587600000, 264600000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 4]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 0, 0, 0, 1],![1, 0, 1, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 1, 0],![0, 1, 1, 1, 1]]
 w1 := ![1, 1]
 w2 := ![0, 1, 1]
 a := ![![-299, 130],![66, -15],![-332, 150],![86, -26],![-148, 88]]
 c := ![![60, 118, 28],![0, -36, -12],![69, 128, 30],![-6, -45, 4],![54, 36, 19]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [5, 6, 4, 0, 0], [0, 6, 6, 3, 2], [3, 2, 4, 1, 0]], 
![[0, 0, 1, 0, 0], [5, 6, 4, 0, 0], [6, 1, 1, 0, 0], [1, 2, 0, 4, 6], [6, 5, 3, 3, 2]], 
![[0, 0, 0, 1, 0], [0, 6, 6, 3, 2], [1, 2, 0, 4, 6], [5, 1, 4, 4, 3], [4, 4, 6, 5, 0]], 
![[0, 0, 0, 0, 1], [3, 2, 4, 1, 0], [6, 5, 3, 3, 2], [4, 4, 6, 5, 0], [3, 1, 6, 2, 6]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![6, 0, 2, 0, 0],![4, 4, 0, 0, 0],![3, 1, 1, 6, 3],![6, 6, 2, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 7]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 7] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
