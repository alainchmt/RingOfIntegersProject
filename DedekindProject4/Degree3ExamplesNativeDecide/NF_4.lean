
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree3ExamplesNativeDecide.Irreducible4
import DedekindProject4.DiscriminantSubalgebraBuilder

-- Number field with label 3.1.9720.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^3 - 18*X - 48
lemma T_def : T = X^3 - 18*X - 48 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-48, -18, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2]

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d :=  2
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![2, 0, 0], ![0, 2, 0], ![0, 0, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]],
![![0, 1, 0],![0, 0, 2],![24, 9, 0]],
![![0, 0, 1],![24, 9, 0],![0, 12, 9]]]
 s := ![![[], [], []],![[], [], [-2]],![[], [-2], [0, -1]]]
 h := Adj
 honed := by native_decide
 hd := by norm_num
 hcc := by native_decide
 hin := by native_decide
 hsymma := by native_decide
 hc_le := by native_decide

lemma T_degree : T.natDegree = 3 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B : Basis (Fin 3) ℤ O := basisOfBuilderLists T l BQ
noncomputable def B' : Basis (Fin 3) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 3) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
def Table : Fin 3 → Fin 3 → List ℤ :=
 ![ ![[1, 0, 0], [0, 1, 0], [0, 0, 1]],
 ![[0, 1, 0], [0, 0, 2], [24, 9, 0]],
 ![[0, 0, 1], [24, 9, 0], [0, 12, 9]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := []
 b' :=  [1]
 k := [1]
 f := [16, 6]
 g :=  [0, 1]
 h :=  [0, 0, 1]
 a :=  [1]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  2
 a' := [4]
 b' :=  [4, 3]
 k := [2, 1]
 f := [12, 5, 1]
 g :=  [3, 1, 1]
 h :=  [4, 1]
 a :=  [0, 2]
 b :=  [2, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 3
 p := ![2, 3, 5]
 exp := ![5, 5, 1]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-1296, 324]
 b := [1296, 432, -108]
 hab := by native_decide
 hd := by
  intro p hp
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
 m := 1
 n := 2
 t :=  2
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]],
![[0, 1, 0], [0, 0, 0], [0, 1, 0]],
![[0, 0, 1], [0, 1, 0], [0, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0]]
 b2 := ![![1, 0, 0],![0, 0, 1]]
 v := ![![0, 1, 0]]
 w := ![![1, 0, 0],![0, 0, 1]]
 wFrob := ![![1, 0, 0],![0, 0, 1]]
 v_ind := ![1]
 w_ind := ![0, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide
 g := ![![0, 0, 1],![1, 0, 1],![0, 1, 0]]
 a := ![![![9]],![![10]],![![0]]]
 c := ![![![12, 0]],![![12, 0]],![![0, 1]]]
 d := ![![![0],![24]],![![0],![24]],![![2],![18]]]
 e := ![![![0, 1],![0, 9]],![![1, 1],![0, 10]],![![0, 0],![24, 0]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inr 0, Sum.inr 0),(Sum.inl 0, Sum.inr 1)]
 hindab := by native_decide
 hmul1 := by native_decide
 hmul2 := by native_decide


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateLists 2 O Om hm M2
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl

lemma T_discr : T.discriminant = -38880 :=  by
  rw [T_monic.discriminant_def, T_degree, ← T_ofList]
  have : [-48, -18, 0, 1].derivative = [-18, 0, 3, 0] := rfl
  rw [← ofList_derivative_eq_derivative , this]
  native_decide

theorem K_discr : NumberField.discr K = -9720 := by
  rw [discr_numberField_eq_discrSubalgebraBuilder
  T_irreducible BQ O_ringOfIntegers]
  rw [T_discr]
  rfl
