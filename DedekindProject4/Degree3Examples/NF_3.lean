
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree3Examples.Irreducible3
import DedekindProject4.DiscriminantSubalgebraBuilder
import Mathlib.NumberTheory.NumberField.Discriminant

-- Number field with label 3.1.9720.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^3 + 27*X - 18
lemma T_def : T = X^3 + 27*X - 18 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-18, 27, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/3*a^2]

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d :=  3
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![3, 0, 0], ![0, 3, 0], ![0, 0, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]],
![![0, 1, 0],![0, 0, 3],![6, -9, 0]],
![![0, 0, 1],![6, -9, 0],![0, 2, -9]]]
 s := ![![[], [], []],![[], [], [-3]],![[], [-3], [0, -1]]]
 h := Adj
 honed := rfl
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide

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
 ![[0, 1, 0], [0, 0, 3], [6, -9, 0]],
 ![[0, 0, 1], [6, -9, 0], [0, 2, -9]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] rfl

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD2: CertificateDedekindCriterionLists l 2 where
 n :=  2
 a' := []
 b' :=  [1]
 k := [0, 1]
 f := [9, -13, 1]
 g :=  [0, 1, 1]
 h :=  [1, 1]
 a :=  [1]
 b :=  [1]
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
 f := [6, -4, 1]
 g :=  [3, 1, 1]
 h :=  [4, 1]
 a :=  [2]
 b :=  [3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![3, 7, 1]
 pdgood := [2, 5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-486, -486]
 b := [2916, 162, 162]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
 m := 2
 n := 1
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]],
![[0, 1, 0], [0, 0, 0], [0, 0, 0]],
![[0, 0, 1], [0, 0, 0], [0, 2, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0],![0, 0, 1]]
 b2 := ![![1, 0, 0]]
 v := ![![0, 1, 0],![0, 0, 1]]
 w := ![![1, 0, 0]]
 wFrob := ![![1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl
 hwFrobComp := by intro i ; fin_cases i <;> rfl
 g := ![![1, 0, 0],![0, 0, 2],![0, 2, 0]]
 a := ![![![1, 0],![0, 1]],![![-18, 0],![4, -18]],![![0, 6],![-18, 0]]]
 c := ![![![0],![0]],![![4],![0]],![![0],![4]]]
 d := ![![![0, 0]],![![0, 6]],![![6, 0]]]
 e := ![![![1]],![![0]],![![0]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 1, Sum.inl 0),(Sum.inl 1, Sum.inr 0)]
 hindab := by decide
 hmul1 := by decide
 hmul2 := by decide


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [3]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateLists 3 O Om hm M3
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl

lemma T_discr : T.discriminant = 87480 :=  by
  rw [← T_ofList]
  unfold Polynomial.discriminant
  have : [-18, 27, 0, 1].derivative = [27, 0, 3, 0] := rfl
  rw [← ofList_derivative_eq_derivative , this]
  rfl

theorem K_discr : NumberField.discr K = -9720 := by
  rw [discr_numberField_eq_discrSubalgebraBuilder
  T_irreducible BQ O_ringOfIntegers]
  rw [T_degree, T_discr ]
  rfl
