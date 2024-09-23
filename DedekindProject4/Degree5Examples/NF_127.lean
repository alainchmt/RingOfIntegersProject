
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible127

-- Number field with label 5.1.10125000000.20 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 75*X^3 - 50*X^2 + 2250*X + 5820
lemma T_def : T = X^5 - 75*X^3 - 50*X^2 + 2250*X + 5820 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [5820, 2250, -50, -75, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/1982*a^4 - 157/991*a^3 - 579/1982*a^2 - 294/991*a + 287/991]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  1982
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1982, 0, 0, 0, 0], ![0, 1982, 0, 0, 0], ![0, 0, 1982, 0, 0], ![0, 0, 0, 1982, 0], ![574, -588, -579, -314, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-574, 588, 579, 314, 1982],![88, -94, -92, -50, -314]],
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-574, 588, 579, 314, 1982],![-5820, -2250, 50, 75, 0],![1068, 204, -156, -92, -504]],
![![0, 0, 0, 1, 0],![-574, 588, 579, 314, 1982],![-5820, -2250, 50, 75, 0],![-43050, 38280, 41175, 23600, 148650],![8456, -5652, -6696, -3844, -24088]],
![![0, 0, 0, 0, 1],![88, -94, -92, -50, -314],![1068, 204, -156, -92, -504],![8456, -5652, -6696, -3844, -24088],![-1634, 870, 1126, 646, 4029]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-1982]],![[], [], [], [-3928324], [622348, -1982]],![[], [], [-3928324], [0, -3928324], [998928, 622348, -1982]],![[], [-1982], [622348, -1982], [998928, 622348, -1982], [-315386, -97513, 628, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-574, 588, 579, 314, 1982], [88, -94, -92, -50, -314]],
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-574, 588, 579, 314, 1982], [-5820, -2250, 50, 75, 0], [1068, 204, -156, -92, -504]],
 ![[0, 0, 0, 1, 0], [-574, 588, 579, 314, 1982], [-5820, -2250, 50, 75, 0], [-43050, 38280, 41175, 23600, 148650], [8456, -5652, -6696, -3844, -24088]],
 ![[0, 0, 0, 0, 1], [88, -94, -92, -50, -314], [1068, 204, -156, -92, -504], [8456, -5652, -6696, -3844, -24088], [-1634, 870, 1126, 646, 4029]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] rfl

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp991: Fact $ Nat.Prime 991 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [2]
 b' :=  [1, 2]
 k := [0, 1]
 f := [-1940, -750, 17, 26, 1]
 g :=  [0, 1, 1]
 h :=  [0, 1, 2, 1]
 a :=  [1, 2]
 b :=  [1, 0, 0, 1]
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
 f := [-1164, -450, 10, 15]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [1]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 991] where
 n := 4
 p := ![2, 3, 5, 991]
 exp := ![8, 4, 9, 2]
 pdgood := [3, 5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp991.out
 a := [-86924475000000, 27862312500000, 2073600000000, -698962500000]
 b := [242522100000000, 25632720000000, -9766237500000, -414720000000, 139792500000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]],
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 4]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl
 hwFrobComp := by intro i ; fin_cases i <;> rfl
 g := ![![1, 0, 1, 0, 0],![0, 1, 1, 1, 0],![0, 1, 1, 0, 1],![0, 0, 1, 1, 0],![0, 0, 0, 0, 1]]
 w1 := ![1, 1]
 w2 := ![1, 1, 1]
 a := ![![-85, 370],![-30748, 72091],![4400, -10226],![-30300, 71114],![4934, -11572]]
 c := ![![-5038, -1708, 488],![-43890, 46502, 129690],![1963, -8278, -18626],![-43404, 45783, 128022],![7488, -7288, -20781]]
 hmulw := by decide
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide


noncomputable def M991 : MaximalOrderCertificateOfUnramifiedLists 991 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [417, 588, 579, 314, 0], [88, 897, 899, 941, 677]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [417, 588, 579, 314, 0], [126, 723, 50, 75, 0], [77, 204, 835, 899, 487]],
![[0, 0, 0, 1, 0], [417, 588, 579, 314, 0], [126, 723, 50, 75, 0], [554, 622, 544, 807, 0], [528, 294, 241, 120, 687]],
![[0, 0, 0, 0, 1], [88, 897, 899, 941, 677], [77, 204, 835, 899, 487], [528, 294, 241, 120, 687], [348, 870, 135, 646, 65]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![263, 533, 398, 353, 0],![836, 33, 920, 903, 0],![939, 856, 729, 529, 0],![4, 199, 32, 100, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by intro i; fin_cases i ; all_goals {unfold nPow_sq_table ; unfold nPow_sq_table ; rfl}  -- unfolding prevents a heartbeats maxout.

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 991]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 991 O Om hm M991
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 991] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
