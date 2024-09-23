
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible139

-- Number field with label 5.1.91125000000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 100*X^2 - 525*X - 15720
lemma T_def : T = X^5 - 100*X^2 - 525*X - 15720 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-15720, -525, -100, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/22728*a^4 + 1519/22728*a^3 - 10895/22728*a^2 - 1207/7576*a - 27/947]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  22728
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![22728, 0, 0, 0, 0], ![0, 22728, 0, 0, 0], ![0, 0, 22728, 0, 0], ![0, -11364, 0, 11364, 0], ![-648, -3621, -10895, 1519, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![324, 1051, 5447, -1519, 11364],![44, 140, 728, -204, 1519]],
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![648, 2102, 10895, -3038, 22728],![7860, 262, 50, -1, 0],![740, -972, -5216, 1456, -10895]],
![![0, 0, 0, 1, 0],![324, 1051, 5447, -1519, 11364],![7860, 262, 50, -1, 0],![-324, 2904, -5316, 1569, -11364],![-3840, 170, -1214, 344, -2520]],
![![0, 0, 0, 0, 1],![44, 140, 728, -204, 1519],![740, -972, -5216, 1456, -10895],![-3840, 170, -1214, 344, -2520],![-872, 476, 2274, -634, 4752]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-22728]],![[], [], [], [-258280992], [-34523832, -22728]],![[], [], [-258280992], [0, -129140496], [123822144, -17261916, -11364]],![[], [-22728], [-34523832, -22728], [123822144, -17261916, -11364], [33106152, -2285571, -3038, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [324, 1051, 5447, -1519, 11364], [44, 140, 728, -204, 1519]],
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [648, 2102, 10895, -3038, 22728], [7860, 262, 50, -1, 0], [740, -972, -5216, 1456, -10895]],
 ![[0, 0, 0, 1, 0], [324, 1051, 5447, -1519, 11364], [7860, 262, 50, -1, 0], [-324, 2904, -5316, 1569, -11364], [-3840, 170, -1214, 344, -2520]],
 ![[0, 0, 0, 0, 1], [44, 140, 728, -204, 1519], [740, -972, -5216, 1456, -10895], [-3840, 170, -1214, 344, -2520], [-872, 476, 2274, -634, 4752]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] rfl

instance hp947: Fact $ Nat.Prime 947 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [3144, 105, 20]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [4]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3, 2, 947] where
 n := 4
 p := ![2, 3, 5, 947]
 exp := ![14, 8, 9, 2]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp947.out
 a := [-11986382025000000, 317765025000000, 37598175000000, -2217375000000]
 b := [264918600000000, 2370667905000000, -63553005000000, -7519635000000, 443475000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 2, 2, 0], [2, 2, 2, 0, 1]],
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, 2, 1, 0], [0, 1, 2, 2, 0], [2, 0, 1, 1, 1]],
![[0, 0, 0, 1, 0], [0, 1, 2, 2, 0], [0, 1, 2, 2, 0], [0, 0, 0, 0, 0], [0, 2, 1, 2, 0]],
![[0, 0, 0, 0, 1], [2, 2, 2, 0, 1], [2, 0, 1, 1, 1], [0, 2, 1, 2, 0], [1, 2, 0, 2, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 2, 0, 2],![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 2, 0, 2],![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0]]
 v_ind := ![0, 1, 3]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl
 hwFrobComp := by intro i ; fin_cases i <;> rfl
 g := ![![2, 2, 4, 4, 0],![0, 0, 0, 2, 2],![4, 4, 4, 2, 4],![0, 2, 4, 0, 0],![0, 2, 1, 1, 0]]
 w1 := ![1, 0, 0]
 w2 := ![0, 1]
 a := ![![108476, -56271, -28920],![21324, -11011, -5676],![67008, -34755, -17860],![50370, -26193, -13440],![29397, -15252, -7836]]
 c := ![![-20382, 27321],![-1188, 5967],![-12684, 16899],![-13030, 11937],![-5811, 7366]]
 hmulw := by decide
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0]],
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![1, 4]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl
 hwFrobComp := by intro i ; fin_cases i <;> rfl
 g := ![![0, 0, 0, 1, 0],![0, 0, 1, 1, 0],![1, 1, 0, 0, 1],![0, 1, 1, 0, 1],![0, 1, 1, 0, 0]]
 w1 := ![1, 1]
 w2 := ![1, 1, 0]
 a := ![![15177, 31572],![20858, 43405],![-26, -64],![5654, 11768],![6412, 13352]]
 c := ![![2496, -5796, -2106],![3190, -8070, -2894],![23, 48, 4],![716, -2227, -784],![716, -2568, -889]]
 hmulw := by decide
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

noncomputable def M947 : MaximalOrderCertificateOfUnramifiedLists 947 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [324, 104, 712, 375, 0], [44, 140, 728, 743, 572]],
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [648, 208, 478, 750, 0], [284, 262, 50, 946, 0], [740, 922, 466, 509, 469]],
![[0, 0, 0, 1, 0], [324, 104, 712, 375, 0], [284, 262, 50, 946, 0], [623, 63, 366, 622, 0], [895, 170, 680, 344, 321]],
![[0, 0, 0, 0, 1], [44, 140, 728, 743, 572], [740, 922, 466, 509, 469], [895, 170, 680, 344, 321], [75, 476, 380, 313, 17]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![7, 916, 484, 347, 0],![259, 710, 863, 528, 0],![338, 890, 507, 116, 0],![208, 402, 312, 435, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by intro i; fin_cases i ; all_goals {unfold nPow_sq_table ; unfold nPow_sq_table ; rfl}  -- unfolding prevents a heartbeats maxout.

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [3, 2, 947]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 947 O Om hm M947
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3, 2, 947] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
