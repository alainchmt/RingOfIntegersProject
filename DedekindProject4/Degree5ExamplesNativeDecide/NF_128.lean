
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5ExamplesNativeDecide.Irreducible128

-- Number field with label 5.3.12000000000.4 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 200*X^2 - 450*X + 480 
lemma T_def : T = X^5 - 200*X^2 - 450*X + 480 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [480, -450, -200, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/3*a^3 + 1/3*a^2, 1/702*a^4 + 7/351*a^3 + 98/351*a^2 - 44/117*a + 11/117] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  702
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![702, 0, 0, 0, 0], ![0, 702, 0, 0, 0], ![0, 0, 702, 0, 0], ![0, 0, 234, 234, 0], ![66, -264, 196, 14, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, -1, 3, 0],![-22, 88, -61, -13, 234],![-2, 6, -4, 0, 14]], 
![![0, 0, 1, 0, 0],![0, 0, -1, 3, 0],![-66, 264, -182, -42, 702],![-182, 238, 6, -14, 234],![-28, 82, -46, -12, 196]], 
![![0, 0, 0, 1, 0],![-22, 88, -61, -13, 234],![-182, 238, 6, -14, 234],![-114, 76, 52, 62, 78],![-52, 58, 10, 2, 44]], 
![![0, 0, 0, 0, 1],![-2, 6, -4, 0, 14],![-28, 82, -46, -12, 196],![-52, 58, 10, 2, 44],![-10, 24, -11, -3, 53]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-702]],![[], [], [], [-164268], [-9828, -702]],![[], [], [-164268], [-109512, -54756], [-49140, -3510, -234]],![[], [-702], [-9828, -702], [-49140, -3510, -234], [-5160, -588, -28, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, -1, 3, 0], [-22, 88, -61, -13, 234], [-2, 6, -4, 0, 14]], 
 ![[0, 0, 1, 0, 0], [0, 0, -1, 3, 0], [-66, 264, -182, -42, 702], [-182, 238, 6, -14, 234], [-28, 82, -46, -12, 196]], 
 ![[0, 0, 0, 1, 0], [-22, 88, -61, -13, 234], [-182, 238, 6, -14, 234], [-114, 76, 52, 62, 78], [-52, 58, 10, 2, 44]], 
 ![[0, 0, 0, 0, 1], [-2, 6, -4, 0, 14], [-28, 82, -46, -12, 196], [-52, 58, 10, 2, 44], [-10, 24, -11, -3, 53]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp13: Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-96, 90, 40]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [4]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 13] where
 n := 4
 p := ![2, 3, 5, 13]
 exp := ![13, 9, 9, 2]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp13.out
 a := [67748400000000, -3445200000000, 205200000000, -707400000000]
 b := [-46008000000000, -30527280000000, 689040000000, -41040000000, 141480000000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 3
 n := 2
 t :=  3
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 1, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 1, 1]]
 v_ind := ![1, 2, 3]
 w_ind := ![0, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 0, 0, 1, 1],![0, 1, 1, 1, 0],![0, 1, 0, 1, 0],![0, 0, 0, 0, 1],![0, 0, 1, 1, 1]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![713, -44, 24],![1284, -321, -48],![618, -52, 29],![194, -62, -16],![1378, -314, -54]]
 c := ![![-262, 498],![-376, 1112],![-224, 448],![-51, 180],![-414, 1161]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 2, 0, 0], [2, 1, 2, 2, 0], [1, 0, 2, 0, 2]], 
![[0, 0, 1, 0, 0], [0, 0, 2, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [2, 1, 2, 0, 1]], 
![[0, 0, 0, 1, 0], [2, 1, 2, 2, 0], [1, 1, 0, 1, 0], [0, 1, 1, 2, 0], [2, 1, 1, 2, 2]], 
![[0, 0, 0, 0, 1], [1, 0, 2, 0, 2], [2, 1, 2, 0, 1], [2, 1, 1, 2, 2], [2, 0, 1, 0, 2]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 2, 0, 0, 0],![0, 0, 0, 1, 2]]
 v := ![![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 2, 0, 0, 0],![0, 0, 0, 1, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0],![0, 0, 0, 1, 2]]
 v_ind := ![1]
 w_ind := ![0, 1, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 1, 0, 1, 2],![1, 1, 1, 0, 2],![0, 4, 2, 0, 0],![1, 2, 2, 0, 2],![0, 0, 2, 4, 4]]
 w1 := ![1]
 w2 := ![0, 0, 1, 1]
 a := ![![-626],![-867],![-1698],![-1515],![-2154]]
 c := ![![-528, 1542, -231, 3],![-458, 1764, -294, -72],![-624, 3044, -549, -138],![-744, 3000, -509, -129],![-2184, 5868, -837, 2]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
 hacindw := by native_decide 

noncomputable def M13 : MaximalOrderCertificateOfUnramifiedLists 13 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 12, 3, 0], [4, 10, 4, 0, 0], [11, 6, 9, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 12, 3, 0], [12, 4, 0, 10, 0], [0, 4, 6, 12, 0], [11, 4, 6, 1, 1]], 
![[0, 0, 0, 1, 0], [4, 10, 4, 0, 0], [0, 4, 6, 12, 0], [3, 11, 0, 10, 0], [0, 6, 10, 2, 5]], 
![[0, 0, 0, 0, 1], [11, 6, 9, 0, 1], [11, 4, 6, 1, 1], [0, 6, 10, 2, 5], [3, 11, 2, 10, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![11, 1, 5, 2, 0],![7, 0, 3, 6, 0],![4, 0, 3, 10, 0],![11, 8, 7, 8, 12]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3, 13]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 13 O Om hm M13
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 13] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
