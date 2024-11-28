
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5ExamplesNativeDecide.Irreducible99

-- Number field with label 5.3.1822500000.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 45*X^3 - 40*X^2 + 150*X + 192 
lemma T_def : T = X^5 - 45*X^3 - 40*X^2 + 150*X + 192 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [192, 150, -40, -45, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/158*a^4 - 25/79*a^3 - 73/158*a^2 - 12/79*a - 36/79] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  158
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![158, 0, 0, 0, 0], ![0, 158, 0, 0, 0], ![0, 0, 158, 0, 0], ![0, 0, 0, 158, 0], ![-72, -24, -73, -50, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![72, 24, 73, 50, 158],![-24, -9, -23, -16, -50]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![72, 24, 73, 50, 158],![-192, -150, 40, 45, 0],![48, 42, -27, -23, -28]], 
![![0, 0, 0, 1, 0],![72, 24, 73, 50, 158],![-192, -150, 40, 45, 0],![3240, 888, 3135, 2290, 7110],![-984, -252, -993, -729, -2234]], 
![![0, 0, 0, 0, 1],![-24, -9, -23, -16, -50],![48, 42, -27, -23, -28],![-984, -252, -993, -729, -2234],![300, 72, 317, 233, 705]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-158]],![[], [], [], [-24964], [7900, -158]],![[], [], [-24964], [0, -24964], [4424, 7900, -158]],![[], [-158], [7900, -158], [4424, 7900, -158], [-2792, -2399, 100, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [72, 24, 73, 50, 158], [-24, -9, -23, -16, -50]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [72, 24, 73, 50, 158], [-192, -150, 40, 45, 0], [48, 42, -27, -23, -28]], 
 ![[0, 0, 0, 1, 0], [72, 24, 73, 50, 158], [-192, -150, 40, 45, 0], [3240, 888, 3135, 2290, 7110], [-984, -252, -993, -729, -2234]], 
 ![[0, 0, 0, 0, 1], [-24, -9, -23, -16, -50], [48, 42, -27, -23, -28], [-984, -252, -993, -729, -2234], [300, 72, 317, 233, 705]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp79: Fact $ Nat.Prime 79 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [2]
 b' :=  [2, 2]
 k := [0, 1]
 f := [-64, -50, 14, 16, 1]
 g :=  [0, 2, 1]
 h :=  [0, 1, 1, 1]
 a :=  [2, 2]
 b :=  [0, 0, 0, 1]
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
 f := [-38, -29, 10, 11, 1]
 g :=  [2, 1]
 h :=  [1, 2, 4, 3, 1]
 a :=  [2]
 b :=  [1, 1, 2, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 79] where
 n := 4
 p := ![2, 3, 5, 79]
 exp := ![7, 6, 7, 2]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp79.out
 a := [980505000000, -976718250000, -63909000000, 39224250000]
 b := [-951733800000, -237897000000, 336550950000, 12781800000, -7844850000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 1, 1, 0, 1],![0, 1, 1, 1, 0],![1, 1, 1, 1, 1],![0, 0, 1, 1, 0],![0, 1, 1, 0, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![347, -1244],![-1262, 4747],![-876, 3300],![-1228, 4644],![-38, 204]]
 c := ![![-756, 1032, -1458],![2208, -4124, 5272],![1513, -2872, 3656],![2160, -4049, 5164],![-60, -220, 159]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M79 : MaximalOrderCertificateOfUnramifiedLists 79 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [72, 24, 73, 50, 0], [55, 70, 56, 63, 29]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [72, 24, 73, 50, 0], [45, 8, 40, 45, 0], [48, 42, 52, 56, 51]], 
![[0, 0, 0, 1, 0], [72, 24, 73, 50, 0], [45, 8, 40, 45, 0], [1, 19, 54, 78, 0], [43, 64, 34, 61, 57]], 
![[0, 0, 0, 0, 1], [55, 70, 56, 63, 29], [48, 42, 52, 56, 51], [43, 64, 34, 61, 57], [63, 72, 1, 75, 73]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![64, 45, 14, 0, 0],![38, 36, 34, 0, 0],![48, 33, 50, 1, 0],![61, 37, 1, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 79]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 79 O Om hm M79
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 79] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
