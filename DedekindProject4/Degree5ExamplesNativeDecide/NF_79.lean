
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5ExamplesNativeDecide.Irreducible79

-- Number field with label 5.1.729000000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 30*X^3 - 40*X^2 + 240*X - 192 
lemma T_def : T = X^5 - 30*X^3 - 40*X^2 + 240*X - 192 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-192, 240, -40, -30, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/16*a^4 + 1/8*a^2 - 1/2*a] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  16
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![16, 0, 0, 0, 0], ![0, 16, 0, 0, 0], ![0, 0, 8, 0, 0], ![0, -8, 0, 4, 0], ![0, -8, 2, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 2, 0, 0],![0, 1, 0, 2, 0],![0, 2, -2, 0, 4],![12, -11, 4, 8, 0]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![0, 2, -1, 0, 4],![24, -23, 10, 14, 0],![0, 16, -19, 4, 16]], 
![![0, 0, 0, 1, 0],![0, 2, -2, 0, 4],![24, -23, 10, 14, 0],![0, 30, -36, 10, 26],![90, -88, 42, 41, 8]], 
![![0, 0, 0, 0, 1],![12, -11, 4, 8, 0],![0, 16, -19, 4, 16],![90, -88, 42, 41, 8],![18, 45, -68, 35, 49]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-16]],![[], [], [], [-32], [0, -8]],![[], [], [-32], [0, -16], [-120, 0, -4]],![[], [-16], [0, -8], [-120, 0, -4], [-24, -34, 0, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 0, 2, 0], [0, 2, -2, 0, 4], [12, -11, 4, 8, 0]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, -1, 0, 4], [24, -23, 10, 14, 0], [0, 16, -19, 4, 16]], 
 ![[0, 0, 0, 1, 0], [0, 2, -2, 0, 4], [24, -23, 10, 14, 0], [0, 30, -36, 10, 26], [90, -88, 42, 41, 8]], 
 ![[0, 0, 0, 0, 1], [12, -11, 4, 8, 0], [0, 16, -19, 4, 16], [90, -88, 42, 41, 8], [18, 45, -68, 35, 49]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [2]
 b' :=  [2, 2]
 k := [0, 1]
 f := [64, -80, 14, 11, 1]
 g :=  [0, 2, 1]
 h :=  [0, 1, 1, 1]
 a :=  [1]
 b :=  [1, 0, 2]
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
 f := [39, -46, 11, 8, 1]
 g :=  [3, 1]
 h :=  [1, 3, 4, 2, 1]
 a :=  [1]
 b :=  [4, 4, 0, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 3
 p := ![2, 3, 5]
 exp := ![20, 6, 6]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-846028800000, -363916800000, 29030400000, 22291200000]
 b := [-627056640000, 345876480000, 126282240000, -5806080000, -4458240000]
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
![[0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 1, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 0, 1, 0, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 3]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 0, 1, 0, 0],![1, 0, 0, 1, 0],![1, 1, 0, 0, 1],![0, 0, 0, 1, 0],![0, 1, 0, 0, 0]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![9, 22],![-146, 93],![-18, 128],![-146, 92],![-20, 16]]
 c := ![![12, 16, -14],![90, 22, 24],![75, 56, -44],![90, 21, 24],![12, 2, 3]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
