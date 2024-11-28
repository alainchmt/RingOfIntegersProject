
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible47

-- Number field with label 5.3.202500000.3 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 15*X^3 - 60*X^2 + 120*X + 96 
lemma T_def : T = X^5 - 15*X^3 - 60*X^2 + 120*X + 96 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [96, 120, -60, -15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/184*a^4 - 4/23*a^3 + 89/184*a^2 + 9/46*a + 9/23] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  184
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![184, 0, 0, 0, 0], ![0, 184, 0, 0, 0], ![0, 0, 184, 0, 0], ![0, -92, 0, 92, 0], ![72, 36, 89, -32, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-36, -2, -45, 32, 92],![12, 1, 16, -10, -32]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-72, -4, -89, 64, 184],![-48, -53, 30, 14, 0],![-24, 16, -61, 32, 104]], 
![![0, 0, 0, 1, 0],![-36, -2, -45, 32, 92],![-48, -53, 30, 14, 0],![-234, -22, -319, 238, 598],![42, -23, 112, -64, -176]], 
![![0, 0, 0, 0, 1],![12, 1, 16, -10, -32],![-24, 16, -61, 32, 104],![42, -23, 112, -64, -176],![-24, 17, -68, 37, 109]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-184]],![[], [], [], [-16928], [5888, -184]],![[], [], [-16928], [0, -8464], [-9476, 2944, -92]],![[], [-184], [5888, -184], [-9476, 2944, -92], [6524, -1217, 64, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-36, -2, -45, 32, 92], [12, 1, 16, -10, -32]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-72, -4, -89, 64, 184], [-48, -53, 30, 14, 0], [-24, 16, -61, 32, 104]], 
 ![[0, 0, 0, 1, 0], [-36, -2, -45, 32, 92], [-48, -53, 30, 14, 0], [-234, -22, -319, 238, 598], [42, -23, 112, -64, -176]], 
 ![[0, 0, 0, 0, 1], [12, 1, 16, -10, -32], [-24, 16, -61, 32, 104], [42, -23, 112, -64, -176], [-24, 17, -68, 37, 109]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp23: Fact $ Nat.Prime 23 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-32, -40, 20, 5]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [1]
 b :=  [1, 1, 1]
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
 f := [-19, -23, 13, 4, 1]
 g :=  [1, 1]
 h :=  [1, 4, 1, 4, 1]
 a :=  [4]
 b :=  [2, 0, 3, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 23] where
 n := 4
 p := ![2, 3, 5, 23]
 exp := ![13, 4, 7, 2]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp23.out
 a := [153792000000, 49437000000, -2376000000, -7533000000]
 b := [105494400000, -87847200000, -18927000000, 475200000, 1506600000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 0, 0, 1, 0],![1, 1, 0, 1, 0],![0, 1, 0, 0, 1],![0, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![191, -64],![218, -77],![154, -98],![318, -150],![348, -192]]
 c := ![![-98, 124, -156],![-104, 138, -168],![-21, 88, -62],![-114, 197, -206],![-90, 210, -185]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M23 : MaximalOrderCertificateOfUnramifiedLists 23 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [10, 21, 1, 9, 0], [12, 1, 16, 13, 14]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [20, 19, 3, 18, 0], [21, 16, 7, 14, 0], [22, 16, 8, 9, 12]], 
![[0, 0, 0, 1, 0], [10, 21, 1, 9, 0], [21, 16, 7, 14, 0], [19, 1, 3, 8, 0], [19, 0, 20, 5, 8]], 
![[0, 0, 0, 0, 1], [12, 1, 16, 13, 14], [22, 16, 8, 9, 12], [19, 0, 20, 5, 8], [22, 17, 1, 14, 17]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![4, 12, 9, 7, 0],![16, 15, 0, 2, 0],![8, 14, 7, 11, 0],![3, 21, 2, 3, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 23]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 23 O Om hm M23
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 23] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
