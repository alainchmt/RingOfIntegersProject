
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible122

-- Number field with label 5.3.10125000000.3 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 150*X^2 + 480 
lemma T_def : T = X^5 - 25*X^3 - 150*X^2 + 480 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [480, 0, -150, -25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/248*a^4 + 3/62*a^3 + 119/248*a^2 + 19/124*a - 5/31] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  248
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![248, 0, 0, 0, 0], ![0, 248, 0, 0, 0], ![0, 0, 248, 0, 0], ![0, -124, 0, 124, 0], ![-40, 38, 119, 12, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![20, -25, -60, -12, 124],![0, -2, -5, 0, 12]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![40, -50, -119, -24, 248],![-240, 12, 75, 24, 0],![0, -29, -62, -10, 144]], 
![![0, 0, 0, 1, 0],![20, -25, -60, -12, 124],![-240, 12, 75, 24, 0],![230, -370, -684, -63, 1426],![-100, -49, -72, -2, 238]], 
![![0, 0, 0, 0, 1],![0, -2, -5, 0, 12],![0, -29, -62, -10, 144],![-100, -49, -72, -2, 238],![-10, -24, -47, -6, 116]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-248]],![[], [], [], [-30752], [-2976, -248]],![[], [], [-30752], [0, -15376], [-17732, -1488, -124]],![[], [-248], [-2976, -248], [-17732, -1488, -124], [-3682, -407, -24, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [20, -25, -60, -12, 124], [0, -2, -5, 0, 12]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [40, -50, -119, -24, 248], [-240, 12, 75, 24, 0], [0, -29, -62, -10, 144]], 
 ![[0, 0, 0, 1, 0], [20, -25, -60, -12, 124], [-240, 12, 75, 24, 0], [230, -370, -684, -63, 1426], [-100, -49, -72, -2, 238]], 
 ![[0, 0, 0, 0, 1], [0, -2, -5, 0, 12], [0, -29, -62, -10, 144], [-100, -49, -72, -2, 238], [-10, -24, -47, -6, 116]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp31: Fact $ Nat.Prime 31 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := []
 b' :=  [2]
 k := [1, 0, 1, 0, 1]
 f := [-160, 0, 50, 9]
 g :=  [0, 2, 0, 1]
 h :=  [0, 0, 1]
 a :=  [2, 0, 2]
 b :=  [0, 2]
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
 f := [-96, 0, 30, 5]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [4]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 31] where
 n := 4
 p := ![2, 3, 5, 31]
 exp := ![14, 4, 9, 2]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp31.out
 a := [5189400000000, 975375000000, 164700000000, -111825000000]
 b := [1560600000000, -2721330000000, -418725000000, -32940000000, 22365000000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 0, 0, 0, 1],![1, 1, 1, 1, 1],![0, 0, 0, 1, 1],![0, 1, 1, 0, 0],![0, 1, 0, 1, 0]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![405, -118],![1594, -417],![1008, -236],![586, -182],![618, -120]]
 c := ![![-4, -230, -8],![-134, -906, -22],![-155, -576, -8],![20, -331, -14],![-150, -352, 1]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M31 : MaximalOrderCertificateOfUnramifiedLists 31 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [20, 6, 2, 19, 0], [0, 29, 26, 0, 12]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [9, 12, 5, 7, 0], [8, 12, 13, 24, 0], [0, 2, 0, 21, 20]], 
![[0, 0, 0, 1, 0], [20, 6, 2, 19, 0], [8, 12, 13, 24, 0], [13, 2, 29, 30, 0], [24, 13, 21, 29, 21]], 
![[0, 0, 0, 0, 1], [0, 29, 26, 0, 12], [0, 2, 0, 21, 20], [24, 13, 21, 29, 21], [21, 7, 15, 25, 23]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![15, 7, 15, 17, 0],![29, 24, 30, 6, 0],![2, 7, 2, 26, 0],![18, 1, 18, 8, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 31]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 31 O Om hm M31
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 31] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
