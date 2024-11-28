
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5ExamplesNativeDecide.Irreducible140

-- Number field with label 5.1.91125000000.6 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 200*X^2 + 1275*X - 1740 
lemma T_def : T = X^5 - 200*X^2 + 1275*X - 1740 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-1740, 1275, -200, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/452*a^4 + 53/452*a^3 + 97/452*a^2 - 31/452*a + 21/113] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  452
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![452, 0, 0, 0, 0], ![0, 452, 0, 0, 0], ![0, 0, 452, 0, 0], ![0, -226, 0, 226, 0], ![84, -31, 97, 53, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-42, -11, -49, -53, 226],![-6, -5, -11, -12, 53]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-84, -22, -97, -106, 452],![870, -638, 100, -1, 0],![186, -150, 0, -22, 97]], 
![![0, 0, 0, 1, 0],![-42, -11, -49, -53, 226],![870, -638, 100, -1, 0],![42, 496, -270, 153, -226],![174, -26, -64, 7, 58]], 
![![0, 0, 0, 0, 1],![-6, -5, -11, -12, 53],![186, -150, 0, -22, 97],![174, -26, -64, 7, 58],![78, -40, -20, -9, 58]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-452]],![[], [], [], [-102152], [-23956, -452]],![[], [], [-102152], [0, -51076], [-21696, -11978, -226]],![[], [-452], [-23956, -452], [-21696, -11978, -226], [-10420, -3003, -106, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-42, -11, -49, -53, 226], [-6, -5, -11, -12, 53]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-84, -22, -97, -106, 452], [870, -638, 100, -1, 0], [186, -150, 0, -22, 97]], 
 ![[0, 0, 0, 1, 0], [-42, -11, -49, -53, 226], [870, -638, 100, -1, 0], [42, 496, -270, 153, -226], [174, -26, -64, 7, 58]], 
 ![[0, 0, 0, 0, 1], [-6, -5, -11, -12, 53], [186, -150, 0, -22, 97], [174, -26, -64, 7, 58], [78, -40, -20, -9, 58]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp113: Fact $ Nat.Prime 113 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [2]
 b' :=  [1, 2]
 k := [0, 1]
 f := [580, -425, 67, 1, 1]
 g :=  [0, 1, 1]
 h :=  [0, 1, 2, 1]
 a :=  [1]
 b :=  [2, 0, 2]
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
 f := [348, -255, 40]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [2]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [113, 2] where
 n := 4
 p := ![2, 3, 5, 113]
 exp := ![12, 6, 9, 2]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp113.out
 a := [134069175000000, -4209975000000, -3144825000000, -1553175000000]
 b := [241371900000000, -64090035000000, 841995000000, 628965000000, 310635000000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M113 : MaximalOrderCertificateOfUnramifiedLists 113 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [71, 102, 64, 60, 0], [107, 108, 102, 101, 53]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [29, 91, 16, 7, 0], [79, 40, 100, 112, 0], [73, 76, 0, 91, 97]], 
![[0, 0, 0, 1, 0], [71, 102, 64, 60, 0], [79, 40, 100, 112, 0], [42, 44, 69, 40, 0], [61, 87, 49, 7, 58]], 
![[0, 0, 0, 0, 1], [107, 108, 102, 101, 53], [73, 76, 0, 91, 97], [61, 87, 49, 7, 58], [78, 73, 93, 104, 58]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![92, 99, 112, 6, 0],![67, 43, 52, 110, 0],![80, 24, 42, 75, 0],![51, 12, 85, 73, 112]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 1, 0, 0],![0, 0, 0, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 1, 0, 0],![0, 0, 0, 1, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![1, 3]
 w_ind := ![0, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 0, 0, 1, 0],![0, 0, 1, 0, 1],![1, 1, 0, 1, 1],![0, 1, 1, 1, 1],![0, 1, 1, 0, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![-823, -394],![-18, 933],![-1202, 722],![-998, 1270],![48, 1280]]
 c := ![![564, 818, 404],![1746, -1170, -542],![889, 854, -248],![2244, -291, -588],![1290, -1084, -789]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [113, 2]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 113 O Om hm M113
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [113, 2] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
