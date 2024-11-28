
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible112

-- Number field with label 5.1.3037500000.7 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 100*X^2 + 750*X + 2200 
lemma T_def : T = X^5 - 25*X^3 - 100*X^2 + 750*X + 2200 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [2200, 750, -100, -25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/5*a^3, 1/1110*a^4 - 34/555*a^3 - 19/74*a^2 + 41/111*a - 49/111] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  1110
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1110, 0, 0, 0, 0], ![0, 1110, 0, 0, 0], ![0, 0, 1110, 0, 0], ![0, 0, 0, 222, 0], ![-490, 410, -285, -68, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 5, 0],![98, -82, 57, 68, 222],![-32, 24, -17, -22, -68]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 5, 0],![490, -410, 285, 340, 1110],![-440, -150, 20, 25, 0],![20, 140, -74, -85, -260]], 
![![0, 0, 0, 1, 0],![98, -82, 57, 68, 222],![-440, -150, 20, 25, 0],![490, -498, 255, 360, 1110],![-2, 150, -57, -86, -238]], 
![![0, 0, 0, 0, 1],![-32, 24, -17, -22, -68],![20, 140, -74, -85, -260],![-2, 150, -57, -86, -238],![-20, -67, 27, 36, 101]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-1110]],![[], [], [], [-246420], [75480, -1110]],![[], [], [-246420], [0, -49284], [57720, 15096, -222]],![[], [-1110], [75480, -1110], [57720, 15096, -222], [-36280, -4079, 136, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 5, 0], [98, -82, 57, 68, 222], [-32, 24, -17, -22, -68]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 5, 0], [490, -410, 285, 340, 1110], [-440, -150, 20, 25, 0], [20, 140, -74, -85, -260]], 
 ![[0, 0, 0, 1, 0], [98, -82, 57, 68, 222], [-440, -150, 20, 25, 0], [490, -498, 255, 360, 1110], [-2, 150, -57, -86, -238]], 
 ![[0, 0, 0, 0, 1], [-32, 24, -17, -22, -68], [20, 140, -74, -85, -260], [-2, 150, -57, -86, -238], [-20, -67, 27, 36, 101]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by native_decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by native_decide)

instance hp37: Fact $ Nat.Prime 37 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

noncomputable def D : CertificateDedekindAlmostAllLists T l [37, 2, 3, 5] where
 n := 4
 p := ![2, 3, 5, 37]
 exp := ![7, 7, 12, 2]
 pdgood := []
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp37.out
 a := [13516875000000, 4923281250000, 2075625000000, -559406250000]
 b := [85100625000000, -5265000000000, -2103468750000, -415125000000, 111881250000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 

noncomputable def M37 : MaximalOrderCertificateOfUnramifiedLists 37 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 5, 0], [24, 29, 20, 31, 0], [5, 24, 20, 15, 6]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 5, 0], [9, 34, 26, 7, 0], [4, 35, 20, 25, 0], [20, 29, 0, 26, 36]], 
![[0, 0, 0, 1, 0], [24, 29, 20, 31, 0], [4, 35, 20, 25, 0], [9, 20, 33, 27, 0], [35, 2, 17, 25, 21]], 
![[0, 0, 0, 0, 1], [5, 24, 20, 15, 6], [20, 29, 0, 26, 36], [35, 2, 17, 25, 21], [17, 7, 27, 36, 27]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![18, 31, 22, 11, 0],![23, 26, 25, 12, 0],![16, 2, 36, 19, 0],![13, 34, 20, 10, 1]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 1, 1, 0, 1],![0, 1, 1, 1, 0],![0, 0, 1, 0, 1],![0, 1, 0, 0, 1],![0, 0, 1, 1, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![19, 206],![352, 1145],![-6, 88],![-60, -122],![328, 1028]]
 c := ![![-136, 308, -496],![320, 2220, -3528],![-235, 86, -182],![58, -247, 452],![222, 1998, -3213]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t :=  2
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 2, 0], [2, 2, 0, 2, 0], [1, 0, 1, 2, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 2, 0], [1, 1, 0, 1, 0], [1, 0, 2, 1, 0], [2, 2, 1, 2, 1]], 
![[0, 0, 0, 1, 0], [2, 2, 0, 2, 0], [1, 0, 2, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 2]], 
![[0, 0, 0, 0, 1], [1, 0, 1, 2, 1], [2, 2, 1, 2, 1], [1, 0, 0, 1, 2], [1, 2, 0, 0, 2]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 2, 0, 0],![0, 1, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![2, 1, 0, 0, 1],![0, 2, 0, 0, 0]]
 v := ![![1, 0, 2, 0, 0],![0, 1, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![2, 1, 0, 0, 1],![0, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 2, 0, 1],![0, 0, 0, 1, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![2, 1, 2, 0, 0],![0, 2, 1, 1, 0],![0, 0, 1, 0, 1],![1, 1, 1, 0, 0],![2, 0, 2, 2, 2]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![628, 1560],![708, 1786],![135, 330],![330, 819],![966, 2442]]
 c := ![![-2922, 1554, -1371],![-3444, 1776, -1602],![-587, 330, -282],![-1524, 814, -717],![-4758, 2436, -2204]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M5 : MaximalOrderCertificateWLists 5 O Om hm where
 m := 4
 n := 1
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [3, 3, 2, 3, 2], [3, 4, 3, 3, 2]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [3, 3, 2, 3, 2], [0, 0, 0, 0, 0], [0, 2, 0, 0, 0], [3, 0, 3, 4, 2]], 
![[0, 0, 0, 0, 1], [3, 4, 3, 3, 2], [0, 0, 1, 0, 0], [3, 0, 3, 4, 2], [0, 3, 2, 1, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 0, 4],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 4],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0]]
 v_ind := ![0, 1, 2, 3]
 w_ind := ![0]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![6, 4, 4, 0, 6],![4, 4, 4, 8, 6],![2, 2, 8, 2, 8],![2, 0, 4, 4, 6],![0, 0, 2, 0, 0]]
 w1 := ![1, 1, 1, 0]
 w2 := ![1]
 a := ![![-73, 390, -180, -90],![-1535, 3332, -1390, -2050],![-195, 1310, -338, -320],![-535, 1450, -520, -738],![35, 300, -10, 10]]
 c := ![![265],![-5],![615],![175],![221]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
 hacindw := by native_decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [37, 2, 3, 5]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 37 O Om hm M37
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateWLists 5 O Om hm M5
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [37, 2, 3, 5] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
