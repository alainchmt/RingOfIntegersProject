
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5ExamplesNativeDecide.Irreducible90

-- Number field with label 5.1.1215000000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 10*X^3 - 80*X^2 + 345*X - 448 
lemma T_def : T = X^5 - 10*X^3 - 80*X^2 + 345*X - 448 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-448, 345, -80, -10, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 - 1/4*a, 1/48*a^4 + 5/48*a^3 - 3/16*a^2 + 19/48*a - 1/3] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  48
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![48, 0, 0, 0, 0], ![0, 48, 0, 0, 0], ![0, -24, 24, 0, 0], ![0, -12, 0, 12, 0], ![-16, 19, -9, 5, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 1, 2, 0, 0],![0, 0, -1, 2, 0],![4, -4, 4, -5, 12],![11, -7, 6, -2, 5]], 
![![0, 0, 1, 0, 0],![0, 0, -1, 2, 0],![4, -4, 5, -7, 12],![54, -30, 18, 7, -6],![18, -8, -2, 7, -2]], 
![![0, 0, 0, 1, 0],![4, -4, 4, -5, 12],![54, -30, 18, 7, -6],![8, 4, -34, 10, 24],![12, -6, 0, -14, 36]], 
![![0, 0, 0, 0, 1],![11, -7, 6, -2, 5],![18, -8, -2, 7, -2],![12, -6, 0, -14, 36],![31, -18, 15, -9, 18]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-48]],![[], [], [], [-288], [-96, -24]],![[], [], [-288], [0, -144], [0, -60, -12]],![[], [-48], [-96, -24], [0, -60, -12], [-128, -17, -10, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 0, -1, 2, 0], [4, -4, 4, -5, 12], [11, -7, 6, -2, 5]], 
 ![[0, 0, 1, 0, 0], [0, 0, -1, 2, 0], [4, -4, 5, -7, 12], [54, -30, 18, 7, -6], [18, -8, -2, 7, -2]], 
 ![[0, 0, 0, 1, 0], [4, -4, 4, -5, 12], [54, -30, 18, 7, -6], [8, 4, -34, 10, 24], [12, -6, 0, -14, 36]], 
 ![[0, 0, 0, 0, 1], [11, -7, 6, -2, 5], [18, -8, -2, 7, -2], [12, -6, 0, -14, 36], [31, -18, 15, -9, 18]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [90, -68, 18, 4, 1]
 g :=  [2, 1]
 h :=  [1, 2, 4, 3, 1]
 a :=  [3]
 b :=  [3, 3, 4, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![20, 7, 7]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-1255824000000, -203472000000, 16848000000, 22032000000]
 b := [-1111449600000, 476150400000, 58320000000, -3369600000, -4406400000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
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
![[0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 1, 0, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [1, 1, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [1, 0, 1, 1, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 1, 0, 1],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 v := ![![1, 0, 1, 0, 1],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 1, 0]]
 v_ind := ![0, 3]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 0, 1, 0, 0],![1, 0, 0, 1, 1],![0, 1, 1, 1, 1],![1, 0, 1, 1, 1],![0, 0, 0, 1, 0]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![5, 12],![142, -25],![162, -20],![146, -14],![78, -6]]
 c := ![![36, -20, 8],![12, -42, -62],![47, -68, -56],![48, -63, -54],![2, -20, -43]]
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
![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 0, 2, 2, 0], [1, 2, 1, 1, 0], [2, 2, 0, 1, 2]], 
![[0, 0, 1, 0, 0], [0, 0, 2, 2, 0], [1, 2, 2, 2, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 1]], 
![[0, 0, 0, 1, 0], [1, 2, 1, 1, 0], [0, 0, 0, 1, 0], [2, 1, 2, 1, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 0, 1], [2, 2, 0, 1, 2], [0, 1, 1, 1, 1], [0, 0, 0, 1, 0], [1, 0, 0, 0, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 2, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![1, 2, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 0, 0, 0, 1]]
 v_ind := ![0, 3]
 w_ind := ![0, 1, 4]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 2, 0, 1, 1],![1, 1, 1, 2, 1],![2, 2, 1, 2, 2],![0, 0, 2, 0, 1],![0, 2, 1, 2, 1]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![58, -30],![69, -23],![111, -42],![66, 3],![81, -27]]
 c := ![![39, -69, 54],![81, -102, 78],![97, -144, 102],![45, -83, 24],![78, -111, 82]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
