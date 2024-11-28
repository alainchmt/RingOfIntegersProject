
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible22

-- Number field with label 5.1.40500000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 75*X - 300 
lemma T_def : T = X^5 + 75*X - 300 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-300, 75, 0, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/10*a^3 - 1/2*a, 1/80*a^4 - 3/80*a^3 + 5/16*a^2 + 1/16*a - 1/4] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  80
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![80, 0, 0, 0, 0], ![0, 80, 0, 0, 0], ![0, 0, 80, 0, 0], ![0, -40, 0, 8, 0], ![-20, 5, 25, -3, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 5, 0, 10, 0],![2, 1, -3, 3, 8],![3, 0, 1, 2, -3]], 
![![0, 0, 1, 0, 0],![0, 5, 0, 10, 0],![20, 10, -25, 30, 80],![30, -10, 0, -5, 0],![-5, 10, -9, 10, 25]], 
![![0, 0, 0, 1, 0],![2, 1, -3, 3, 8],![30, -10, 0, -5, 0],![-2, 2, 2, -3, -8],![8, -4, 0, -2, 2]], 
![![0, 0, 0, 0, 1],![3, 0, 1, 2, -3],![-5, 10, -9, 10, 25],![8, -4, 0, -2, 2],![-5, 6, -3, 4, 6]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-80]],![[], [], [], [-640], [240, -80]],![[], [], [-640], [0, -64], [-160, 24, -8]],![[], [-80], [240, -80], [-160, 24, -8], [140, -59, 6, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 5, 0, 10, 0], [2, 1, -3, 3, 8], [3, 0, 1, 2, -3]], 
 ![[0, 0, 1, 0, 0], [0, 5, 0, 10, 0], [20, 10, -25, 30, 80], [30, -10, 0, -5, 0], [-5, 10, -9, 10, 25]], 
 ![[0, 0, 0, 1, 0], [2, 1, -3, 3, 8], [30, -10, 0, -5, 0], [-2, 2, 2, -3, -8], [8, -4, 0, -2, 2]], 
 ![[0, 0, 0, 0, 1], [3, 0, 1, 2, -3], [-5, 10, -9, 10, 25], [8, -4, 0, -2, 2], [-5, 6, -3, 4, 6]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [100, -25]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [1]
 b :=  [1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 5] where
 n := 3
 p := ![2, 3, 5]
 exp := ![15, 4, 10]
 pdgood := [3]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-84375000000, -16875000000, -3375000000, -675000000]
 b := [8100000000, 16875000000, 3375000000, 675000000, 135000000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 0, 1], [0, 0, 0, 0, 0], [1, 0, 1, 0, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 1, 0, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![1, 0, 1, 0, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 1, 1, 1, 0],![1, 0, 1, 1, 1],![0, 1, 1, 0, 1],![1, 1, 0, 0, 1],![0, 1, 1, 0, 0]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![209, -270],![260, -343],![230, -302],![46, -58],![182, -236]]
 c := ![![-48, 154, 60],![-78, 198, 64],![-99, 192, 76],![-24, 49, 26],![-72, 146, 61]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [2, 1, 2, 3, 3], [3, 0, 1, 2, 2]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [2, 1, 2, 3, 3], [0, 0, 0, 0, 0], [3, 2, 2, 2, 2], [3, 1, 0, 3, 2]], 
![[0, 0, 0, 0, 1], [3, 0, 1, 2, 2], [0, 0, 1, 0, 0], [3, 1, 0, 3, 2], [0, 1, 2, 4, 1]]]
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
 g := ![![3, 0, 1, 1, 3],![4, 3, 3, 3, 1],![4, 2, 0, 1, 1],![0, 1, 4, 0, 1],![0, 0, 1, 0, 0]]
 w1 := ![1, 1, 1, 0]
 w2 := ![1]
 a := ![![91, 135, -115, 160],![155, 161, -175, 310],![15, 35, -9, 60],![190, 265, -235, 366],![45, 55, -55, 80]]
 c := ![![-15],![15],![15],![-40],![-9]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
 hacindw := by native_decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 5]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 5 O Om hm M5
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 5] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
