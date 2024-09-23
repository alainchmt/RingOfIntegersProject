
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible51

-- Number field with label 5.1.281250000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 25*X^3 + 250*X - 300 
lemma T_def : T = X^5 - 25*X^3 + 250*X - 300 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-300, 250, 0, -25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/5*a^3, 1/10*a^4 - 1/2*a^2] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  10
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![10, 0, 0, 0, 0], ![0, 10, 0, 0, 0], ![0, 0, 10, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, -5, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 5, 0],![0, 0, 1, 0, 2],![30, -25, 0, 10, 0]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 5, 0],![0, 0, 5, 0, 10],![60, -50, 0, 25, 0],![0, 30, -15, 0, 20]], 
![![0, 0, 0, 1, 0],![0, 0, 1, 0, 2],![60, -50, 0, 25, 0],![0, 12, -5, 0, 10],![120, -100, 6, 25, 0]], 
![![0, 0, 0, 0, 1],![30, -25, 0, 10, 0],![0, 30, -15, 0, 20],![120, -100, 6, 25, 0],![0, 45, -30, 15, 15]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-10]],![[], [], [], [-20], [0, -10]],![[], [], [-20], [0, -4], [-40, 0, -2]],![[], [-10], [0, -10], [-40, 0, -2], [0, -15, 0, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 5, 0], [0, 0, 1, 0, 2], [30, -25, 0, 10, 0]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 5, 0], [0, 0, 5, 0, 10], [60, -50, 0, 25, 0], [0, 30, -15, 0, 20]], 
 ![[0, 0, 0, 1, 0], [0, 0, 1, 0, 2], [60, -50, 0, 25, 0], [0, 12, -5, 0, 10], [120, -100, 6, 25, 0]], 
 ![[0, 0, 0, 0, 1], [30, -25, 0, 10, 0], [0, 30, -15, 0, 20], [120, -100, 6, 25, 0], [0, 45, -30, 15, 15]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] rfl

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  2
 a' := []
 b' :=  [1]
 k := [0, 1]
 f := [100, -83, 0, 9]
 g :=  [0, 1, 0, 1]
 h :=  [1, 0, 1]
 a :=  [1, 1, 2]
 b :=  [1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 5] where
 n := 3
 p := ![2, 3, 5]
 exp := ![6, 2, 13]
 pdgood := [3]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-2343750000, 2343750000, 2343750000, 468750000]
 b := [0, 5156250000, 468750000, -468750000, -93750000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![1, 1, 1, 1, 0],![0, 1, 0, 0, 0],![1, 0, 1, 1, 1],![0, 1, 1, 0, 0],![0, 0, 1, 1, 0]]
 w1 := ![1, 1]
 w2 := ![0, 0, 1]
 a := ![![93, 4],![0, 5],![176, -4],![60, 10],![92, -2]]
 c := ![![90, 20, -108],![0, 2, 0],![255, 28, -272],![60, 7, -80],![90, 18, -109]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M5 : MaximalOrderCertificateWLists 5 O Om hm where
 m := 4
 n := 1
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 2], [0, 0, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 2], [0, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0]]
 v_ind := ![1, 2, 3, 4]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![0, 0, 2, 3, 0],![0, 0, 3, 0, 1],![1, 0, 2, 0, 4],![0, 3, 1, 0, 2],![0, 0, 3, 0, 0]]
 w1 := ![0, 1, 1, 0]
 w2 := ![0]
 a := ![![-214, -5, 125, 50],![-220, 6, 100, 50],![-380, -25, 151, 100],![-190, -10, 90, 56],![-150, 15, 75, 30]]
 c := ![![60],![60],![120],![60],![36]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
 hacindw := by decide 


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
    
