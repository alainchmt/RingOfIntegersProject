
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible89

-- Number field with label 5.3.1215000000.5 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 170*X^2 + 120*X + 528 
lemma T_def : T = X^5 + 15*X^3 - 170*X^2 + 120*X + 528 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [528, 120, -170, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/76*a^4 - 3/38*a^3 - 25/76*a^2 - 5/19*a + 3/19] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  76
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![76, 0, 0, 0, 0], ![0, 76, 0, 0, 0], ![0, 0, 76, 0, 0], ![0, -38, 0, 38, 0], ![12, -20, -25, -6, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-6, 13, 12, 6, 38],![-6, -4, 0, -2, -6]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-12, 26, 25, 12, 76],![-264, -68, 85, -16, 0],![48, -8, -28, 0, -40]], 
![![0, 0, 0, 1, 0],![-6, 13, 12, 6, 38],![-264, -68, 85, -16, 0],![51, -200, -136, 34, -323],![123, 92, -4, 13, 123]], 
![![0, 0, 0, 0, 1],![-6, -4, 0, -2, -6],![48, -8, -28, 0, -40],![123, 92, -4, 13, 123],![-54, -16, 16, -6, -11]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-76]],![[], [], [], [-2888], [456, -76]],![[], [], [-2888], [0, -1444], [1558, 228, -38]],![[], [-76], [456, -76], [1558, 228, -38], [-610, 29, 12, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-6, 13, 12, 6, 38], [-6, -4, 0, -2, -6]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-12, 26, 25, 12, 76], [-264, -68, 85, -16, 0], [48, -8, -28, 0, -40]], 
 ![[0, 0, 0, 1, 0], [-6, 13, 12, 6, 38], [-264, -68, 85, -16, 0], [51, -200, -136, 34, -323], [123, 92, -4, 13, 123]], 
 ![[0, 0, 0, 0, 1], [-6, -4, 0, -2, -6], [48, -8, -28, 0, -40], [123, 92, -4, 13, 123], [-54, -16, 16, -6, -11]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] rfl

instance hp19: Fact $ Nat.Prime 19 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [2]
 b' :=  [1, 2]
 k := [0, 1]
 f := [-176, -40, 57, -4, 1]
 g :=  [0, 1, 1]
 h :=  [0, 1, 2, 1]
 a :=  [1]
 b :=  [1, 2, 2]
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
 f := [-105, -22, 37, -1, 1]
 g :=  [3, 1]
 h :=  [1, 3, 4, 2, 1]
 a :=  [3]
 b :=  [2, 3, 2, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 19] where
 n := 4
 p := ![2, 3, 5, 19]
 exp := ![12, 5, 7, 2]
 pdgood := [3, 5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp19.out
 a := [973944000000, -2324187000000, -385668000000, -122283000000]
 b := [-4051425600000, -2226560400000, 611577000000, 77133600000, 24456600000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 1]], 
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [1, 0, 0, 1, 1], [0, 0, 0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 0, 1, 0]]
 v := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 4]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![0, 1, 0, 1, 1],![1, 1, 1, 0, 1],![0, 1, 0, 1, 0],![0, 1, 1, 0, 0],![1, 0, 0, 1, 1]]
 w1 := ![1, 1]
 w2 := ![1, 1, 0]
 a := ![![3, -20],![126, 85],![-54, -4],![68, 100],![-28, -34]]
 c := ![![-40, -24, 28],![-74, -30, -58],![-89, -60, 56],![-124, -67, -30],![-30, -22, 41]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M19 : MaximalOrderCertificateOfUnramifiedLists 19 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [13, 13, 12, 6, 0], [13, 15, 0, 17, 13]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [7, 7, 6, 12, 0], [2, 8, 9, 3, 0], [10, 11, 10, 0, 17]], 
![[0, 0, 0, 1, 0], [13, 13, 12, 6, 0], [2, 8, 9, 3, 0], [13, 9, 16, 15, 0], [9, 16, 15, 13, 9]], 
![[0, 0, 0, 0, 1], [13, 15, 0, 17, 13], [10, 11, 10, 0, 17], [9, 16, 15, 13, 9], [3, 3, 16, 13, 8]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![17, 14, 8, 17, 0],![16, 10, 13, 16, 0],![11, 14, 13, 12, 0],![3, 17, 7, 5, 18]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by intro i ; fin_cases i <;> rfl 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 19]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 19 O Om hm M19
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 19] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
