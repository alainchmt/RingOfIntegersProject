
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible102

-- Number field with label 5.1.1822500000.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 70*X^2 - 30*X - 732 
lemma T_def : T = X^5 + 15*X^3 - 70*X^2 - 30*X - 732 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-732, -30, -70, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/8*a^4 + 1/8*a^3 - 1/2*a^2 + 1/4*a - 1/2] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  8
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![8, 0, 0, 0, 0], ![0, 8, 0, 0, 0], ![0, 0, 8, 0, 0], ![0, 0, -4, 4, 0], ![-4, 2, -4, 1, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 1, 2, 0],![2, -1, 1, -2, 4],![92, 3, 7, -5, 1]], 
![![0, 0, 1, 0, 0],![0, 0, 1, 2, 0],![4, -2, 3, -2, 8],![364, 16, 26, -14, -4],![82, 100, 12, 19, -19]], 
![![0, 0, 0, 1, 0],![2, -1, 1, -2, 4],![364, 16, 26, -14, -4],![-380, 175, -13, 57, -28],![-896, -47, -7, 31, 38]], 
![![0, 0, 0, 0, 1],![92, 3, 7, -5, 1],![82, 100, 12, 19, -19],![-896, -47, -7, 31, 38],![444, -251, 56, -57, 64]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-8]],![[], [], [], [-32], [-8, -8]],![[], [], [-32], [32, -16], [80, 0, -4]],![[], [-8], [-8, -8], [80, 0, -4], [-36, 22, -2, -1]]]
 h := Adj
 honed := by decide!
 hd := by norm_num
 hcc := by decide 
 hin := by decide
 hsymma := by decide
 hc_le := by decide! 

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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [2, -1, 1, -2, 4], [92, 3, 7, -5, 1]], 
 ![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [4, -2, 3, -2, 8], [364, 16, 26, -14, -4], [82, 100, 12, 19, -19]], 
 ![[0, 0, 0, 1, 0], [2, -1, 1, -2, 4], [364, 16, 26, -14, -4], [-380, 175, -13, 57, -28], [-896, -47, -7, 31, 38]], 
 ![[0, 0, 0, 0, 1], [92, 3, 7, -5, 1], [82, 100, 12, 19, -19], [-896, -47, -7, 31, 38], [444, -251, 56, -57, 64]]]

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
 f := [244, 10, 24, -4, 1]
 g :=  [0, 2, 1]
 h :=  [0, 1, 1, 1]
 a :=  [1, 1]
 b :=  [2, 0, 2, 2]
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
 f := [147, 8, 17, -1, 1]
 g :=  [3, 1]
 h :=  [1, 3, 4, 2, 1]
 a :=  [4]
 b :=  [1, 4, 1, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 3
 p := ![2, 3, 5]
 exp := ![13, 6, 7]
 pdgood := [3, 5]
 hsub := by decide!
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-1458000000, -3726000000, 1701000000, 81000000]
 b := [20023200000, -1069200000, 648000000, -340200000, -16200000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 1, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 0, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1], [0, 1, 1, 1, 0], [0, 1, 0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![0, 0, 0, 0, 1],![1, 1, 0, 0, 1],![1, 0, 0, 0, 1],![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![49, 56],![46, 65],![50, 56],![78, 46],![18, 78]]
 c := ![![-180, -68, -104],![-132, -74, -94],![-179, -68, -104],![-770, -37, -84],![-594, -16, -19]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 


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
    
