
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible141

-- Number field with label 5.1.91125000000.16 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 150*X^3 - 100*X^2 + 8025*X + 28260 
lemma T_def : T = X^5 - 150*X^3 - 100*X^2 + 8025*X + 28260 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [28260, 8025, -100, -150, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/24*a^3 - 1/12*a^2 - 5/24*a - 1/2, 1/504*a^4 + 1/168*a^3 - 5/168*a^2 + 107/504*a + 13/42] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  504
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![504, 0, 0, 0, 0], ![0, 504, 0, 0, 0], ![0, 0, 504, 0, 0], ![-252, -105, -42, 21, 0], ![156, 107, -15, 3, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![12, 5, 2, 24, 0],![-9, -6, 0, -5, 21],![-54, -15, 1, 6, 3]], 
![![0, 0, 1, 0, 0],![12, 5, 2, 24, 0],![-192, -122, 9, -72, 504],![-1089, -294, 15, 151, -42],![-204, -130, -10, 12, 135]], 
![![0, 0, 0, 1, 0],![-9, -6, 0, -5, 21],![-1089, -294, 15, 151, -42],![138, -28, -14, -39, 126],![-285, -84, 0, 19, 15]], 
![![0, 0, 0, 0, 1],![-54, -15, 1, 6, 3],![-204, -130, -10, 12, 135],![-285, -84, 0, 19, 15],![-130, -54, -3, 6, 26]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-504]],![[], [], [], [-10584], [-1512, -504]],![[], [], [-10584], [1764, -441], [-2604, -21, -21]],![[], [-504], [-1512, -504], [-2604, -21, -21], [-1124, -129, -6, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [12, 5, 2, 24, 0], [-9, -6, 0, -5, 21], [-54, -15, 1, 6, 3]], 
 ![[0, 0, 1, 0, 0], [12, 5, 2, 24, 0], [-192, -122, 9, -72, 504], [-1089, -294, 15, 151, -42], [-204, -130, -10, 12, 135]], 
 ![[0, 0, 0, 1, 0], [-9, -6, 0, -5, 21], [-1089, -294, 15, 151, -42], [138, -28, -14, -39, 126], [-285, -84, 0, 19, 15]], 
 ![[0, 0, 0, 0, 1], [-54, -15, 1, 6, 3], [-204, -130, -10, 12, 135], [-285, -84, 0, 19, 15], [-130, -54, -3, 6, 26]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] rfl

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-5652, -1605, 20, 30]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [2]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![18, 12, 9, 2]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
 a := [10100440800000000, -2188749600000000, -131220000000000, 29743200000000]
 b := [-33907248000000000, -3237809760000000, 794668320000000, 26244000000000, -5948640000000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 0, 1, 1, 0], [0, 0, 0, 1, 0], [1, 0, 0, 1, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 0, 1], [1, 0, 0, 1, 1], [0, 0, 1, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![1, 0, 1, 1, 1],![1, 1, 1, 1, 1],![1, 1, 0, 0, 0],![0, 1, 1, 0, 0],![1, 0, 0, 0, 1]]
 w1 := ![1, 1]
 w2 := ![1, 0, 0]
 a := ![![983, -6],![984, -1],![2, 6],![782, -2],![208, -14]]
 c := ![![-1386, -1040, 96],![-1434, -1052, 114],![-47, -12, 18],![-342, -591, 6],![-258, -230, 15]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t :=  2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 2, 2, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 0, 2],![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 2],![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 0, 0]]
 v_ind := ![0, 1, 3]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![2, 2, 0, 2, 2],![1, 0, 0, 2, 2],![4, 4, 4, 2, 2],![1, 0, 0, 0, 2],![0, 2, 1, 0, 0]]
 w1 := ![1, 0, 1]
 w2 := ![0, 1]
 a := ![![397, -6, 90],![369, -14, 75],![882, 18, 1382],![87, 0, 135],![141, 12, 333]]
 c := ![![-1113, -180],![-1026, -168],![-3252, -543],![-608, -93],![-600, -101]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide 

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [5, 5, 2, 3, 0], [5, 1, 0, 2, 0], [2, 6, 1, 6, 3]], 
![[0, 0, 1, 0, 0], [5, 5, 2, 3, 0], [4, 4, 2, 5, 0], [3, 0, 1, 4, 0], [6, 3, 4, 5, 2]], 
![[0, 0, 0, 1, 0], [5, 1, 0, 2, 0], [3, 0, 1, 4, 0], [5, 0, 0, 3, 0], [2, 0, 0, 5, 1]], 
![[0, 0, 0, 0, 1], [2, 6, 1, 6, 3], [6, 3, 4, 5, 2], [2, 0, 0, 5, 1], [3, 2, 4, 6, 5]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![1, 5, 3, 4, 6]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by intro i ; fin_cases i <;> rfl 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3, 7]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 7] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
