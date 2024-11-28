
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [12, 5, 2, 24, 0], [-9, -6, 0, -5, 21], [-54, -15, 1, 6, 3]], 
 ![[0, 0, 1, 0, 0], [12, 5, 2, 24, 0], [-192, -122, 9, -72, 504], [-1089, -294, 15, 151, -42], [-204, -130, -10, 12, 135]], 
 ![[0, 0, 0, 1, 0], [-9, -6, 0, -5, 21], [-1089, -294, 15, 151, -42], [138, -28, -14, -39, 126], [-285, -84, 0, 19, 15]], 
 ![[0, 0, 0, 0, 1], [-54, -15, 1, 6, 3], [-204, -130, -10, 12, 135], [-285, -84, 0, 19, 15], [-130, -54, -3, 6, 26]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

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
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
 a := [10100440800000000, -2188749600000000, -131220000000000, 29743200000000]
 b := [-33907248000000000, -3237809760000000, 794668320000000, 26244000000000, -5948640000000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 0, 1, 1, 0], [0, 0, 0, 1, 0], [1, 0, 0, 1, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 0, 1], [1, 0, 0, 1, 1], [0, 0, 1, 0, 0]]]
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
 g := ![![1, 0, 1, 1, 1],![1, 1, 0, 1, 0],![1, 1, 0, 0, 0],![0, 1, 1, 0, 0],![1, 0, 0, 0, 1]]
 w1 := ![1, 1]
 w2 := ![0, 1, 1]
 a := ![![1221, 0],![358, -5],![42, 8],![706, 32],![240, -12]]
 c := ![![-2674, -1580, 252],![-762, -464, 62],![-57, -38, 14],![-1428, -849, 176],![-598, -344, 41]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t :=  2
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 2, 2, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 2]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 0, 2],![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 2],![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 0, 0]]
 v_ind := ![0, 1, 3]
 w_ind := ![0, 1]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![4, 4, 4, 8, 0],![4, 4, 8, 8, 8],![8, 8, 8, 8, 4],![2, 0, 0, 0, 4],![0, 2, 1, 0, 0]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![3406, 150, 3156],![7314, 130, 4728],![6654, 198, 4564],![720, -36, 390],![645, 27, 309]]
 c := ![![-10782, -1647],![-18030, -2895],![-16158, -2547],![-2014, -363],![-876, -140]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by native_decide 

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [5, 5, 2, 3, 0], [5, 1, 0, 2, 0], [2, 6, 1, 6, 3]], 
![[0, 0, 1, 0, 0], [5, 5, 2, 3, 0], [4, 4, 2, 5, 0], [3, 0, 1, 4, 0], [6, 3, 4, 5, 2]], 
![[0, 0, 0, 1, 0], [5, 1, 0, 2, 0], [3, 0, 1, 4, 0], [5, 0, 0, 3, 0], [2, 0, 0, 5, 1]], 
![[0, 0, 0, 0, 1], [2, 6, 1, 6, 3], [6, 3, 4, 5, 2], [2, 0, 0, 5, 1], [3, 2, 4, 6, 5]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![1, 5, 3, 4, 6]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

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
    
