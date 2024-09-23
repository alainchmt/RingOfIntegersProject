
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible135

-- Number field with label 5.1.15187500000.13 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 50*X^3 - 50*X^2 + 1125*X + 910 
lemma T_def : T = X^5 - 50*X^3 - 50*X^2 + 1125*X + 910 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [910, 1125, -50, -50, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/6*a^3 - 1/3*a^2 + 1/6*a - 1/3, 1/396*a^4 + 23/396*a^3 + 83/396*a^2 - 11/36*a - 37/198] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  396
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![396, 0, 0, 0, 0], ![0, 396, 0, 0, 0], ![0, 0, 396, 0, 0], ![-132, 66, -132, 66, 0], ![-74, -121, 83, 23, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![2, -1, 2, 6, 0],![4, 24, -22, -25, 66],![0, 5, -7, -6, 23]], 
![![0, 0, 1, 0, 0],![2, -1, 2, 6, 0],![28, 144, -129, -138, 396],![-144, -244, 68, 97, -132],![-38, -22, -38, -30, 133]], 
![![0, 0, 0, 1, 0],![4, 24, -22, -25, 66],![-144, -244, 68, 97, -132],![136, 328, -246, -241, 616],![-20, -1, -50, -37, 139]], 
![![0, 0, 0, 0, 1],![0, 5, -7, -6, 23],![-38, -22, -38, -30, 133],![-20, -1, -50, -37, 139],![-24, -12, -33, -25, 100]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-396]],![[], [], [], [-26136], [-9108, -396]],![[], [], [-26136], [17424, -4356], [-5808, -1386, -66]],![[], [-396], [-9108, -396], [-5808, -1386, -66], [-5926, -745, -46, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [2, -1, 2, 6, 0], [4, 24, -22, -25, 66], [0, 5, -7, -6, 23]], 
 ![[0, 0, 1, 0, 0], [2, -1, 2, 6, 0], [28, 144, -129, -138, 396], [-144, -244, 68, 97, -132], [-38, -22, -38, -30, 133]], 
 ![[0, 0, 0, 1, 0], [4, 24, -22, -25, 66], [-144, -244, 68, 97, -132], [136, 328, -246, -241, 616], [-20, -1, -50, -37, 139]], 
 ![[0, 0, 0, 0, 1], [0, 5, -7, -6, 23], [-38, -22, -38, -30, 133], [-20, -1, -50, -37, 139], [-24, -12, -33, -25, 100]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] rfl

instance hp11: Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-182, -225, 10, 10]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [2]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [3, 2, 11] where
 n := 4
 p := ![2, 3, 5, 11]
 exp := ![11, 11, 9, 2]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp11.out
 a := [-6096262500000, 14412937500000, 604462500000, -331087500000]
 b := [81143775000000, 1650577500000, -4206937500000, -120892500000, 66217500000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t :=  2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [2, 2, 2, 0, 0], [1, 0, 2, 2, 0], [0, 2, 2, 0, 2]], 
![[0, 0, 1, 0, 0], [2, 2, 2, 0, 0], [1, 0, 0, 0, 0], [0, 2, 2, 1, 0], [1, 2, 1, 0, 1]], 
![[0, 0, 0, 1, 0], [1, 0, 2, 2, 0], [0, 2, 2, 1, 0], [1, 1, 0, 2, 1], [1, 2, 1, 2, 1]], 
![[0, 0, 0, 0, 1], [0, 2, 2, 0, 2], [1, 2, 1, 0, 1], [1, 2, 1, 2, 1], [0, 0, 0, 2, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 2, 1, 2],![0, 1, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 v := ![![1, 0, 2, 1, 2],![0, 1, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i ; fin_cases i <;> rfl 
 hwFrobComp := by intro i ; fin_cases i <;> rfl 
 g := ![![1, 1, 0, 1, 1],![1, 1, 1, 2, 1],![2, 1, 2, 1, 2],![2, 1, 2, 2, 1],![0, 2, 2, 1, 2]]
 w1 := ![0, 1]
 w2 := ![0, 0, 1]
 a := ![![457, -498],![1260, -1628],![2256, -3357],![1986, -2802],![2289, -3393]]
 c := ![![-351, -63, -210],![-774, 216, -516],![-1028, 1083, -822],![-1026, 718, -756],![-1035, 1101, -839]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 1, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 0, 1], [0, 1, 0, 1, 1], [0, 0, 1, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
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
 g := ![![0, 1, 0, 0, 1],![1, 1, 0, 1, 1],![1, 0, 0, 1, 1],![0, 0, 1, 1, 1],![0, 1, 0, 1, 1]]
 w1 := ![0, 1]
 w2 := ![0, 0, 1]
 a := ![![1163, -292],![3738, -1011],![3446, -940],![3542, -904],![3738, -1012]]
 c := ![![-54, -562, -556],![68, -1480, -1814],![61, -1372, -1666],![-160, -1725, -1672],![68, -1480, -1815]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M11 : MaximalOrderCertificateOfUnramifiedLists 11 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [2, 10, 2, 6, 0], [4, 2, 0, 8, 0], [0, 5, 4, 5, 1]], 
![[0, 0, 1, 0, 0], [2, 10, 2, 6, 0], [6, 1, 3, 5, 0], [10, 9, 2, 9, 0], [6, 0, 6, 3, 1]], 
![[0, 0, 0, 1, 0], [4, 2, 0, 8, 0], [10, 9, 2, 9, 0], [4, 9, 7, 1, 0], [2, 10, 5, 7, 7]], 
![[0, 0, 0, 0, 1], [0, 5, 4, 5, 1], [6, 0, 6, 3, 1], [2, 10, 5, 7, 7], [9, 10, 0, 8, 1]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![1, 1, 9, 8, 0],![6, 0, 0, 4, 0],![4, 0, 3, 0, 0],![10, 0, 2, 3, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by intro i ; fin_cases i <;> rfl 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [3, 2, 11]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 11 O Om hm M11
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3, 2, 11] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
