
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible30

-- Number field with label 5.1.67500000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 20*X^3 - 50*X^2 - 45*X - 26 
lemma T_def : T = X^5 - 20*X^3 - 50*X^2 - 45*X - 26 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-26, -45, -50, -20, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/4*a^4 - 1/4*a^3 - 1/4*a^2 - 1/4*a - 1/2] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  4
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![4, 0, 0, 0, 0], ![0, 4, 0, 0, 0], ![0, 0, 4, 0, 0], ![0, -2, 0, 2, 0], ![-2, -1, -1, -1, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![1, 1, 0, 1, 2],![6, 15, 12, 9, -1]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![2, 2, 1, 2, 4],![13, 32, 25, 19, 0],![3, 12, 3, 24, 19]], 
![![0, 0, 0, 1, 0],![1, 1, 0, 1, 2],![13, 32, 25, 19, 0],![9, 28, 16, 34, 18],![66, 150, 114, 96, 15]], 
![![0, 0, 0, 0, 1],![6, 15, 12, 9, -1],![3, 12, 3, 24, 19],![66, 150, 114, 96, 15],![57, 168, 102, 177, 81]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-4]],![[], [], [], [-8], [4, -4]],![[], [], [-8], [0, -4], [-36, 2, -2]],![[], [-4], [4, -4], [-36, 2, -2], [-10, -19, 2, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [1, 1, 0, 1, 2], [6, 15, 12, 9, -1]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [2, 2, 1, 2, 4], [13, 32, 25, 19, 0], [3, 12, 3, 24, 19]], 
 ![[0, 0, 0, 1, 0], [1, 1, 0, 1, 2], [13, 32, 25, 19, 0], [9, 28, 16, 34, 18], [66, 150, 114, 96, 15]], 
 ![[0, 0, 0, 0, 1], [6, 15, 12, 9, -1], [3, 12, 3, 24, 19], [66, 150, 114, 96, 15], [57, 168, 102, 177, 81]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [1]
 b' :=  [0, 2, 1]
 k := [1, 0, 2, 0, 1]
 f := [9, 16, 18, 8, 1]
 g :=  [1, 1, 1, 1]
 h :=  [1, 2, 1]
 a :=  [1, 2, 2]
 b :=  [1, 1, 2, 1]
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
 f := [6, 10, 11, 5, 1]
 g :=  [4, 1]
 h :=  [1, 1, 1, 1, 1]
 a :=  [2]
 b :=  [1, 1, 3, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 3
 p := ![2, 3, 5]
 exp := ![11, 3, 7]
 pdgood := [3, 5]
 hsub := by decide!
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-459000000, -171000000, -45000000, 27000000]
 b := [169200000, 181800000, 77400000, 9000000, -5400000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 1, 0], [0, 1, 0, 1, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 0, 1, 0], [1, 1, 0, 1, 0], [1, 0, 1, 1, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 1, 1], [1, 0, 1, 0, 1], [0, 0, 0, 0, 1], [1, 0, 0, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 0, 0, 1]]
 v := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![0, 1, 0, 0, 1],![1, 1, 1, 0, 0],![1, 1, 0, 0, 0],![0, 1, 1, 0, 0],![1, 0, 0, 1, 0]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![53, 42],![10, 5],![2, 4],![10, 4],![22, 26]]
 c := ![![-24, 8, 8],![-6, 2, 2],![-1, 0, 0],![-6, 1, 2],![-6, 6, 3]]
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
    
