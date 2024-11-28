
import DedekindProject4.CertificateDedekind
import DedekindProject4.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import DedekindProject4.Degree5Examples.Irreducible53

-- Number field with label 5.1.337500000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 30*X^2 + 60*X - 216 
lemma T_def : T = X^5 + 15*X^3 - 30*X^2 + 60*X - 216 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-216, 60, -30, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/24*a^4 - 1/4*a^3 + 1/8*a^2 - 1/2] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  24
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![24, 0, 0, 0, 0], ![0, 24, 0, 0, 0], ![0, 0, 24, 0, 0], ![0, -12, 0, 12, 0], ![-12, 0, 3, -6, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![6, 3, -2, 6, 12],![6, -5, 2, -4, -6]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![12, 6, -3, 12, 24],![108, -38, 15, -16, 0],![-60, 26, -9, 4, -12]], 
![![0, 0, 0, 1, 0],![6, 3, -2, 6, 12],![108, -38, 15, -16, 0],![-51, 36, -2, -36, -102],![-27, 4, -4, 29, 63]], 
![![0, 0, 0, 0, 1],![6, -5, 2, -4, -6],![-60, 26, -9, 4, -12],![-27, 4, -4, 29, 63],![48, -18, 6, -20, -35]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-24]],![[], [], [], [-288], [144, -24]],![[], [], [-288], [0, -144], [156, 72, -12]],![[], [-24], [144, -24], [156, 72, -12], [-174, -27, 12, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [6, 3, -2, 6, 12], [6, -5, 2, -4, -6]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [12, 6, -3, 12, 24], [108, -38, 15, -16, 0], [-60, 26, -9, 4, -12]], 
 ![[0, 0, 0, 1, 0], [6, 3, -2, 6, 12], [108, -38, 15, -16, 0], [-51, 36, -2, -36, -102], [-27, 4, -4, 29, 63]], 
 ![[0, 0, 0, 0, 1], [6, -5, 2, -4, -6], [-60, 26, -9, 4, -12], [-27, 4, -4, 29, 63], [48, -18, 6, -20, -35]]]

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
 f := [44, -11, 7, -2, 1]
 g :=  [4, 1]
 h :=  [1, 1, 1, 1, 1]
 a :=  [4]
 b :=  [0, 1, 4, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![13, 5, 8]
 pdgood := [5]
 hsub := by decide!
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-3240000000, -810000000, 0, 270000000]
 b := [1296000000, 1620000000, -162000000, 0, -54000000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 1, 1], [0, 0, 0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 4]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![1, 1, 0, 1, 1],![0, 0, 1, 1, 1],![0, 1, 1, 1, 1],![0, 1, 1, 0, 0],![1, 1, 1, 1, 0]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![-3, 2],![-10, 13],![-2, 14],![10, 14],![-22, 22]]
 c := ![![8, 14, -10],![68, -10, -4],![67, -8, 2],![58, -19, 18],![112, -18, -15]]
 hmulw := by decide! 
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 1, 0, 0], [0, 1, 2, 2, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 0, 0, 0], [0, 1, 0, 2, 0], [0, 2, 0, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 1, 0, 0], [0, 1, 2, 2, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 2, 2, 0], [0, 2, 0, 1, 0], [0, 1, 2, 2, 0], [0, 0, 0, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 2]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 1, 2]]
 v_ind := ![1, 2, 3]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![4, 4, 4, 2, 2],![0, 2, 2, 0, 0],![4, 0, 0, 0, 2],![0, 0, 1, 2, 2],![0, 4, 4, 4, 2]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![284, -96, 102],![198, -62, 12],![-162, 54, -178],![9, -18, 96],![330, -126, 354]]
 c := ![![-192, -3],![-132, -24],![138, -51],![-8, 33],![-258, 89]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide 


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
    
