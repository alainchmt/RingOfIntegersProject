import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 40*X^3 - 10*X^2 - 15*X - 8 : ℤ[X])

local notation "l" => [-8, -15, -10, -40, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp13' : Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)

def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [5, 11, 3, 12, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 0, 1, 1]
 hbits := by native_decide
 h := ![[0, 1], [11, 5, 2, 10, 7], [5, 2, 8, 7, 10], [8, 1, 1, 4, 2], [2, 4, 2, 5, 7], [0, 1]]
 g := ![![[3, 8, 1, 7, 1], [0, 1], []],![[3, 1, 8, 11, 12, 1, 7, 6], [1, 11, 5, 4], [12, 5, 12, 8, 0, 7, 1, 5]],![[0, 8, 1, 7, 10, 11, 8, 1], [1, 12, 0, 9], [8, 9, 10, 0, 10, 8, 7, 12]],![[9, 0, 7, 2, 8, 3, 11, 6], [6, 12, 5, 1], [7, 11, 0, 4, 5, 12, 9, 8]],![[4, 4, 4, 7, 2, 5, 1, 11], [7, 5, 7, 10], [6, 8, 5, 10, 7, 5, 7, 5]]]
 h' := ![![[11, 5, 2, 10, 7], [0, 8, 2, 10, 1], [0, 0, 0, 1], [0, 1]],![[5, 2, 8, 7, 10], [4, 9, 2, 7, 8], [10, 7, 9, 2, 11], [11, 5, 2, 10, 7]],![[8, 1, 1, 4, 2], [5, 11, 4, 7, 11], [7, 4, 6, 0, 10], [5, 2, 8, 7, 10]],![[2, 4, 2, 5, 7], [12, 5, 12, 9, 9], [9, 8, 9, 4, 12], [8, 1, 1, 4, 2]],![[0, 1], [7, 6, 6, 6, 10], [4, 7, 2, 6, 6], [2, 4, 2, 5, 7]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [3, 9, 0, 1], [], [], []]
 b := ![[], [7, 1, 11, 1, 11], [], [], []]
 hhz := by native_decide
 hhn := by native_decide
 hgcd := by native_decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 5
 hprim := by native_decide
 hdeg := by native_decide
 hnn := by native_decide
 hdn := by native_decide
 p := ![13]
 hp := by 
  intro i
  fin_cases i
  exact hp13'.out
 hlc := by native_decide
 m := ![1]
 F := fun i =>
  match i with 
  | 0 => ![[5, 11, 3, 12, 0, 1]]
 D := fun i =>
  match i with 
  | 0 => ![5]
 hl := by native_decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P0
 hm := by native_decide
 hprod := by native_decide
 hinter := by native_decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
