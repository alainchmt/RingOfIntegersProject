import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 25*X^3 - 350*X^2 + 1200*X + 320 : ℤ[X])

local notation "l" => [320, 1200, -350, -25, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp17' : Fact $ Nat.Prime 17 := fact_iff.2 (by norm_num)

def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [14, 10, 7, 9, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by native_decide
 h := ![[0, 1], [6, 8, 2, 8, 7], [14, 12, 2, 6, 8], [14, 9, 2, 3, 4], [0, 4, 11, 0, 15], [0, 1]]
 g := ![![[2, 4, 3, 9, 9], [10, 8, 0, 1], [], []],![[7, 1, 11, 6, 13, 7, 5, 3], [8, 14, 9, 16], [12, 6, 0, 13], [0, 8, 10, 15]],![[14, 15, 13, 10, 4, 5, 7, 13], [1, 16, 8, 8], [5, 2, 12, 2], [9, 2, 11, 13]],![[0, 7, 6, 3, 0, 12, 0, 15], [14, 9, 7, 4], [6, 3, 10, 8], [11, 0, 7, 16]],![[0, 12, 16, 11, 11, 6, 8, 2], [5, 11, 10, 8], [11, 10, 8, 4], [7, 5, 0, 4]]]
 h' := ![![[6, 8, 2, 8, 7], [13, 9, 3, 10, 3], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[14, 12, 2, 6, 8], [9, 10, 6, 1, 10], [6, 4, 9, 16, 4], [2, 1, 4, 0, 9], [6, 8, 2, 8, 7]],![[14, 9, 2, 3, 4], [7, 1, 15, 2, 12], [2, 12, 12, 11, 5], [2, 14, 14, 16, 11], [14, 12, 2, 6, 8]],![[0, 4, 11, 0, 15], [0, 8, 0, 13, 5], [14, 11, 15, 6, 2], [8, 6, 13, 16, 12], [14, 9, 2, 3, 4]],![[0, 1], [2, 6, 10, 8, 4], [15, 7, 15, 1, 5], [4, 13, 2, 2, 2], [0, 4, 11, 0, 15]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [4, 0, 15, 1], [], [], []]
 b := ![[], [5, 13, 3, 6, 12], [], [], []]
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
 p := ![17]
 hp := by 
  intro i
  fin_cases i
  exact hp17'.out
 hlc := by native_decide
 m := ![1]
 F := fun i =>
  match i with 
  | 0 => ![[14, 10, 7, 9, 0, 1]]
 D := fun i =>
  match i with 
  | 0 => ![5]
 hl := by native_decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
 hm := by native_decide
 hprod := by native_decide
 hinter := by native_decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
