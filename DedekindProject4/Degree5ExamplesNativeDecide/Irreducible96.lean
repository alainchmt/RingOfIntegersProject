import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 25*X^3 - 250*X^2 - 750*X - 1100 : ℤ[X])

local notation "l" => [-1100, -750, -250, -25, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp7' : Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [6, 6, 2, 3, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 1, 1]
 hbits := by native_decide
 h := ![[0, 1], [4, 4, 0, 3, 5], [5, 0, 2, 1], [5, 2, 1, 0, 2], [0, 0, 4, 3], [0, 1]]
 g := ![![[4, 0, 1], []],![[5, 2, 2, 4, 5, 1, 6, 3], [6, 2, 5, 5, 4, 5, 1, 6]],![[5, 4, 4, 3, 4, 6, 4], [1, 3, 2, 6, 1]],![[2, 2, 1, 2, 1, 2], [2, 0, 4, 5, 1, 2, 0, 1]],![[0, 1, 6, 3, 1, 5, 3], [0, 1, 0, 3, 6]]]
 h' := ![![[4, 4, 0, 3, 5], [0, 0, 0, 1], [0, 1]],![[5, 0, 2, 1], [0, 4, 5, 0, 3], [4, 4, 0, 3, 5]],![[5, 2, 1, 0, 2], [0, 4, 6, 4, 5], [5, 0, 2, 1]],![[0, 0, 4, 3], [1, 5, 2, 1], [5, 2, 1, 0, 2]],![[0, 1], [0, 1, 1, 1, 6], [0, 0, 4, 3]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [2, 4, 4, 6], [], [], []]
 b := ![[], [6, 4, 5, 3, 3], [], [], []]
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
 p := ![7]
 hp := by 
  intro i
  fin_cases i
  exact hp7'.out
 hlc := by native_decide
 m := ![1]
 F := fun i =>
  match i with 
  | 0 => ![[6, 6, 2, 3, 0, 1]]
 D := fun i =>
  match i with 
  | 0 => ![5]
 hl := by native_decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
 hm := by native_decide
 hprod := by native_decide
 hinter := by native_decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
