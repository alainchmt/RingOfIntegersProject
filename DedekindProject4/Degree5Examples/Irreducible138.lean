import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 + 90*X^3 - 120*X^2 + 2160*X - 5184 : ℤ[X])

local notation "l" => [-5184, 2160, -120, 90, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp7 : Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [3, 4, 6, 6, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 3, 5, 4, 1], [6, 6, 1, 1, 2], [0, 6, 2, 1, 3], [4, 5, 6, 1, 1], [0, 1]]
 g := ![![[1, 0, 1], []],![[3, 3, 1, 0, 5, 0, 1, 4], [6, 5, 2, 2, 3, 1, 5, 1]],![[4, 2, 6, 3, 3, 3, 4, 4], [3, 5, 0, 5, 0, 5, 5, 1]],![[1, 5, 2, 5, 5, 3, 2, 5], [3, 4, 1, 5, 1, 6, 6, 6]],![[5, 3, 0, 3, 3, 3, 0, 2], [6, 5, 5, 0, 0, 1, 3, 1]]]
 h' := ![![[4, 3, 5, 4, 1], [0, 0, 0, 1], [0, 1]],![[6, 6, 1, 1, 2], [4, 0, 6, 2, 5], [4, 3, 5, 4, 1]],![[0, 6, 2, 1, 3], [4, 5, 4, 1, 4], [6, 6, 1, 1, 2]],![[4, 5, 6, 1, 1], [5, 4, 5, 1, 2], [0, 6, 2, 1, 3]],![[0, 1], [4, 5, 6, 2, 3], [4, 5, 6, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4, 6], [], [], []]
 b := ![[], [5, 2, 6, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 5
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![7]
 hp := by 
  intro i
  fin_cases i
  exact hp7.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with 
  | 0 => ![[3, 4, 6, 6, 0, 1]]
 D := fun i =>
  match i with 
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
 hm := by decide
 hprod := by decide
 hinter := by decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
