import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 + 75*X^3 - 150*X^2 + 150*X - 780 : ℤ[X])

local notation "l" => [-780, 150, -150, 75, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp29' : Fact $ Nat.Prime 29 := fact_iff.2 (by norm_num)

def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [3, 5, 24, 17, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by native_decide
 h := ![[0, 1], [25, 9, 21, 18], [28, 2, 26, 22, 26], [1, 12, 22, 27, 11], [4, 5, 18, 20, 21], [0, 1]]
 g := ![![[11, 9, 14, 9, 23], [6, 7, 27, 25], [12, 0, 1], []],![[28, 24, 17, 14, 21, 0, 19], [24, 10, 12, 20], [2, 10, 17, 6, 4, 15, 27], [6, 0, 2, 25, 3]],![[21, 15, 25, 25, 21, 24, 17, 26], [5, 11, 0, 1], [17, 4, 27, 23, 27, 16, 18, 3], [16, 23, 5, 22, 4, 24, 14, 2]],![[0, 26, 10, 16, 19, 0, 24, 8], [10, 6, 1, 5], [28, 5, 3, 14, 14, 18, 4, 12], [9, 23, 11, 11, 25, 20, 28, 26]],![[2, 6, 14, 17, 3, 27, 25, 27], [14, 25, 28, 25], [14, 2, 23, 2, 18, 1, 13, 18], [22, 7, 19, 9, 23, 8, 12, 10]]]
 h' := ![![[25, 9, 21, 18], [2, 6, 19, 14, 20], [22, 27, 28, 23, 5], [0, 0, 0, 1], [0, 1]],![[28, 2, 26, 22, 26], [28, 22, 6, 13, 15], [10, 26, 17, 5, 7], [5, 25, 2, 2, 4], [25, 9, 21, 18]],![[1, 12, 22, 27, 11], [9, 0, 15, 25, 1], [13, 0, 14, 0, 1], [9, 2, 16, 7, 17], [28, 2, 26, 22, 26]],![[4, 5, 18, 20, 21], [27, 13, 16, 18, 8], [12, 7, 10, 4, 11], [3, 9, 18, 19, 26], [1, 12, 22, 27, 11]],![[0, 1], [25, 17, 2, 17, 14], [3, 27, 18, 26, 5], [27, 22, 22, 0, 11], [4, 5, 18, 20, 21]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [22, 20, 12], [], [], []]
 b := ![[], [9, 17, 8, 19, 9], [], [], []]
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
 p := ![29]
 hp := by 
  intro i
  fin_cases i
  exact hp29'.out
 hlc := by native_decide
 m := ![1]
 F := fun i =>
  match i with 
  | 0 => ![[3, 5, 24, 17, 0, 1]]
 D := fun i =>
  match i with 
  | 0 => ![5]
 hl := by native_decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P0
 hm := by native_decide
 hprod := by native_decide
 hinter := by native_decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
