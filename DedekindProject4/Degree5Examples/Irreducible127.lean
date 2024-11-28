import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 75*X^3 - 50*X^2 + 2250*X + 5820 : ℤ[X])

local notation "l" => [5820, 2250, -50, -75, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp7' : Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp13' : Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[5, 2], [3, 1]],![[4, 5], [6, 6]]]
 h' := ![![[3, 6], [6, 4], [0, 1]],![[0, 1], [4, 3], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 3 2 2 [2, 6, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 2], [1, 4, 5], [0, 1]]
 g := ![![[2, 2, 2], [1]],![[1, 4, 3, 4], [0, 5, 0, 1]],![[1, 2, 5, 5], [6, 0, 2, 6]]]
 h' := ![![[3, 2, 2], [5, 1, 4], [0, 1]],![[1, 4, 5], [6, 2, 4], [3, 2, 2]],![[0, 1], [3, 4, 6], [1, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 5], []]
 b := ![[], [1, 3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P13P1 : CertificateIrreducibleZModOfList' 13 4 2 3 [1, 0, 6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 6, 3], [9, 2, 1, 2], [0, 10, 6, 8], [0, 1]]
 g := ![![[0, 9, 5, 9], [10, 9, 1], []],![[4, 11, 8, 1, 3, 12], [5, 10, 3], [7, 8, 4, 11, 2, 1]],![[9, 7, 9, 0, 11, 11], [0, 11, 12], [6, 11, 5, 10, 6, 8]],![[0, 8, 5, 7, 12, 2], [3], [6, 12, 7, 7, 1, 5]]]
 h' := ![![[0, 0, 6, 3], [3, 4, 4, 10], [0, 0, 0, 1], [0, 1]],![[9, 2, 1, 2], [5, 11, 12, 2], [6, 5, 6, 4], [0, 0, 6, 3]],![[0, 10, 6, 8], [12, 10, 5, 8], [8, 7, 11, 8], [9, 2, 1, 2]],![[0, 1], [7, 1, 5, 6], [7, 1, 9], [0, 10, 6, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 2, 2], []]
 b := ![[], [], [5, 5, 2, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 2
 d := 5
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![7, 13]
 hp := by 
  intro i
  fin_cases i
  exact hp7'.out
  exact hp13'.out
 hlc := by decide
 m := ![2, 2]
 F := fun i =>
  match i with 
  | 0 => ![[5, 4, 1], [2, 6, 3, 1]]
  | 1 => ![[9, 1], [1, 0, 6, 4, 1]]
 D := fun i =>
  match i with 
  | 0 => ![2, 3]
  | 1 => ![1, 4]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  · exact irreducible_ofList_of_linear (R := ZMod 13) _ (by decide) (by decide)
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P1
 hm := by decide
 hprod := by decide!
 hinter := by decide!

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
