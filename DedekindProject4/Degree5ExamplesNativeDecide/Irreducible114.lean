import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 75*X^3 - 200*X^2 + 150*X - 60 : ℤ[X])

local notation "l" => [-60, 150, -200, -75, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp13' : Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp19' : Fact $ Nat.Prime 19 := fact_iff.2 (by norm_num)

def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [10, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 0, 1, 1]
 hbits := by native_decide
 h := ![[0, 1], [8, 12], [0, 1]]
 g := ![![[7, 4], [4], [8, 1]],![[0, 9], [4], [3, 12]]]
 h' := ![![[8, 12], [3, 11], [11, 2], [0, 1]],![[0, 1], [0, 2], [1, 11], [8, 12]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [2]]
 b := ![[], [9, 1]]
 hhz := by native_decide
 hhn := by native_decide
 hgcd := by native_decide

def P13P1 : CertificateIrreducibleZModOfList' 13 3 2 3 [7, 5, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 0, 1, 1]
 hbits := by native_decide
 h := ![[0, 1], [11, 5, 6], [7, 7, 7], [0, 1]]
 g := ![![[4, 0, 9], [10, 12], [1]],![[12, 9, 12, 11], [11, 12], [7, 0, 8, 8]],![[3, 0, 0, 6], [3, 9], [6, 10, 1, 5]]]
 h' := ![![[11, 5, 6], [5, 1, 10], [6, 8, 5], [0, 1]],![[7, 7, 7], [0, 1, 11], [8, 12, 5], [11, 5, 6]],![[0, 1], [9, 11, 5], [2, 6, 3], [7, 7, 7]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [0, 10], []]
 b := ![[], [6, 8, 7], []]
 hhz := by native_decide
 hhn := by native_decide
 hgcd := by native_decide

def P19P1 : CertificateIrreducibleZModOfList' 19 4 2 4 [1, 1, 10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by native_decide
 h := ![[0, 1], [15, 4, 10, 7], [1, 13, 1, 8], [0, 1, 8, 4], [0, 1]]
 g := ![![[4, 3, 5, 17], [12, 12, 14, 9], [1], []],![[11, 8, 13, 13, 3, 1], [10, 14, 13, 4], [3, 4, 16], [10, 12, 11]],![[0, 18, 12, 13, 10, 8], [1, 5, 17, 8, 16, 10], [0, 12, 9], [2, 14, 7]],![[0, 0, 2, 8, 2, 16], [1, 1, 8, 17, 14, 9], [18, 14, 1], [16, 16, 16]]]
 h' := ![![[15, 4, 10, 7], [7, 15, 8, 13], [18, 18, 9, 16], [0, 0, 1], [0, 1]],![[1, 13, 1, 8], [4, 1, 16, 7], [14, 10, 14], [6, 3, 3, 15], [15, 4, 10, 7]],![[0, 1, 8, 4], [0, 0, 8, 1], [1, 6, 9, 14], [18, 10, 16, 3], [1, 13, 1, 8]],![[0, 1], [18, 3, 6, 17], [10, 4, 6, 8], [3, 6, 18, 1], [0, 1, 8, 4]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [], [16, 14, 1], []]
 b := ![[], [], [4, 17, 16, 7], []]
 hhz := by native_decide
 hhn := by native_decide
 hgcd := by native_decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 2
 d := 5
 hprim := by native_decide
 hdeg := by native_decide
 hnn := by native_decide
 hdn := by native_decide
 p := ![13, 19]
 hp := by 
  intro i
  fin_cases i
  exact hp13'.out
  exact hp19'.out
 hlc := by native_decide
 m := ![2, 2]
 F := fun i =>
  match i with 
  | 0 => ![[10, 5, 1], [7, 5, 8, 1]]
  | 1 => ![[16, 1], [1, 1, 10, 3, 1]]
 D := fun i =>
  match i with 
  | 0 => ![2, 3]
  | 1 => ![1, 4]
 hl := by native_decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P0
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P1
  · exact irreducible_ofList_of_linear (R := ZMod 19) _ (by native_decide) (by native_decide)
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P1
 hm := by native_decide
 hprod := by native_decide
 hinter := by native_decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
