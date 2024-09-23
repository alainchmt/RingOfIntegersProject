import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^8 - X^6 + 2*X^4 + X^2 + 1 : ℤ[X])

local notation "l" => [1, 0, 1, 0, 2, 0, -1, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring

instance hp3' : Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)

def P3P0 : CertificateIrreducibleZModOfList' 3 4 2 1 [2, 0, 1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 1], [0, 2], [0, 0, 0, 2], [0, 1]]
 g := ![![[]],![[0, 2, 0, 2, 0, 1]],![[]],![[0, 1, 0, 1, 0, 2]]]
 h' := ![![[0, 0, 0, 1], [0, 1]],![[0, 2], [0, 0, 0, 1]],![[0, 0, 0, 2], [0, 2]],![[0, 1], [0, 0, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2], []]
 b := ![[], [], [0, 1, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : CertificateIrreducibleIntOfPrimeDegreeAnalysis T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 n := 1
 d := 4
 s := 724
 P := 58741
 M := 9
 r := 3/2
 ρ := 13/6
 hPPrime := by norm_num
 hrpos := by norm_num
 hnn := by decide
 hdn := by decide
 p := ![3]
 hp := by
  intro i
  fin_cases i
  exact hp3'.out
 hlc := by decide
 m := ![2]
 F := fun i =>
  match i with
  | 0 => ![[2, 0, 1, 0, 1], [2, 0, 1, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![4, 4]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
 hm := by decide
 hprod := by decide
 hinter := by decide
 hrhoeq := by rfl
 hrho := by rfl
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrimeDegrees _ _ C
