import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^3 - 45 : ℤ[X])

local notation "l" => [-45, 0, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring

noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 1
 P := 467
 M := 8
 r := 17/4
 ρ := 7793/1156
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide!
 hrho := by decide!
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C
