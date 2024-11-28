import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^6 - X^5 - 2*X^4 + 5*X^3 + 2*X^2 - 3*X + 1 : ℤ[X])

local notation "l" => [1, -3, 2, 5, -2, -1, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring

noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 3
 P := 32611
 M := 7
 r := 2
 ρ := 13/4
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide!
 hrho := by decide!
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C

example : cauchyBoundScaledOfList [3,14,15,92,65] (1/2) = 249/130 := by decide!

example : Nat.Prime 7 := by decide
