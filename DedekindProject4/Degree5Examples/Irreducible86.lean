import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 - 25*X^3 - 150*X^2 + 100*X + 120 : ℤ[X])

local notation "l" => [120, 100, -150, -25, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 2
 P := 171449
 M := -13
 r := 6
 ρ := 61/6
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide!
 hrho := by decide!
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
