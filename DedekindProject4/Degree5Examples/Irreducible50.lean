import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 - 20*X^2 + 240*X - 48 : ℤ[X])

local notation "l" => [-48, 240, -20, 0, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 5
 P := 74197
 M := 13
 r := 5
 ρ := 173/25
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide!
 hrho := by decide!
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
