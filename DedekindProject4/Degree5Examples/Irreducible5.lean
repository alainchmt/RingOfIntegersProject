import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 + 10*X^3 - 15*X^2 + 10*X - 12 : ℤ[X])

local notation "l" => [-12, 10, -15, 10, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 6
 P := 65141
 M := 13
 r := 3
 ρ := 19/3
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by rfl
 hrho := by rfl
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
