import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 - 100*X^2 - 525*X - 600 : ℤ[X])

local notation "l" => [-600, -525, -100, 0, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 2
 P := 255137
 M := 14
 r := 23/4
 ρ := 18567/2116
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by rfl
 hrho := by rfl
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 