import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 + 5*X^3 - 20*X - 16 : ℤ[X])

local notation "l" => [-16, -20, 0, 5, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by native_decide
 hprim := by native_decide
 hlz := by native_decide
 s := 2
 P := 9199
 M := -7
 r := 9/4
 ρ := 161/36
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by native_decide
 hrho := by native_decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
