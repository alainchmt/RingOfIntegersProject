import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 - 80*X^2 + 60*X + 96 : ℤ[X])

local notation "l" => [96, 60, -80, 0, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by native_decide
 hprim := by native_decide
 hlz := by native_decide
 s := 5
 P := 489691
 M := 19
 r := 21/4
 ρ := 14381/1764
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by native_decide
 hrho := by native_decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
