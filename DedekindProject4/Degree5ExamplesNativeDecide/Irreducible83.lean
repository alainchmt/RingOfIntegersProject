import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 + 15*X^3 - 80*X^2 - 90*X - 936 : ℤ[X])

local notation "l" => [-936, -90, -80, 15, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by native_decide
 hprim := by native_decide
 hlz := by native_decide
 s := 18
 P := 810137
 M := 27
 r := 21/4
 ρ := 14381/1764
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by native_decide
 hrho := by native_decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
