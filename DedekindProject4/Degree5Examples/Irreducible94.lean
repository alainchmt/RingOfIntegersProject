import DedekindProject4.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import DedekindProject4.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 + 25*X^3 - 200*X^2 + 300*X - 80 : ℤ[X])

local notation "l" => [-80, 300, -200, 25, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 2
 P := 802831
 M := -17
 r := 29/4
 ρ := 37189/3364
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide!
 hrho := by decide!
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
