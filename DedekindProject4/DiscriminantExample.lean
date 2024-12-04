import DedekindProject4.Discriminant

open Polynomial

/-- Let `f` be the polynomial `f = 2 X^3 - X^2 - 2 X + 1`. -/
def f := ofList [(1 : ℤ), -2, -1, 2]

/-- The derivative `f'` is given by `f' = 6 X^2 - 2 X - 2`. -/
def f' := ofList [(-2 : ℤ), -2, 6]
lemma derivative_f : derivative f = f' := by
  rw [f, f', ← ofList_derivative_eq_derivative]
  decide!

lemma resultant_f_f' : Polynomial.resultant f f' = -72 := by decide!
lemma discriminant_f : Polynomial.discriminant f = 36 := by
  apply mul_left_cancel₀ (show f.leadingCoeff ≠ 0 by decide)
  rw [Polynomial.discriminant_def, derivative_f]
  · decide!
  · decide!

lemma root_product_f : 2 ^ (2 * (f.natDegree - 1)) * (0.5 + 1 : ℚ)^2 * 2^2 * (1 - 0.5)^2 = Polynomial.discriminant f := by
  rw [discriminant_f]
  decide!
