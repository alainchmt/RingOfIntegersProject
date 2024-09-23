import Mathlib.RingTheory.Polynomial.Basic

/-! # Polynomials as Lists

In this file we define arithmetic operations on lists which correspond to polynomial arithemtic.
We also define computable polynomials as lists with no trailing zeros and show that they are isomorphic
to Mathlib polynomials.

## Main definitions:
- `Polynomial.ofList` : turns a list of coefficients into the corresponding polynomial.
- `computablePolynomialRingEquiv` : the ring isomorphism between computable polynomials and Mathlib
polynomials

-/


open Polynomial BigOperators

variable {R : Type*} [DecidableEq R]

def Finsupp.ofList {R : Type*} [DecidableEq R] [Zero R] (xs : List R) : ℕ →₀ R where
  toFun := (fun i => xs.getD i 0)
  support := (Finset.range xs.length).filter (fun i => xs.getD i 0 ≠ 0)
  mem_support_toFun a := by
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    apply List.getD_eq_default

/-- Sends the list `[a₀, …, aₙ]` to the polynomial `a₀ + … + aₙ * X ^ n`.  -/
def Polynomial.ofList {R : Type*} [Semiring R] [DecidableEq R] (xs : List R) : R[X] :=
  ⟨Finsupp.ofList xs⟩

@[simp] lemma Polynomial.coeff_ofList {R : Type*} [Semiring R] [DecidableEq R] (xs : List R)
    (n : ℕ) : (ofList xs).coeff n = xs.getD n 0 := by
  rfl

@[simp]
lemma Polynomial.ofList_nil [Semiring R] : ofList (R := R) [] = 0 := rfl

@[simp]
lemma Polynomial.ofList_cons [Semiring R] (x : R) (xs) :
    ofList (x :: xs) = C x + X * ofList xs := by
  ext i
  cases i
  · simp [coeff_ofList]
  · simp

/-- Pointwise addition of lists. -/
def List.addPointwise [AddMonoid R]: List R → List R → List R
  | as, [] => as
  | [], bs => bs
  | (a :: as), (b :: bs) => (a + b) :: as.addPointwise bs

def List.neg [AddGroup R] : List R → List R :=
  fun l => List.map (fun a => - a) l

def List.mulPointwise [Monoid R](c : R) : List R → List R :=
  fun l => l.map (fun a => c * a)

def List.mulAddPointwise [Semiring R] (c d : R) : List R → List R → List R :=
  fun l₁ l₂ => List.addPointwise (l₁.mulPointwise c) (l₂.mulPointwise d)

/-- Removes the trailing zeros of a list. -/
def List.dropTrailingZeros [Zero R] [DecidableEq R] : List R → List R
  | [] => []
  | x :: xs => if x ≠ 0 ∨ xs.any (fun x => x ≠ 0) then x :: xs.dropTrailingZeros else []

@[simp] lemma List.dropTrailingZeros_nil [Zero R] [DecidableEq R] :
    List.dropTrailingZeros (R := R) [] = [] := rfl

@[simp] lemma List.dropTrailingZeros_eq_empty [Zero R] [DecidableEq R] (xs : List R)
  (hxs : xs.all fun x => x = 0) :
    List.dropTrailingZeros (R := R) (0 :: xs) = [] := if_neg (by aesop)

/-- Convolution of lists, which corresponds to polynomial multiplication. -/
def List.convolve [Semiring R]: List R → List R → List R
  | [], _ => []
  | _, [] => []
  | (a :: as), bs => List.mulAddPointwise a 1 bs (0 :: as.convolve bs)
-- (a + X * as) * bs = a * bs + X * (as * bs)

/-- A more efficient version of dropTrailingZeros in case the last entry is nonzero. -/
def List.dropTrailingZeros' [Zero R][DecidableEq R] : List R → List R
  | [] => []
  | (a :: as) => if List.getLast _ (List.cons_ne_nil a as) ≠ 0 then (a :: as)
    else (a :: as).dropTrailingZeros

------------------------------------------------
@[simp]
lemma addPointwise_nil_left [AddMonoid R] (l : List R) : List.addPointwise [] l = l := by
  induction' l with a as _
  rfl ; rfl

@[simp]
lemma addPointwise_nil_right [AddMonoid R] (l : List R) : List.addPointwise l [] = l := by
  induction' l with a as _
  rfl ; rfl

@[simp]
lemma addPointwise_cons [AddMonoid R] (x y : R) (l l' : List R) :
    List.addPointwise (x :: l) (y :: l') = (x + y) :: (List.addPointwise l l') := by
  rfl

@[simp]
lemma ofList_mulPointwise_eq_C_mul [Semiring R] (c : R) (l : List R) :
  ofList (l.mulPointwise c) = C c * ofList l := by
  induction' l with a as ha
  · simp only [List.mulPointwise, List.map_nil, ofList_nil, mul_zero]
  · simp only [List.mulPointwise, List.map_cons, ofList_cons, map_mul]
    erw [ha]
    simp only [mul_add, Polynomial.X_mul, mul_assoc]

@[simp]
lemma ofList_map [Semiring R ][DecidableEq R] {S : Type*} [Semiring S] [DecidableEq S]
 (l : List R) (f : R →+* S) : Polynomial.map f (ofList l) = ofList (List.map f l) := by
  induction' l with a as ha
  · simp only [List.map_nil, ofList_nil, mul_zero, Polynomial.map_zero]
  · simp only [List.map_cons, ofList_cons, Polynomial.map_add, map_C, Polynomial.map_mul, map_X]
    rw [ha]

lemma List.ofList_convolve_nil_right [Semiring R] (l : List R) :
    Polynomial.ofList (l.convolve []) = 0 := by
  induction' l with _ _ ha
  · simp only [convolve, ofList_nil]
  · simp only [convolve, ofList_nil, mul_zero, map_zero, one_mul, map_id', zero_add, ha]

lemma ofList_zeros [Semiring R] (l : List R) (h : ∀ x ∈ l, x = 0) : ofList l = 0 := by
  induction' l with a as ha
  · rfl
  · simp only [ofList_cons]
    have : ∀ x ∈ as , x = 0 := by exact fun x a_1 => h x (List.Mem.tail a a_1)
    rw [ha this, h a (List.Mem.head as), map_zero, mul_zero, add_zero]

lemma List.dropTrailingZeros_of_zero [Zero R] [DecidableEq R]
    (l : List R) (h : ∀ x ∈ l, x = 0) : l.dropTrailingZeros = [] := by
  induction' l with a as _
  · rfl
  · by_cases h2 : ¬ a = 0 ∨ ∃ x ∈ as, ¬x = 0
    · simp only [dropTrailingZeros, ne_eq, decide_not, any_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, ite_eq_right_iff, imp_false]
      push_neg
      simp only [mem_cons, forall_eq_or_imp] at h
      exact h
    · simp only [dropTrailingZeros, ne_eq, decide_not, any_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, h2, ↓reduceIte]

lemma List.dropTrailingZeros_ne_zero_of_ne_zero [Zero R] [DecidableEq R]
    (l : List R) (h : ∃ x ∈ l, x ≠ 0) : ∃ x ∈ l.dropTrailingZeros, x ≠ 0 := by
  induction' l with a as ha
  · simp only [not_mem_nil, ne_eq, false_and, exists_const] at h
  · simp only [mem_cons, ne_eq, exists_eq_or_imp] at h
    simp only [dropTrailingZeros, ne_eq, decide_not, any_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, h, ↓reduceIte, mem_cons, exists_eq_or_imp]
    rcases h with h1 | h2
    · exact Or.inl h1
    · exact not_or_of_imp fun _ => ha h2

@[simp]
lemma ofList_dropTrailingZeros_eq_ofList [Semiring R] [DecidableEq R] (l : List R) :
    ofList (l.dropTrailingZeros) = ofList l := by
  induction' l with a as ha
  · simp only [ofList_nil, List.dropTrailingZeros]
  · by_cases h : (a ≠ 0 ∨ as.any (fun x => x ≠ 0))
    · simp only [ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, ofList_cons]
      rw [ha]
    · simp only [ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, ofList_cons, ofList_nil]
      push_neg at h
      rw [h.1, ofList_zeros as h.2, map_zero, mul_zero, add_zero]

lemma dropTrailingZeros_iter [Zero R] (l : List R) [DecidableEq R] :
    l.dropTrailingZeros =  (l.dropTrailingZeros).dropTrailingZeros := by
  induction' l with a as ha
  · simp only [List.dropTrailingZeros]
  · by_cases h : (a ≠ 0 ∨ as.any (fun x => x ≠ 0))
    · simp only [ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at  h
      simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, List.dropTrailingZeros]
      rcases h with h1 | h2
      · simp only [h1, not_false_eq_true, true_or, ↓reduceIte, List.cons.injEq, true_and]
        exact ha
      · simp only [List.dropTrailingZeros_ne_zero_of_ne_zero as h2, or_true, ↓reduceIte,
        List.cons.injEq, true_and]
        exact ha
    · simp only [ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, List.dropTrailingZeros]

@[simp]
lemma dropTrailingZeros_zero [Zero R] [DecidableEq R] : ([0] : List R).dropTrailingZeros = [] := by
  simp only [List.dropTrailingZeros, ne_eq, not_true_eq_false, decide_not, List.any_nil, or_self,
    ↓reduceIte]

lemma dropTrailingZeros_cons [Zero R] [DecidableEq R] (a : R) (as : List R) :
    (a :: as).dropTrailingZeros =  (a :: as.dropTrailingZeros).dropTrailingZeros:= by
  by_cases h : (a ≠ 0 ∨ as.any (fun x => x ≠ 0))
  · simp only [ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, h, ↓reduceIte]
    rcases h with h1 | h2
    · simp only [h1, not_false_eq_true, true_or, ↓reduceIte, List.cons.injEq, true_and]
      exact dropTrailingZeros_iter as
    · simp[List.dropTrailingZeros_ne_zero_of_ne_zero, h2]
      exact dropTrailingZeros_iter as
  · simp only [ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    push_neg at h
    have : ∀ x ∈ (0 :: as), x = 0 := by
      simp only [List.mem_cons, forall_eq_or_imp]
      exact And.imp (fun _ ↦ trivial) (fun a => a) h
    rw [h.1, List.dropTrailingZeros_of_zero as h.2, List.dropTrailingZeros_of_zero _ this,
       dropTrailingZeros_zero ]

lemma dropTrailingZeros_append_zero [Zero R] [DecidableEq R] (l : List R) :
    (l ++ [0]).dropTrailingZeros = l.dropTrailingZeros := by
  induction' l with a as ha
  · simp only [List.dropTrailingZeros, ne_eq, not_true_eq_false, decide_not, List.any_nil, or_self,
    ↓reduceIte]
  · rw [List.cons_append, dropTrailingZeros_cons, ha, ← dropTrailingZeros_cons]

lemma dropTrailingZeros_append_ne_zero [Zero R] [DecidableEq R] (a : R) (ha : a ≠ 0)(l : List R) :
    (l ++ [a]).dropTrailingZeros = l ++ [a] := by
  induction' l with a as ha
  · simp only [List.dropTrailingZeros, ne_eq, ha, not_false_eq_true, decide_not, List.any_nil,
    or_false, ↓reduceIte, List.nil_append]
  · rename R => a'
    rename a ≠ 0 => ha'
    rw [List.cons_append, dropTrailingZeros_cons, ha]
    erw [ite_eq_iff]
    left
    constructor
    · right
      simp only [ne_eq, decide_not, List.any_eq_true, List.mem_append, List.mem_singleton,
        Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨a, ⟨ by exact Or.inr rfl, ha'⟩ ⟩
    rw [ha]

lemma dropTrailingZeros_length [Zero R] [DecidableEq R] (l : List R) :
    (l.dropTrailingZeros).length ≤ l.length := by
  induction' l with a as ha
  · simp only [List.dropTrailingZeros, List.length_nil, le_refl]
  · by_cases h : ¬a = 0 ∨ ∃ x ∈ as, ¬x = 0
    · simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, h, ↓reduceIte, List.length_cons]
      exact Nat.pred_le_iff.mp ha
    · simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, List.length_nil, List.length_cons, zero_le]

lemma eq_dropTrailingZeros_iff_last_entry_ne_zero
    [Zero R] [DecidableEq R] (l : List R) (hz : l ≠ []) :
    l = l.dropTrailingZeros ↔ l.getLast hz ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    nth_rw 2 [← List.dropLast_append_getLast hz] at h
    simp_rw [hc, dropTrailingZeros_append_zero] at h
    have aux1 := le_of_eq_of_le (congr_arg _ h) (dropTrailingZeros_length (l.dropLast))
    simp only [List.length_dropLast] at aux1
    have := Nat.pred_lt (n := l.length)
      (by exact Nat.pos_iff_ne_zero.mp (List.length_pos_of_ne_nil hz) )
    rw [← not_le] at this
    exact this aux1
  · intro h
    nth_rw 2 [← List.dropLast_append_getLast hz]
    rw [dropTrailingZeros_append_ne_zero _ h, List.dropLast_append_getLast hz]

lemma dropTrailingZeros_eq_dropTrailingZeros'
    [Zero R][DecidableEq R](l : List R):
    l.dropTrailingZeros = l.dropTrailingZeros' := by
  match l with
  | [] => rfl
  | (a :: as) =>
    by_cases h : (a :: as).getLast (List.cons_ne_nil a as) ≠ 0
    · unfold List.dropTrailingZeros'
      simp only [ ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, not_false_eq_true, ↓reduceIte]
      rw [← eq_dropTrailingZeros_iff_last_entry_ne_zero] at h
      rw [← h]
    · unfold List.dropTrailingZeros'
      simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte]

-------------------------------------------------------------------------------

/- For lists, we define an addition, multiplication and other operations.  -/

instance [AddMonoid R] : Add (List R) where
  add := λ l₁ l₂ => l₁.addPointwise l₂

instance [AddGroup R] : Neg (List R) where
  neg := List.neg

instance [AddGroup R] : Sub (List R) where
  sub := λ l₁ l₂ => l₁.addPointwise (l₂.neg)

instance [Semiring R] : Mul (List R) where
  mul := λ l₁ l₂ => l₁.convolve l₂

instance [One R] : One (List R) where
  one := [1]

instance : Zero (List R) where
  zero := []

instance [Semiring R] : NatPow (List R)  where
  pow := λ l => λ n => npowRec n l

instance [Semiring R] : NatCast (List  R) where
  natCast := λ n => [(n : R)]

instance [Semiring R] : AddZeroClass (List R) where
  zero_add := addPointwise_nil_left
  add_zero := addPointwise_nil_right


@[simp]
lemma List.mul_nil [Semiring R] (l : List R) : l * [] = [] := by
  induction' l with b bs _
  · rfl
  · rfl

@[simp]
lemma List.nil_mul [Semiring R] (l : List R) : [] * l = [] := by
  induction' l with b bs _
  · rfl
  · rfl

@[simp]
lemma List.nil_add [AddMonoid R] (l : List R) : [] + l = l := by
  induction' l with a as _
  · rfl
  · rfl

@[simp]
lemma List.add_nil [AddMonoid R] (l : List R) : l + [] = l := by
  induction' l with a as _
  · rfl
  · rfl

lemma List.neg_eq_neg_one_mul [Ring R] (l : List R) : l.neg = [- 1] * l := by
  match l with
  | [] => rfl
  | (a :: as) =>
    simp only [neg, map_cons]
    congr
    · simp only [neg_mul, one_mul, mul_zero, add_zero]
    · simp only [neg_mul, one_mul, convolve, map_nil, addPointwise]


lemma List.add_length [AddMonoid R] (l₁ l₂ : List R) :
    (l₁ + l₂).length = max l₁.length l₂.length := by
  have : ∀ (l : List R), (l₁ + l).length = max l₁.length l.length := by
    induction' l₁ with a as hi
    · intro l
      rw [List.nil_add]
      simp only [length_nil, ge_iff_le, zero_le, max_eq_right]
    · intro l
      match l with
      | [] =>
      · rw [List.add_nil]
        simp only [length_cons, length_nil, ge_iff_le, zero_le, max_eq_left]
      | (b :: bs) =>
      · have : a :: as + b :: bs = (a + b) :: (as + bs) := by rfl
        rw [this, length_cons, hi bs, length_cons, length_cons]
        exact (Nat.succ_max_succ (length as) (length bs)).symm
  exact this l₂

lemma List.mulPointwise_length [Semiring R] (l : List R) (a : R) :
    (List.mulPointwise a l).length = l.length := by
  unfold mulPointwise
  simp only [length_map]

lemma List.mul_eq_mulPointwise [Semiring R] (l : List R) (a : R) :
    [a] * l = List.mulPointwise a l :=
  match l with
  | [] => rfl
  | (b :: bs) => by
    rw [(show [a] * (b :: bs) = [a].convolve (b :: bs) by rfl)]
    simp only [convolve, mulAddPointwise, addPointwise, mul_zero, add_zero, one_mul, map_nil,
      mulPointwise, map_cons]

/- Lemmas relating operations on functions `Fin n → R` and lists. -/

lemma List.add_length_ofFn [AddMonoid R] (a b : Fin n →  R):
    List.length ((List.ofFn a) + (List.ofFn b)) = n := by
  simp only [List.add_length, length_ofFn, max_self]

lemma List.add_ofFn [AddMonoid R] (a b : Fin n →  R) :
    (List.ofFn a) + (List.ofFn b) = List.ofFn (a + b) := by
  induction' n with n hn
  · simp only [Nat.zero_eq, ofFn_zero, Matrix.empty_add_empty]
    rfl
  · rw [List.ofFn_succ a, List.ofFn_succ b, ofFn_succ, Pi.add_apply]
    erw [← hn (fun i => a (Fin.succ i)) (fun i => b (Fin.succ i))]
    rfl

variable [Semiring R]

lemma List.mulPointwise_ofFn (a : Fin n → R) (c : R) :
    List.mulPointwise c (List.ofFn a) = List.ofFn (c • a) := by
  match n with
  | 0 =>
    simp only [Nat.zero_eq, ofFn_zero, Matrix.smul_empty]
    rfl
  | Nat.succ n =>
    rw [List.ofFn_succ a]
    unfold mulPointwise
    simp only [map_cons, map_ofFn, ofFn_succ, Pi.smul_apply, smul_eq_mul, cons.injEq, ofFn_inj,
      true_and]
    rfl

lemma List.sum_ofFn' {m : ℕ} (hm : m ≠ 0) (f : Fin m → (Fin n → R)) :
    List.ofFn (∑ i, f i) = List.sum (List.ofFn (fun i => List.ofFn (f i))) := by
  induction' m with m hmm
  · contradiction
  · by_cases hm1 : m ≠ 0
    · unfold List.sum
      rw [List.ofFn_succ',List.concat_eq_append, List.foldl_concat, Fin.sum_univ_castSucc _]
      have := hmm hm1 (fun i => f (Fin.castSucc i))
      rw [← List.add_ofFn, this]
      rfl
    · push_neg at hm1
      simp only [hm1, List.ofFn_zero, List.foldl_nil]
      rw [ Fin.sum_univ_castSucc, Fintype.sum_equiv (finCongr hm1) (fun i => f (Fin.castSucc i))
        (fun i => f (Fin.castSucc (Fin.cast hm1.symm i)))]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Nat.reduceSucc, ofFn_succ,
        Fin.isValue, Fin.cast_zero, Fin.cast_succ_eq, ofFn_zero, List.sum]
      dsimp
      erw [List.nil_add]
      have : Fin.last m = 0 := by
        rw [← Fin.val_inj]
        exact hm1
      rw [this]
      · intro x
        rfl

/- Properties of `ofList` -/

lemma List.pow_def {l : List R} {n : ℕ} : l ^ n = npowRec n l := rfl

lemma List.one_eq : (1 : List R) = [1] := rfl

lemma List.zero_eq : (0 : List R) = [] := rfl

lemma ofList_one : ofList (1 : List R) = 1 := by
  simp only [List.one_eq, ofList_cons, ofList_nil, map_one, mul_zero, add_zero]

lemma ofList_zero : ofList (0 : List R) = 0 := by
  simp only [List.zero_eq, ofList_nil]

lemma ofList_singleton (a : R) : ofList [a] = C a := by
  simp only [ofList_cons, ofList_nil, mul_zero, add_zero]

lemma ofList_natCast {n : ℕ} : ofList (n : List R) = n :=
  ofList_singleton _

/-- `ofList` respects addition. -/
lemma ofList_addPointwise_eq_add (l₁ l₂ : List R) :
    ofList (l₁ + l₂) = ofList (l₁) + ofList (l₂) := by
  have : ∀ (l : List R) , Polynomial.ofList (l₁.addPointwise l) =
  Polynomial.ofList (l₁) + Polynomial.ofList (l) := by
    induction' l₁ with a as ha
    · intro l ; simp only [addPointwise_nil_left, ofList_nil, zero_add]
    · intro l
      match l with
      | [] => simp only [ofList_nil, addPointwise_nil_right, add_zero]
      | (b :: bs) =>
        simp only [addPointwise_cons, ofList_cons, map_add, ha bs, add_assoc, add_comm, mul_add ]
        rw [add_comm (C a) _, add_comm (C a) _, add_assoc]
  exact this l₂

/-- `ofList` respects multiplication. -/
lemma ofList_convolve_eq_mul (l₁ l₂ : List R) :
    ofList (l₁ *  l₂) = ofList (l₁) * ofList (l₂) := by
  induction' l₁ with a as ha
  · simp only [ofList_nil, zero_mul, List.nil_mul]
  · match l₂ with
    | [] => erw [List.ofList_convolve_nil_right, ofList, mul_zero]
    | (b :: bs) =>
      simp only [ofList_cons, mul_zero, add_zero, map_mul]
      erw [ofList_addPointwise_eq_add, ofList_mulPointwise_eq_C_mul, ofList_mulPointwise_eq_C_mul,
          ofList_cons, ofList_cons, ha]
      simp only [map_one, ofList_cons, one_mul, map_zero, zero_mul, zero_add]
      simp only [add_comm, mul_add, add_assoc, add_mul, X_mul, mul_assoc]
      abel

/-- `ofList` respects powers. -/
lemma ofList_pow_eq_pow (l : List R) (n : ℕ) : ofList (l ^ n) = (ofList l) ^ n := by
  induction' n with n hn
  · simp only [List.pow_def, npowRec, ofList_one, map_one, mul_zero, add_zero, Nat.zero_eq, pow_zero]
  · have : l ^ (Nat.succ (n := n)) = npowRec (Nat.succ (n := n)) l := by rfl
    rw [this]
    simp only [npowRec]
    erw [ofList_convolve_eq_mul, hn, pow_succ]

/-- Sends a polynomial to a list of its coefficients. The zero polynomial is sent to `[0]`. -/
def Polynomial.toList' [DecidableEq R] (p : Polynomial R) : List R :=
  List.ofFn (λ (i : Fin (p.natDegree + 1)) => p.coeff i : Fin (p.natDegree + 1) → R)

@[simp]
lemma Polynomial.toList'_length [DecidableEq R] (p : Polynomial R) :
    (Polynomial.toList' p).length = p.natDegree + 1 := List.length_ofFn fun i => coeff p ↑i

@[simp]
lemma Polynomial.toList_C [DecidableEq R] (a : R) : toList' (C a) = [a] := by
  unfold toList'
  rw [List.ofFn_succ]
  congr
  · simp only [Fin.val_zero, coeff_C_zero]
  · simp only [natDegree_C, List.ofFn_zero]

lemma Polynomial.toList_cons_of_add_ne_zero [DecidableEq R] [Nontrivial R] (a : R)
    (p : Polynomial R) (hp : p ≠ 0) :
    toList' (C a + X * p) = (a :: toList' p) := by
  have heqdeg : (C a + X * p).natDegree = p.natDegree + 1 := by
    rw [natDegree_C_add, Polynomial.natDegree_X_mul hp]
  unfold Polynomial.toList'
  rw [List.ofFn_succ]
  congr
  · simp only [Fin.val_zero, coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul,
    add_zero]
  · simp only [Fin.val_succ, coeff_add, coeff_C_succ, coeff_X_mul, zero_add]
    rw [Fin.heq_fun_iff heqdeg]
    simp only [implies_true]

lemma Polynomial.toList'_cons [DecidableEq R] (a : R) (p : Polynomial R) :
    (toList' (C a + X * p)).dropTrailingZeros = (a :: toList' p).dropTrailingZeros := by
  by_cases hp : p = 0
  · rw [hp, mul_zero, add_zero, Polynomial.toList_C, ← C_0, Polynomial.toList_C]
    simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_nil, or_false, ite_not,
      List.any_cons, decide_True, Bool.not_true, Bool.or_self, not_true_eq_false, or_self,
      ↓reduceIte]
  · haveI : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton, ← Polynomial.subsingleton_iff_subsingleton] at h
      exact hp (Subsingleton.eq_zero p)
    congr
    exact Polynomial.toList_cons_of_add_ne_zero a p hp

/-- Sends a polynomial to a list of its coefficients (with non-zero last entry).
  The zero polynomial is sent to `[]`. -/
def Polynomial.toList [DecidableEq R] (p : Polynomial R) := (toList' p).dropTrailingZeros

/-- `toList` is the left inverse of ofList (modulo trailing zeros). -/
lemma toList_comp_ofList [DecidableEq R] (l : List R) :
   toList (ofList l) = l.dropTrailingZeros := by
  show (toList' (ofList l)).dropTrailingZeros = l.dropTrailingZeros
  induction' l with a as ha
  · simp only [toList', ofList_nil, natDegree_zero, zero_add, List.ofFn_succ, Nat.reduceAdd,
      Fin.isValue, Fin.cast_eq_self, Fin.coe_fin_one, coeff_zero, List.ofFn_zero, List.all_nil,
      List.dropTrailingZeros_eq_empty, List.dropTrailingZeros_nil]
  · simp only [ofList_cons]
    rw [Polynomial.toList'_cons, dropTrailingZeros_cons, ha, ← dropTrailingZeros_cons]

lemma toList_zero [DecidableEq R] : toList (0 : R[X]) = [] := by
  simp only [toList, toList', natDegree_zero, zero_add, List.ofFn_succ, Nat.reduceAdd, Fin.isValue,
    Fin.cast_eq_self, Fin.coe_fin_one, coeff_zero, List.ofFn_zero, List.all_nil,
    List.dropTrailingZeros_eq_empty]

lemma nil_of_ofList_eq_zero [DecidableEq R] (l : List R)
    (hdt : l = l.dropTrailingZeros) (hz : ofList l = 0) : l = [] := by
  rw [← toList_comp_ofList l , hz, toList_zero] at hdt
  exact hdt

lemma toList_eq_toList' [DecidableEq R] (p : R[X]) (hpz : p ≠ 0) :
    toList' p = toList p := by
  have : toList' p ≠ [] := by
    unfold toList'
    simp only [List.ofFn_succ, Fin.val_zero, Fin.val_succ, ne_eq, not_false_eq_true]
  erw [eq_dropTrailingZeros_iff_last_entry_ne_zero _ this]
  unfold toList'
  rw [List.getLast_eq_get]
  simp only [List.ofFn_succ, Fin.val_zero, Fin.val_succ, List.length_cons, List.length_ofFn,
    Nat.succ_sub_succ_eq_sub, tsub_zero, List.get_ofFn, Fin.cast_mk, coeff_natDegree, ne_eq,
    leadingCoeff_eq_zero, hpz, not_false_eq_true]

/-- `ofList` is the right inverse of `toList'`. -/
lemma ofList_of_toList [DecidableEq R] (p : Polynomial R) :
    ofList (Polynomial.toList' p) = p := by
  have : ∀ (n : ℕ) (f : Polynomial R) , f.natDegree = n → ofList (Polynomial.toList' f) = f := by
    intro n
    induction' n with n hn
    intro f hnat
    · rw [Polynomial.eq_C_of_natDegree_eq_zero hnat]
      simp only [toList_C, ofList_cons, ofList_nil, coeff_C_zero, natDegree_C, zero_add,
          mul_zero, add_zero]
    · intro f hfrg
      unfold toList'
      simp only [List.ofFn_succ, Fin.val_zero, Fin.val_succ, ofList_cons]
      obtain ⟨q, hq⟩ := (Polynomial.X_dvd_iff (f := Polynomial.erase 0 f)).2 (erase_same _ _)
      have heq : f = C (coeff f 0) + X * q := by
        rw [← hq]
        exact (Polynomial.monomial_add_erase f 0).symm
      have hqz : q ≠ 0 := by
        by_contra h
        rw [h, mul_zero, add_zero] at heq
        rw [heq, natDegree_C] at hfrg
        simp only at hfrg
      haveI : Nontrivial R := by
        rw [← Polynomial.nontrivial_iff]
        exact nontrivial_of_ne _ _ hqz
      have hcoeff : ∀ i , coeff f (i + 1) = coeff q i := by
        intro i
        rw [heq]
        simp only [coeff_add, coeff_C_succ, coeff_X_mul, zero_add]
      have hgd : natDegree q = n := by
        rw [← Nat.succ_inj, Nat.succ_eq_add_one, Nat.succ_eq_add_one, ← hfrg, heq, natDegree_C_add,
            Polynomial.natDegree_X_mul hqz]
      have hL: toList' q = (List.ofFn fun (i : Fin (natDegree f)) => coeff f (↑i + 1)) := by
        symm
        unfold toList'
        convert congr_heq ((heq_self_iff_true _ ).2 True.intro) ?_
        rw [Fin.heq_fun_iff rfl]
        intro i
        dsimp
        convert hcoeff i
        · rw [heq, natDegree_C_add, Polynomial.natDegree_X_mul hqz]
      rw [← hL, hn q hgd]
      exact heq.symm
  exact this (natDegree p) p rfl

lemma natDegree_ofList [DecidableEq R] (l : List R) (hz : l ≠ 0) (hlz : l = l.dropTrailingZeros) :
    natDegree (ofList l) + 1 = l.length := by
  rw [← toList_comp_ofList, ← toList_eq_toList'] at hlz
  nth_rw 2 [hlz]
  rw [Polynomial.toList'_length (ofList l)]
  by_contra hc
  rw [hc, toList_zero] at hlz
  exact hz hlz

lemma natDegree_ofList' [DecidableEq R] (l : List R) (hz : l.dropTrailingZeros ≠ 0) :
    natDegree (ofList l) + 1 = l.dropTrailingZeros.length := by
  rw [← ofList_dropTrailingZeros_eq_ofList]
  refine natDegree_ofList (l.dropTrailingZeros) hz (dropTrailingZeros_iter l)

lemma ofList_replicate_zero_append [DecidableEq R] (n : ℕ) (l : List R) :
    ofList (List.replicate n (0 : R) ++ l) = X ^ n * ofList l := by
  induction' n with n hn
  · simp only [List.replicate, List.nil_append, Nat.zero_eq, pow_zero, one_mul]
  · simp only [List.replicate, ofList_cons, List.cons_append, map_zero, List.append_eq, zero_add]
    rw [hn, ← mul_assoc, pow_succ']

lemma List.self_eq_dropTrailingZeros_append_zero [DecidableEq R] [Zero R]
    (l : List R) : ∃ (n : ℕ) , l = l.dropTrailingZeros ++ replicate n 0 := by
  induction' l with a as ha
  · use 0
    simp only [dropTrailingZeros, replicate, append_nil]
  · by_cases h : (a ≠ 0 ∨ as.any (fun x => x ≠ 0))
    · simp only [ne_eq, decide_not, any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      simp only [dropTrailingZeros, ne_eq, decide_not, any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, cons_append, cons.injEq, true_and]
      exact ha
    · simp only [ne_eq, decide_not, any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      simp only [dropTrailingZeros, ne_eq, decide_not, any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, nil_append]
      use (a :: as).length
      push_neg at h
      simp only [h, replicate, Nat.add_eq, add_zero, cons.injEq, true_and]
      rw [List.eq_replicate_length]
      exact h.2

lemma ofList_eq_zero {R : Type u} [Semiring R] [DecidableEq R]
    (l : List R) (h : ofList l = 0) : ∃ (n : ℕ) , l = List.replicate n 0 := by
  have aux := toList_comp_ofList l
  rw [h, toList_zero] at aux
  obtain ⟨n, hn⟩ := List.self_eq_dropTrailingZeros_append_zero l
  rw [← aux] at hn
  exact ⟨n, hn⟩

lemma List.eq_of_eq_dropTrailingZeros_eq_length [DecidableEq R][Zero R]
    (l₁ l₂ : List R) (hdt : l₁.dropTrailingZeros = l₂.dropTrailingZeros)
    (hl : l₁.length = l₂.length) : l₁ = l₂ := by
  obtain ⟨n, h1⟩ := List.self_eq_dropTrailingZeros_append_zero l₁
  obtain ⟨m, h2⟩ := List.self_eq_dropTrailingZeros_append_zero l₂
  rw [h1, h2] at hl
  simp only [length_append, length_replicate] at hl
  rw [hdt, add_right_inj] at hl
  rw [h1, h2, hdt, hl]

-----------------------

lemma ofList_foldl_add {R : Type u}[Semiring R][DecidableEq R](l : List (List R)):
    ∀ a , ofList (List.foldl (fun (x y : List R) => x + y) a l ) = ofList a + ofList (l.sum) := by
  induction' l with b bs hb
  · simp only [List.foldl_nil, List.sum_nil, ofList_zero, ofList_nil, add_zero, forall_const]
  · intro a
    erw [List.foldl_cons, hb (a + b), List.sum, List.foldl_cons,
    hb (0 + b), ← List.sum, ofList_addPointwise_eq_add,
    ofList_addPointwise_eq_add, zero_add, add_assoc]

lemma ofList_foldl_mul {R : Type u}[Semiring R][DecidableEq R](l : List (List R)):
    ∀ a , ofList (List.foldl (fun (x y : List R) => x * y) a l ) = ofList a * ofList (l.prod) := by
  induction' l with b bs hb
  · intro a
    simp only [List.foldl_nil, ofList_nil, List.prod, ofList_one, map_one, mul_zero, add_zero,
      mul_one, forall_const]
  · intro a
    erw [List.foldl_cons, hb (a * b), List.prod, List.foldl_cons,
      hb (1 * b), ← List.prod, ofList_convolve_eq_mul,
      ofList_convolve_eq_mul]
    simp only [ofList_one, map_one, mul_zero, add_zero, one_mul, mul_assoc]

lemma list_sum_eq_ofList_sum {R : Type u} [Semiring R] [DecidableEq R]
    {n : ℕ}(f : Fin n → List R) : ofList ((List.ofFn f).sum) = ∑ k, ofList (f k) := by
  induction' n with n hn
  · simp only [ofList_zero, List.ofFn_zero, List.sum_nil, Nat.zero_eq, Finset.univ_eq_empty,
      Finset.sum_empty]
  · erw [List.ofFn_succ, List.sum, List.foldl_cons, ofList_foldl_add,
      hn, ofList_addPointwise_eq_add,
      zero_add, Fin.sum_univ_succ]

lemma list_sum_eq_ofList_prod {R : Type u} [CommRing R] [DecidableEq R]
    {n : ℕ}(f : Fin n → List R) : ofList ((List.ofFn f).prod) = ∏ k, ofList (f k) := by
  induction' n with n hn
  · simp only [ofList_one, List.ofFn_zero, List.prod, List.foldl_nil, map_one, mul_zero, add_zero,
      Nat.zero_eq, Finset.univ_eq_empty, Finset.prod_empty]
  · erw [List.ofFn_succ, List.prod, List.foldl_cons, ofList_foldl_mul,
      hn, ofList_convolve_eq_mul, ofList_one]
    simp only [mul_zero, add_zero, one_mul, Fin.prod_univ_succ]

lemma List.dvd_foldl_gcd {R : Type u} [CommSemiring R] [IsDomain R]
    [DecidableEq R] [GCDMonoid R] (x : R) (l : List R) (hdvd : ∀ a, a ∈ l → x ∣ a) :
    x ∣ List.foldr gcd 0 l := by
  induction' l with b bs hb
  · simp only [foldr_nil, dvd_zero]
  · simp only [mem_cons, forall_eq_or_imp] at hdvd
    rw [foldr_cons]
    exact (dvd_gcd_iff _ _ _ ).2 ⟨hdvd.1, (hb hdvd.2)⟩

/-- The coefficients of `ofList l` are given by the entries of `l`. -/
lemma ofList_coeff {R : Type u} [Semiring R] [DecidableEq R] (l : List R)
    (n : Fin l.length) : coeff (ofList l) n = l.get n := by
  simp

/-- The leading coefficient of `ofList l` is the last entry of `l`. -/
lemma ofList_leadingCoeff {R : Type u}[Semiring R][DecidableEq R] (l : List R)
    (hl : l ≠ []) (hlz : l = l.dropTrailingZeros) :
    (ofList l).leadingCoeff = l.getLast hl := by
  simp_rw [List.getLast_eq_get, ← ofList_coeff, ← (natDegree_ofList _ hl hlz)]
  rfl

/-- If the gcd of the entries in `l` is a unit, then the polynomial `ofList l` is primitive. -/
lemma ofList_isPrimitive {R : Type u} [CommSemiring R] [IsDomain R] [DecidableEq R] [GCDMonoid R]
    (u : R) (l : List R) (hp : List.foldr gcd 0 l = u) (hu : IsUnit u) : IsPrimitive (ofList l) := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hdvdc
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvdc
  have hdvd : ∀ a , a ∈ l → r ∣ a := by
    intro a ha
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 ha
    rw [← hi, ← ofList_coeff]
    exact hdvdc ↑i
  refine isUnit_of_dvd_unit ?_ hu
  rw [← hp]
  exact List.dvd_foldl_gcd _ _ hdvd

lemma ofList_eq_sum' {R : Type u} [Semiring R] [DecidableEq R]
    (n : ℕ) (f : Fin n → R) : ofList (List.ofFn f) = ∑ i, C (f i) * X ^ i.val := by
  rw [← Polynomial.coeff_inj]
  ext k
  by_cases hk : k < (List.ofFn f).length
  · rw [ofList_coeff _ ⟨k, hk⟩ ]
    simp only [List.get_ofFn, Fin.cast_mk, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite,
      mul_one, mul_zero]
    rw [Fintype.sum_eq_single (Fin.cast (List.length_ofFn f) ⟨k, hk⟩)]
    · simp only [Fin.cast_mk, ↓reduceIte]
    · intro x hx
      simp only [Fin.cast_mk, ne_eq, ite_eq_right_iff] at hx ⊢
      intro h2
      simp_rw [h2] at hx
      exfalso
      exact hx trivial
  · by_cases ht : (List.ofFn f).dropTrailingZeros = 0
    · rw [← ofList_dropTrailingZeros_eq_ofList, ht]
      obtain ⟨m, hm⟩ := List.self_eq_dropTrailingZeros_append_zero (List.ofFn f)
      erw [ht, List.nil_append] at hm
      have : ∀ (i : Fin n), f i = 0 := by
        intro i
        have := List.get_ofFn f (Fin.cast (List.length_ofFn f).symm i)
        rw [List.get_of_eq hm] at this
        simp only [Fin.coe_cast, Fin.cast_trans, Fin.cast_eq_self] at this
        rw [← this, List.get_eq_getElem, List.getElem_replicate]
      simp_rw [this]
      simp only [ofList_zero, coeff_zero, map_zero, zero_mul, Finset.sum_const_zero]
    · have : (ofList (List.ofFn f)).natDegree < k := by
        rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, natDegree_ofList' _ ht]
        refine le_trans (dropTrailingZeros_length (List.ofFn f) ) ?_
        exact not_lt.1 hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this]
      simp only [List.length_ofFn] at hk
      simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
      rw [Fintype.sum_eq_zero]
      simp only [ite_eq_right_iff]
      intro a hk2
      exfalso
      exact hk (lt_of_eq_of_lt hk2 a.2)

/- If the last entry of `l` is 1, then `ofList l` is monic. -/
lemma monic_ofList {R : Type u} [Semiring R] [DecidableEq R]
    (l : List R) (h : l.getLastD 0 = 1) : Monic (ofList l) := by
  simp only [Polynomial.Monic]
  match l with
  | [] =>
    simp only [List.getLastD_nil] at h
    simp only [ofList_nil, leadingCoeff_zero, h]
  | (a :: ls) =>
    simp only [List.getLastD_cons] at h
    by_cases hn : Nontrivial R
    · have hlen : (a :: ls) ≠ 0 := by simp only [ne_eq, not_false_eq_true]
      have aux : (ofList (a :: ls)).natDegree = (List.length (a :: ls)) - 1 := by
        rw [← natDegree_ofList ((a :: ls)) hlen ?_ ]
        simp only [ofList, natDegree_C_add, add_tsub_cancel_right]
        rw [eq_dropTrailingZeros_iff_last_entry_ne_zero _ hlen]
        rw [List.getLast_eq_getLastD, h]
        simp only [ne_eq, one_ne_zero, not_false_eq_true]
      erw [← Polynomial.coeff_natDegree, aux,
        ofList_coeff (a :: ls) ⟨_ , Nat.pred_lt (n := List.length (a :: ls))
        (by simp only [List.length_cons, ne_eq, Nat.succ_ne_zero, not_false_eq_true])⟩,
        ← List.getLast_eq_get (a :: ls) hlen]
      rw [List.getLast_eq_getLastD, h]
    · rw [← Polynomial.nontrivial_iff, nontrivial_iff (α := R[X])] at hn
      push_neg at hn
      rw [hn (ofList (a :: ls)) 1]
      simp only [monic_one, Monic.leadingCoeff]

lemma eq_dropTrailingZeros_of_getLastD_ne_zero  {R : Type u}[Semiring R]
    [DecidableEq R] (l : List R) (h : l.getLastD 0 ≠ 0) : l = l.dropTrailingZeros := by
  match l with
  | [] => simp only [List.dropTrailingZeros]
  | (a :: ls) =>
    have hlen : (a :: ls) ≠ 0 := by simp only [ne_eq, not_false_eq_true]
    rw [eq_dropTrailingZeros_iff_last_entry_ne_zero _ hlen, List.getLast_eq_getLastD]
    simp only [List.getLastD_cons, ne_eq] at h
    exact h

/-- Given a list of length `n`, this is the function `Fin n → R`
  that sends `i` to the `i`-th entry of the list. -/
def FnOfList {α : Type*} (n : ℕ) (l : List α) (hl : l.length = n) : Fin n → α :=
  fun (i : Fin n) => (l.get (Fin.cast hl.symm i))

lemma listOfFn_of_FnOfList
  {α : Type*}(n : ℕ)(l : List α)(hl : l.length = n) : List.ofFn (FnOfList n l hl) = l := by
  unfold FnOfList
  rw [← List.ofFn_congr hl _, List.ofFn_get]

lemma FnOfList_of_OfFn {α : Type*} (n : ℕ) (a : Fin n → α) :
    FnOfList n (List.ofFn a) (List.length_ofFn a) = a := by
  unfold FnOfList
  simp only [List.get_ofFn, Fin.cast_trans, Fin.cast_eq_self]

------------

/- # EXTRA OPERATIONS ON LISTS -/

/-- Adds `n - 1` zeros between entries of a list. In characteristic `n`, this corresponds to
  computing the `n`-th power of a list. -/
def List.expand {α : Type*} [DecidableEq α] [Zero α] (n : ℕ)  : List α → List α
  | [] => []
  | (a :: as) => if as = [] then [a] else [a] ++  (List.replicate (n - 1) (0 : α)) ++ expand n as

lemma List.expand_char {R : Type u} [CommSemiring R] [DecidableEq R] (p : ℕ)
    [h : ExpChar R p] (l : List R) :
    (List.map (frobenius R p) (List.expand p l)).dropTrailingZeros = (l ^ p).dropTrailingZeros := by
  by_cases hz : p = 0
  · exfalso
    exact pos_iff_ne_zero.1 (expChar_pos (R := R) p) hz
  · induction' l with a as ha
    · unfold expand
      erw [map_nil, ← Nat.succ_pred_eq_of_ne_zero hz]
      congr
      show [] = npowRec (Nat.succ (Nat.pred p)) []
      simp only [npowRec, mul_nil]
    · have : ofList (map (⇑(frobenius R p)) (expand p (a :: as))) = ofList ((a :: as) ^ p) := by
        rw [← ofList_map, ofList_pow_eq_pow ]
        by_cases has : as = []
        · unfold expand
          simp only [has, ↓reduceIte, ofList_cons, ofList_nil, mul_zero, add_zero, map_C]
          rw [← C_pow]
          rfl
        · unfold expand
          simp only [has, ↓reduceIte, singleton_append, cons_append, ofList_cons,
            Polynomial.map_add, map_C, Polynomial.map_mul, map_X, ofList_map, map_append,
            map_replicate, map_zero]
          erw [add_pow_expChar_of_commute _ _ _ (Commute.all _ _), ← C_pow, mul_pow]
          rw [map_nil, nil_append, ofList_replicate_zero_append,
            ← ofList_dropTrailingZeros_eq_ofList (map (⇑(frobenius R p)) (expand p as)),
          ha, ofList_dropTrailingZeros_eq_ofList, ofList_pow_eq_pow , ← mul_assoc]
          nth_rw 1 [← pow_one X]
          rw [← pow_add, Nat.sub_one, Nat.one_add, Nat.succ_pred_eq_of_ne_zero hz]
          rfl
      apply_fun toList at this
      rw [toList_comp_ofList, toList_comp_ofList] at this
      exact this

/-- Given `l`, computes the list corresponding to the derivative of the polynomial defined by `l`. -/
def List.derivative [Semiring R] : List R → List R
  | [] => []
  | (_ :: as) => as + (0 :: derivative as)

lemma ofList_derivative_eq_derivative [Semiring R] (l : List R) :
    ofList (List.derivative l) = derivative (ofList l) := by
  induction' l with a as has
  · simp only [List.derivative, ofList_nil, map_zero]
  · simp only [List.derivative, ofList_cons, map_add, derivative_C, derivative_mul, derivative_X,
      one_mul, zero_add]
    rw [ofList_addPointwise_eq_add, ← has]
    simp only [ofList_cons, map_zero, zero_add]

----------------------------------------------------------------------

section ComputablePolynomialsSemiring

/-- A computable polynomial is a list without no trailing zeros
  (i.e. equal to itself after removing trailing zeros). -/
@[reducible]
def ComputablePolynomial (R : Type*) [Semiring R] [DecidableEq R]:=
  {p : List R // p = p.dropTrailingZeros }

variable  {R : Type*} [Semiring R][DecidableEq R]

instance [AddMonoid R] : Add (ComputablePolynomial R) where
  add := λ p q =>
   ⟨(p.1 + q.1).dropTrailingZeros , dropTrailingZeros_iter (p.1 + q.1)⟩

instance [Semiring R] : Mul (ComputablePolynomial R) where
  mul := λ p q =>
   ⟨(p.1 * q.1).dropTrailingZeros , dropTrailingZeros_iter _ ⟩

instance [Semiring R] : Zero (ComputablePolynomial R) where
  zero := ⟨(0 : List R), rfl⟩

instance [Semiring R] : One (ComputablePolynomial R) where
  one := ⟨ (1 : List R).dropTrailingZeros , by exact dropTrailingZeros_iter 1 ⟩

instance [Semiring R] : Pow (ComputablePolynomial R) ℕ where
  pow := λ p => λ n => ⟨(p.1 ^ n).dropTrailingZeros,  dropTrailingZeros_iter _ ⟩

instance [Semiring R] : NatCast (ComputablePolynomial R) where
  natCast := λ n => ⟨[(n : R)].dropTrailingZeros, dropTrailingZeros_iter _ ⟩

instance [Semiring R] : SMul ℕ (ComputablePolynomial R) where
  smul := λ n => λ p => (↑n * p)

/-- Sends a polynomial to the corresponding computable polynomial. -/
def toComputablePolynomial (p : R[X]) : ComputablePolynomial R :=
  ⟨toList p, dropTrailingZeros_iter (toList' p) ⟩

/-- Sends a computable polynomial to the corresponding polynomial. -/
noncomputable def ofComputablePolynomial (p : ComputablePolynomial R) := ofList p.1

lemma toComputablePolynomial_comp_ofComputablePolynomial (p : ComputablePolynomial R):
  toComputablePolynomial (ofComputablePolynomial p) = p := by
  rw [← Subtype.val_inj]
  unfold toComputablePolynomial
  unfold ofComputablePolynomial
  dsimp
  rw [toList_comp_ofList]
  exact (p.2).symm

lemma ofComputablePolynomial_comp_toComputablePolynomial (p : Polynomial R) :
  ofComputablePolynomial (toComputablePolynomial p) = p := by
  unfold toComputablePolynomial
  unfold ofComputablePolynomial
  dsimp
  erw [ofList_dropTrailingZeros_eq_ofList, ofList_of_toList]


lemma ofComputablePolynomial_injective : Function.Injective (ofComputablePolynomial (R := R)) := by
  intro a b hab
  apply_fun toComputablePolynomial at hab
  rw [toComputablePolynomial_comp_ofComputablePolynomial,
    toComputablePolynomial_comp_ofComputablePolynomial] at hab
  exact hab

lemma ofComputablePolynomial_one :
  ofComputablePolynomial 1 = (1 : R[X]) := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList]
  simp only [ofList_one, map_one, mul_zero, add_zero]

lemma ofComputablePolynomial_add (p q : ComputablePolynomial R) :
  ofComputablePolynomial (p + q) = ofComputablePolynomial p + ofComputablePolynomial q := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList, ofList_addPointwise_eq_add]

lemma ofComputablePolynomial_mul (p q : ComputablePolynomial R) :
  ofComputablePolynomial (p * q) = (ofComputablePolynomial p) * (ofComputablePolynomial q) := by
   unfold ofComputablePolynomial
   erw [ofList_dropTrailingZeros_eq_ofList, ofList_convolve_eq_mul]

lemma ofComputablePolynomial_nsmul (p : ComputablePolynomial R) (n : ℕ) :
  ofComputablePolynomial (n • p) = n • (ofComputablePolynomial p) := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList, ofList_convolve_eq_mul, ofList_dropTrailingZeros_eq_ofList]
  simp only [ofList_singleton, map_natCast, mul_zero, add_zero, nsmul_eq_mul]

lemma ofComputablePolynomial_npow (p : ComputablePolynomial R) (n : ℕ) :
  ofComputablePolynomial (p ^ n) = (ofComputablePolynomial p) ^ n := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList, ofList_pow_eq_pow]

lemma ofComputablePolynomial_natCast (n : ℕ) :
  ofComputablePolynomial n = (n : R[X]) := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList]
  simp only [ofList_singleton, map_natCast, mul_zero, add_zero]

/-- Semiring instance for `ComputablePolynomial R`. -/
noncomputable instance ComputablePolynomial.semiring : Semiring (ComputablePolynomial R) := by
  refine Function.Injective.semiring
    (ofComputablePolynomial (R:= R)) ofComputablePolynomial_injective ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · exact ofComputablePolynomial_one
  · exact ofComputablePolynomial_add
  · exact ofComputablePolynomial_mul
  · intros; apply ofComputablePolynomial_nsmul
  · exact ofComputablePolynomial_npow
  · exact ofComputablePolynomial_natCast

end ComputablePolynomialsSemiring

variable {R : Type*} [DecidableEq R] [Ring R]

instance : Neg (ComputablePolynomial R) where
  neg := fun p => ⟨(p.1).neg.dropTrailingZeros, dropTrailingZeros_iter _ ⟩

instance : Sub (ComputablePolynomial R) where
  sub := fun p q => p + (- q)

instance : IntCast (ComputablePolynomial R) where
  intCast := fun z => ⟨[↑z].dropTrailingZeros, dropTrailingZeros_iter _ ⟩

instance : SMul ℤ (ComputablePolynomial R) where
  smul := fun z => fun p => z * p

lemma ofComputablePolynomial_neg (p : ComputablePolynomial R) :
  ofComputablePolynomial (- p) = - ofComputablePolynomial p := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList, List.neg_eq_neg_one_mul, ofList_convolve_eq_mul]
  simp only [ofList_singleton, map_neg, map_one, mul_zero, add_zero, neg_mul, one_mul]

lemma ofComputablePolynomial_sub (p q: ComputablePolynomial R) :
  ofComputablePolynomial (p - q) = ofComputablePolynomial p - ofComputablePolynomial q := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList, ofList_addPointwise_eq_add,
    ofList_dropTrailingZeros_eq_ofList, List.neg_eq_neg_one_mul, ofList_convolve_eq_mul]
  simp only [ofList_singleton, map_neg, map_one, mul_zero, add_zero, neg_mul, one_mul,
      sub_eq_add_neg]

lemma ofComputablePolynomial_zsmul (p : ComputablePolynomial R) (z : ℤ) :
  ofComputablePolynomial (z • p) = z • (ofComputablePolynomial p) := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList, ofList_convolve_eq_mul, ofList_dropTrailingZeros_eq_ofList]
  simp only [ofList_singleton, map_intCast, mul_zero, add_zero, zsmul_eq_mul]

lemma ofComputablePolynomial_intCast (z : ℤ) :
  ofComputablePolynomial z = (z : R[X]) := by
  unfold ofComputablePolynomial
  erw [ofList_dropTrailingZeros_eq_ofList]
  simp only [ofList_singleton, map_intCast, mul_zero, add_zero]

/-- Ring instance for `ComputablePolynomial R`. -/
noncomputable instance ComputablePolynomial.ring [Ring R] : Ring (ComputablePolynomial R) := by
  refine Function.Injective.ring (ofComputablePolynomial (R:= R))
    (ofComputablePolynomial_injective (R := R)) ?_?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · exact ofComputablePolynomial_one
  · exact ofComputablePolynomial_add
  · exact ofComputablePolynomial_mul
  · exact ofComputablePolynomial_neg
  · exact ofComputablePolynomial_sub
  · intros; apply ofComputablePolynomial_nsmul
  · intros; apply ofComputablePolynomial_zsmul
  · exact ofComputablePolynomial_npow
  · exact ofComputablePolynomial_natCast
  · exact ofComputablePolynomial_intCast

noncomputable def ofComputablePolynomialRingHom [Ring R] : ComputablePolynomial R →+* R[X] where
  toFun := ofComputablePolynomial
  map_one' := ofComputablePolynomial_one
  map_mul' := ofComputablePolynomial_mul
  map_zero' := rfl
  map_add' := ofComputablePolynomial_add

/- Ring isomorphism between polynomials and computable polynomials. -/
noncomputable def computablePolynomialRingEquiv [Ring R] : ComputablePolynomial R ≃+* R[X] where
  toFun := ofComputablePolynomial
  invFun := toComputablePolynomial
  left_inv := toComputablePolynomial_comp_ofComputablePolynomial
  right_inv := ofComputablePolynomial_comp_toComputablePolynomial
  map_mul' := ofComputablePolynomial_mul
  map_add' := ofComputablePolynomial_add
