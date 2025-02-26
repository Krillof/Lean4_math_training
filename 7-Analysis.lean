import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always
set_option diagnostics true

/-
###########################################
###########################################
########Real analysis######################
###########################################
###########################################
-/

/-
/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure Real where ofCauchy ::
  /-- The underlying Cauchy completion -/
  cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)
-/

#check Real

#check Filter.Tendsto
#check nhds -- Neighbourhoods

-- Bolzano-Weierstrass theorem
--#check tendsto_subseq_of_frequently_bounded
--#check tendsto_subseq_of_bounded

#check ContinuousOn

#check deriv

-- Rolle's theorem
#check exists_deriv_eq_zero

-- Intermediate value theorem
#check intermediate_value_Icc

-- Intervals
#check Set.Icc 1 2
#check Set.Ico 1 2
#check Set.Ioc 1 2
#check Set.Ioo 1 2

-- Extreme value theorem
#check IsCompact.exists_isMinOn

-- Heine–Cantor theorem
#check CompactSpace.uniformContinuous_of_continuous

-- Fundamental theorem of calculus
#check intervalIntegral.integral_hasStrictDerivAt_of_tendsto_ae_right
#check intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le



-- TODO: See "Learning/Basic5.lean" and
-- find how limit is defined (or use def from this file
--  if there is none for real analysis)

-- TODO: find already proven theorems from
-- the Lean site no a page with 100 (or 1000 - there are both)
-- theorems


/-
Let's take definition of convergence
from the book "Mathematics in Lean"
and continue to use it.

What about
-/
def ConvergentSeqTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

/-
Show that this definition is equivalent to
-/


theorem
  convergesTo_const
  (a : ℝ)
  : ConvergentSeqTo (fun x : ℕ ↦ a) a
  := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem
  convergesTo_add
  {s t : ℕ → ℝ}
  {a b : ℝ}
  (cs : ConvergentSeqTo s a)
  (ct : ConvergentSeqTo t b)
  : ConvergentSeqTo
      (fun n ↦ s n + t n)
      (a + b)
  := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n ngr
  rcases hs n (le_of_max_le_left ngr) with qs
  rcases ht n (le_of_max_le_right ngr) with qt
  have ε2sum : ε / 2 + ε / 2 = ε := by norm_num
  have g : |s n - a| + |t n - b| < ε := by
    rw [← ε2sum]
    apply add_lt_add qs qt
  apply lt_of_le_of_lt _ g
  have h : s n + t n - (a + b) = (s n - a) + (t n - b) := by linarith
  rw [h]
  apply abs_add

theorem
  convergesTo_minus
  {s t : ℕ → ℝ}
  {a b : ℝ}
  (cs : ConvergentSeqTo s a)
  (ct : ConvergentSeqTo t b)
  : ConvergentSeqTo
      (fun n ↦ s n + t n)
      (a - b)
  := by
  sorry

theorem
  convergesTo_div
  {s t : ℕ → ℝ}
  {a b : ℝ}
  (h : b ≠ 0)
  (cs : ConvergentSeqTo s a)
  (ct : ConvergentSeqTo t b)
  : ConvergentSeqTo
      (fun n ↦ s n + t n)
      (a / b)
  := by
  sorry

def
  InfinitelyLargeSeq
  (s : ℕ → ℝ) :=
  ∀ A > 0,
  ∃ N,
  ∀ n ≥ N,
  |s n| > A

def
  InfinitelySmallSeq
  (s : ℕ → ℝ) :=
  ∀ ε > 0,
  ∃ N,
  ∀ n ≥ N,
  |s n| < ε

def
  BoundedSeq
  (s : ℕ → ℝ) :=
  ∃ A > 0,
  ∀ n,
  |s n| < A

def
  Subsequence
  (s : ℕ → ℝ)
  (ss : ℕ → ℝ)
  :=
  ∃ r : ℕ → ℕ,
  ∀ n,
  s (r n) = ss n



theorem
  infinitely_large_seq_is_not_bounded
  (s : ℕ → ℝ)
  (h : InfinitelyLargeSeq s)
  : ¬ BoundedSeq s
  := by
  sorry

theorem
  not_bounded_seq_does_not_mean_infinitely_large_seq
  (s : ℕ → ℝ)
  (h : BoundedSeq s)
  : (InfinitelyLargeSeq s)
    ∨ (¬ InfinitelyLargeSeq s)
  := by
  sorry

def
  ConvergentFunByCauchyOverToEq
  (U : Set ℝ)
  (f : ℝ → ℝ)
  (a A : ℝ)
  :=
  ∀ ε > 0,
  ∃ δ > 0,
  ∀ x ∈ U,
  |x - a| < δ
  → |A - f x| < ε


def
  ConvergentFunByHeineOverToEq
  (U : Set ℝ)
  (f : ℝ → ℝ)
  (a A : ℝ)
  :=
  ∀ ε > 0,
  ∀ s : ℕ → U,
  ConvergentSeqTo (fun x : ℕ ↦ s x) a
  → ConvergentSeqTo
      (fun x : ℕ ↦ f (s x)) A


theorem
  heine_def_eq_cauchy_def
  (U : Set ℝ)
  (f : ℝ → ℝ)
  (a A : ℝ)
  : ConvergentFunByCauchyOverToEq U (f) a A
    ↔
    ConvergentFunByHeineOverToEq U (f) a A
  := by
  sorry

def
  ConvergentFunOverToEq
  (U : Set ℝ)
  (f : ℝ → ℝ)
  (a A : ℝ)
  :=
  ConvergentFunByCauchyOverToEq U f a A


def
  BoundedFun
  (U : Set ℝ)
  (f : ℝ → ℝ)
  :=
  ∃ A : ℝ,
  ∀ x ∈ U,
  |f x| ≤ A

def
  InfinitelySmallFun
  (U : Set ℝ)
  (f : ℝ → ℝ)
  (a : ℝ)
  := ConvergentFunByCauchyOverToEq U f a 0

theorem
  conv_fun_alt_def_by_infsm_fun
  (U : Set ℝ)
  (f : ℝ → ℝ)
  :
  ConvergentFunOverToEq U f a A
  ↔
  ∃ r : ℝ → ℝ,
  InfinitelySmallFun U r a
  → ∀ x : U,
  f x = A + r x
  := by
  sorry


theorem
  bound_fun_mul_infsm_fun_is_infsm
  (U : Set ℝ)
  (f g: ℝ → ℝ)
  (f_infsm : InfinitelySmallFun U f f_a)
  (g_bound : BoundedFun U g)
  : InfinitelySmallFun
      U (fun x : ℝ ↦ (f x) * (g x)) f_a
  := by
  sorry


theorem
  first_wonderful_limit
  (U : Set ℝ)
  : ConvergentFunOverToEq U (fun x : ℝ ↦ (Real.sin x)/x) 0 1
  := by
  sorry

/-
theorem
  second_wonderful_limit
  (U : Set ℝ)
  : ConvergentFunOverToEq U (fun x : U ↦ (1 + x)^(1/x)) 0 (Real.exp 1)
  := by
  sorry
-/

-- There must be Properties of Infintely small functions

-- h = o(g)
def
  OhSmallOverOfTo
  (U : Set ℝ)
  (h g : ℝ → ℝ)
  (a : ℝ)
  := ConvergentFunOverToEq U (fun x : ℝ ↦ (h x)/(g x)) a 0



theorem
  oh_small_mul_oh_small
  (g1_o : OhSmallOverOfTo U g1 f a)
  (g2_o : OhSmallOverOfTo U g2 f a)
  : OhSmallOverOfTo U (fun x : ℝ ↦ (g1 x) * (g2 x)) f a
  := by
  sorry

def
  ContinousFunOver
  (U : Set ℝ)
  (f : ℝ → ℝ)
  :=
  ∀ x ∈ U,
  ConvergentFunOverToEq U f x (f x)

-- Here must be some properties of continous function



theorem
  Bolzano_pos_sign_keeping_theorem
  (f_cont : ContinousFunOver U f)
  (x : U)
  (fx_ne_zero : f x > 0)
  :
  ∃ a b : ℝ,
  ∀ y ∈ Set.Ioo a b,
  f y > 0
  :=
  sorry

theorem
  Bolzano_neg_sign_keeping_theorem
  (f_cont : ContinousFunOver U f)
  (x : U)
  (fx_ne_zero : f x < 0)
  :
  ∃ a b : ℝ,
  ∀ y ∈ Set.Ioo a b,
  f y < 0
  :=
  sorry

theorem
  intermediate_value_theorem_pos_neg
  (f_cont : ContinousFunOver (Set.Icc a b) f)
  (f_a_pos : f a > 0)
  (f_b_neg : f b < 0)
  :
  ∃ c ∈ Set.Icc a b,
  f c = 0
  := by
  sorry

theorem
  intermediate_value_theorem_neg_pos
  (f_cont : ContinousFunOver (Set.Icc a b) f)
  (f_a_neg : f a < 0)
  (f_b_pos : f b > 0)
  :
  ∃ c ∈ Set.Icc a b,
  f c = 0
  := by
  sorry


theorem
  second_Bolzano_theorem
  (f_cont : ContinousFunOver (Set.Icc a b) f)
  (f_a_eq_A : f a = A)
  (f_b_eq_B : f b = B)
  (A_lt_C : A < C)
  (C_lt_B : C < B)
  :
  ∃ c ∈ Set.Icc a b,
  f c = C
  := by
  sorry

-- theorem img_of_Ioo_through_cont_fun_is_interval
-- theorem img_of_Icc_through_cont_fun_is_interval


theorem
  local_boundedness_of_cont_fun_on_interval
  (f_cont : ContinousFunOver (Set.Icc a b) f)
  :
  BoundedFun (Set.Icc a b) f
  := by
  sorry

theorem
  extreme_value_theorem
  (f_cont : ContinousFunOver (Set.Icc a b) f)
  :
  ∃ c d : ℝ,
  ∀ x ∈ Set.Icc a b,
  f c ≤ f x ∧ f x ≤ f d
  := by
  sorry


#check DifferentiableOn
def
  HasDerivativeOverInOf
  (U D : Set ℝ)
  (deriv_f f : ℝ → ℝ)
  :=
  ∀ a ∈ D,
  ConvergentFunOverToEq
    U
    (fun h : ℝ ↦ (f (a + h) - f a)/h)
    0
    (deriv_f a)


theorem
  power_deriv
  (f_def_over : Set ℝ)
  (diff_over : Set ℝ)
  (n : ℕ)
  : HasDerivativeOverInOf
    f_def_over
    diff_over
    (fun x : ℝ ↦ n * x^(n-1))
    (fun x : ℝ ↦ x^n)
  := by
  sorry

-- There must be other proofs for differentiation


/-
###########################################
###########################################
########?????????????######################
###########################################
###########################################
-/

/-
universe u u' v w

/-- `Matrix m n R` is the type of matrices with entries in `R`, whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m → n → α

-/

#check Matrix

-- TODO: find already proven theorems from
-- the Lean site no a page with 100 (or 1000 - there are both)
-- theorems

/-
###########################################
###########################################
########Complex analysis###################
###########################################
###########################################
-/

#check mk_complex
#check Complex.continuous_sin
#check Continuous

#check Differentiable


-- Liouville's theorem
#check Differentiable.apply_eq_apply_of_bounded

-- Abel's theorem (Not found - Maybe update Mathlib?)
--#check Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone

-- Cauchy integral theorem
#check Complex.circleIntegral_div_sub_of_differentiable_on_off_countable



-- TODO: find already proven theorems from
-- the Lean site no a page with 100 (or 1000 - there are both)
-- theorems
