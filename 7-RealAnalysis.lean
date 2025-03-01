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
  ∀ ε > 0,
  ∃ N,
  ∀ n ≥ N,
  |s n - a| < ε

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

/-
Show that this definition is equivalent to
-/

theorem
  conv_seq_to_unique
  (s_conv : ConvergentSeqTo s a)
  : ∀ b : ℝ,
    ConvergentSeqTo s b
    → a = b
  := by
  sorry

theorem
  conv_seq_to_bounded
  (s_conv : ConvergentSeqTo s a)
  : BoundedSeq s
  := by
  sorry

theorem
  exists_conv_seq_to_with_const_mul
  (s : ℕ → ℝ)
  (a : ℝ)
  (a_ne_zero : a ≠ 0)
  : ∃ s' : ℕ → ℝ,
    ∀ n : ℕ,
    s n = a * s' n
  := by
  by_contra goal
  push_neg at goal
  specialize goal (fun n ↦ a⁻¹ * s n)
  obtain ⟨n, goal⟩ := goal
  rw [ne_eq] at goal
  rw [← mul_assoc] at goal
  rw [mul_inv_cancel₀ a_ne_zero, one_mul] at goal
  have counter_goal : s n = s n := by
    rfl
  contradiction

theorem
  const_move_out
  (b : ℝ)
  : ConvergentSeqTo s a
    ↔ ConvergentSeqTo (fun n : ℕ ↦ b * s n ) (b * a)
  := by
  constructor
  . intro s_a_conv
    intro ε ε_gt_0
    dsimp
    use 1
    intro n n_ge_1
    sorry -- TODO: easy to continue
  . intro bs_ba_conv ε ε_gt_0
    specialize bs_ba_conv ε ε_gt_0
    obtain ⟨N,bs_ba_conv⟩ := bs_ba_conv
    use N
    intro n n_ge_N
    specialize bs_ba_conv n n_ge_N
    dsimp at bs_ba_conv
    sorry -- TODO: easy to continue




theorem
  conv_seq_to_const
  (a : ℝ)
  : ConvergentSeqTo (fun x : ℕ ↦ a) a
  := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem
  conv_seq_to_add
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


-- https://brandonrozek.com/blog/lean4-tutorial/
#check Exists.intro
#check Exists.elim



theorem
  conv_seq_to_minus
  {s t r : ℕ → ℝ}
  {a b : ℝ}
  (cs : ConvergentSeqTo s a)
  (ct : ConvergentSeqTo t b)
  (r_eq : ∀ n : ℕ, r n = s n - t n)
  : ConvergentSeqTo
      (fun n ↦ s n - t n)
      (a - b)
  := by
  have minus_one_ne_zero : (-1 : ℝ) ≠ 0 := by
    linarith
  have t'_eq : ∃ t' : ℕ → ℝ,
                ∀ n : ℕ,
                t n = (-1) * t' n
    := exists_conv_seq_to_with_const_mul (t) (-1) minus_one_ne_zero
  obtain ⟨t', t'_eq⟩ := t'_eq
  intro ε ε_gt_0
  dsimp
  use 1
  intro n n_gt_0
  specialize t'_eq n
  rw [t'_eq]
  simp




  sorry





theorem
  conv_seq_to_div
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
  ConvergentFunByCauchyTo
  {U : Set ℝ}
  (f : U → ℝ)
  (a A : ℝ)
  :=
  ∀ ε > 0,
  ∃ δ > 0,
  ∀ x : U,
  |x - a| < δ
  → |A - f x| < ε


def
  ConvergentFunByHeineTo
  {U : Set ℝ}
  (f : U → ℝ)
  (a A : ℝ)
  :=
  ∀ ε > 0,
  ∀ s : ℕ → U,
  ConvergentSeqTo (fun n : ℕ ↦ s n) a
  → ConvergentSeqTo
      (fun n : ℕ ↦ f (s n)) A


theorem
  heine_def_eq_cauchy_def
  {U : Set ℝ}
  (f : U → ℝ)
  (a A : ℝ)
  : ConvergentFunByCauchyTo (f) a A
    ↔
    ConvergentFunByHeineTo (f) a A
  := by
  sorry

def
  ConvergentFunTo
  {U : Set ℝ}
  (f : U → ℝ)
  (a A : ℝ)
  :=
  ConvergentFunByCauchyTo f a A


def
  BoundedFun
  {U : Set ℝ}
  (f : U → ℝ)
  :=
  ∃ A : ℝ,
  ∀ x : U,
  |f x| ≤ A

def
  InfinitelySmallFun
  {U : Set ℝ}
  (f : U → ℝ)
  (a : ℝ)
  := ConvergentFunTo f a 0

theorem
  conv_fun_alt_def_by_infsm_fun
  (U : Set ℝ)
  (D : Set U)
  (f : U → ℝ)
  :
  ConvergentFunTo f a A
  ↔
  ∃ r : U → ℝ,
  InfinitelySmallFun r a
  → ∀ x : U,
  f x = A + r x
  := by
  sorry


theorem
  bound_fun_mul_infsm_fun_is_infsm
  {U : Set ℝ}
  (f g: U → ℝ)
  (f_infsm : InfinitelySmallFun f f_a)
  (g_bound : BoundedFun g)
  : InfinitelySmallFun
      (fun x : U ↦ (f x) * (g x)) f_a
  := by
  sorry


theorem
  first_wonderful_limit
  {U : Set ℝ}
  : ConvergentFunTo (fun x : U ↦ (Real.sin x)/x) 0 1
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
  OhSmallTo
  {U : Set ℝ}
  (h g : U → ℝ)
  (a : ℝ)
  := ConvergentFunTo (fun x : U ↦ (h x)/(g x)) a 0



theorem
  oh_small_mul_oh_small
  {U : Set ℝ}
  {f g1 g2 : U → ℝ}
  (g1_o : OhSmallTo g1 f a)
  (g2_o : OhSmallTo g2 f a)
  : OhSmallTo (fun x : U ↦ (g1 x) * (g2 x)) f a
  := by
  sorry

def
  ContinousFunAt
  {U : Set ℝ}
  (f : U → ℝ)
  (x : U)
  :=
  ConvergentFunTo (f) x (f x)

def
  ContinousFun
  {U : Set ℝ}
  (f : U → ℝ)
  :=
  ∀ x : U,
  ContinousFunAt f x

-- Here must be some properties of continous function



theorem
  Bolzano_pos_sign_keeping_theorem
  {U : Set ℝ}
  {f : U → ℝ}
  (f_cont : ContinousFun f)
  (x : U)
  (fx_ne_zero : f x > 0)
  :
  ∀ a b : U,
  x ∈ Set.Ioo a b
  →
  ∀ y ∈ Set.Ioo a b,
  f y > 0
  :=
  sorry

theorem
  Bolzano_neg_sign_keeping_theorem
  {U : Set ℝ}
  {f : U → ℝ}
  (f_cont : ContinousFun f)
  (x : U)
  (fx_ne_zero : f x < 0)
  :
  ∀ a b : U,
  x ∈ Set.Ioo a b
  →
  ∀ y ∈ Set.Ioo a b,
  f y > 0
  :=
  sorry

theorem
  intermediate_value_theorem_pos_neg
  {U : Set ℝ}
  {f : U → ℝ}
  (f_cont : ContinousFun f)
  {a b : U}
  (f_a_pos : f a > 0)
  (f_b_neg : f b < 0)
  :
  ∃ c ∈ Set.Icc a b,
  f c = 0
  := by
  sorry

theorem
  intermediate_value_theorem_neg_pos
  {U : Set ℝ}
  {f : U → ℝ}
  (f_cont : ContinousFun f)
  {a b : U}
  (f_a_pos : f a > 0)
  (f_b_neg : f b < 0)
  :
  ∃ c ∈ Set.Icc a b,
  f c = 0
  := by
  sorry


theorem
  second_Bolzano_theorem
  {U : Set ℝ}
  {f : U → ℝ}
  (f_cont : ContinousFun f)
  {a b : U}
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
  {a b : ℝ}
  {f : Set.Icc a b → ℝ}
  (f_cont : ContinousFun f)
  :
  BoundedFun f
  := by
  sorry

theorem
  extreme_value_theorem
  {a b : ℝ}
  {f : Set.Icc a b → ℝ}
  (f_cont : ContinousFun f)
  :
  ∃ c d : Set.Icc a b,
  ∀ x : Set.Icc a b,
  f c ≤ f x ∧ f x ≤ f d
  := by
  sorry



#check DifferentiableOn
def
  HasDerivative
  {U : Set ℝ}
  (f deriv_f : U → ℝ)
  :=
  ∀ a : U,
  ∃ g : U → ℝ,
  OhSmallTo g f a
  →
  ∀ x : U,
  f x - f a = (deriv_f a) * (x - a) + g x



theorem
  power_deriv
  {U : Set ℝ}
  (n : ℕ)
  : HasDerivative
    (fun x : U ↦ x^(n+1))
    (fun x : U ↦ (n+1) * x^n)
  := by
  sorry

-- There must be other proofs for differentiation

def
  HasIndefiniteIntegral
  {U : Set ℝ}
  (f ind_int_f: U → ℝ)
  := HasDerivative ind_int_f f


def
  Partition
  {U : Set ℝ}
  (a b : ℝ)
  (N : ℕ)
  (s : ℕ → U)
  :=
  ∀ n : ℕ,
  n ≤ N-1
  →
  s n ≤ s (n+1)
  ∧
  s 1 = a
  ∧
  s N = b


def
  MeshForPartition
  {U : Set ℝ}
  (q : ℝ)
  (N : ℕ)
  (s : ℕ → U)
  :=
  ∀ n : ℕ,
  n ≤ N-1
  →
  |(s n).val - (s (n+1)).val| ≤ q


def
  TagsForPartition
  {U : Set ℝ}
  (tag : ℕ → U)
  (N : ℕ)
  (s : ℕ → U)
  :=
  ∀ n : ℕ,
  n ≤ N-1
  →
  s n ≤ tag n
  ∧
  tag n ≤ s (n+1)

def
  HasDefiniteIntegral
  {U : Set ℝ}
  (a b : U)
  (f : U → ℝ)
  (integral_of_f : ℝ)
  :=
  ∀ ε > 0,
  ∃ δ > 0,
  ∀ s : ℕ → U,
  ∃ N : ℕ,
  ∃ tag : ℕ → U,
  ∃ q : ℝ,
  Partition a b N s
  ∧
  TagsForPartition tag N s
  ∧
  MeshForPartition q N s
  ∧
  q < δ
  →
  |integral_of_f
  - ∑ k in Set.Icc 1 (N-1),
    ((s (k+1) - s k) * f (tag k) )|
  < ε


theorem
  def_int_in_point
  {U : Set ℝ}
  {a b : U}
  {f : U → ℝ}
  (def_int : HasDefiniteIntegral a a f f_int)
  : f_int = 0
  := by
  sorry





theorem
  def_int_of_one
  {U : Set ℝ}
  {a b : U}
  (def_int : HasDefiniteIntegral a b (fun x : U ↦ 1) f_int)
  : f_int = b - a
  := by
  sorry



/-
!!!! TODO: Serious problem:
Partitions in def_int definition
assumed to have property "s n ≤ s (n+1)"
so I should add to HasDefiniteIntegral
definition case when a > b
(look how same wath done
using match cases for natural numbers...)
-/
theorem
  def_int_swap_interval_borders
  {U : Set ℝ}
  {a b : U}
  {f : U → ℝ}
  (def_int : HasDefiniteIntegral a b f f_int)
  : HasDefiniteIntegral b a f (-f_int)
  := by
  sorry

theorem
  def_int_const_out
  {U : Set ℝ}
  {a b : U}
  {f : U → ℝ}
  (c : U)
  (def_int : HasDefiniteIntegral a b (fun x : U ↦ c * f x) f_int)
  : HasDefiniteIntegral b a f (c*f_int)
  := by
  sorry

--theorem def_int_sum...


def
  HasNDerivatives
  {U : Set ℝ}
  (f : U → ℝ)
  (derivs : ℕ → U → ℝ)
  (N : ℕ)
  :=
  f = derivs 0
  ∧
  ∀ n : ℕ,
  n ≤ N
  →
  HasDerivative (derivs n) (derivs (n+1))


/-
Ordinary Differential Equation
of Nth order
-/
def
  ODEN
  {U : Set ℝ}
  (y : U → ℝ)
  (y_derivs : ℕ → U → ℝ)
  (N : ℕ)
  (f : ℕ → (ℕ → U → ℝ) → U → ℝ)
  (g : U → ℝ)
  :=
  HasNDerivatives y y_derivs N
  ∧
  f N y_derivs = g

/-
Linear Ordinary Differential Equations
-/
def
  LODEN
  {U : Set ℝ}
  (y : U → ℝ)
  (y_derivs : ℕ → U → ℝ)
  (N : ℕ)
  (f : ℕ → (ℕ → U → ℝ) → U → ℝ)
  (g : U → ℝ)
  :=
  ODEN y y_derivs N f g
  ∧
  ∃ p : ℕ → U → ℝ,
  ∀ x : U,
  (f N y_derivs) x
  = (y_derivs N) x
  + (∑ k in Set.Icc 0 (N-1),
      (p k x) * (y_derivs k x))




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
