import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always

open Filter Topology MeasureTheory intervalIntegral

/-
-----------------------------------------
                  Topology
-----------------------------------------
-/

#check TopologicalSpace
#check IsOpen
#check isOpen_sUnion -- first axiom
#check isOpen_biUnion -- alternative equivalent first axiom
#check isOpen_univ -- second axiom
#check IsOpen.inter -- third axiom



#check nhds
/- A set is called a neighborhood of `x` if it contains
an open set around `x`. The set of all
neighborhoods of `x` forms a filter,
the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`.

irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s
-/

#check 𝓝 -- \nhds → 𝓝
#check interior_eq_nhds -- as def
#check interior
/- The interior of a set `s` is the largest open subset of `s`.
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
-/
#check closure
/-
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
-/
#check frontier
/-
def frontier (s : Set X) : Set X :=
  closure s \ interior s
-/
-- def exterior (s : Set X) : Set X := (𝓝ˢ s).ker


#check Dense
/-
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
-/


/- A filter `F` on a type `α`
is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is
stable under intersection. We do not forbid this collection to be
all sets of `α`.

structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
-/

/-
!!! There is
protected theorem mem_sets : s ∈ f.sets ↔ s ∈ f...
-/


/-
The *kernel* of a filter is the intersection of all its sets.

def ker (f : Filter α) : Set α := ⋂₀ f.sets
-/

/- A filter is `NeBot` if it is not
equal to `⊥`, or equivalently the empty set does not belong to
the filter. Bourbaki include this assumption
in the definition of a filter but we prefer to have a
`CompleteLattice` structure on `Filter _`,
so we use a typeclass argument in lemmas instead.

class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥
-/


/- `f.Eventually p` or `∀ᶠ x in f, p x`
mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in atTop, p x`
means that `p` holds true for sufficiently large `x`.

protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f


@[inherit_doc Filter.Eventually]
notation3 "∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r
-/


/- `f.Frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`.
E.g., `∃ᶠ x in atTop, p x`
means that there exist arbitrarily large `x` for which `p` holds true.

protected def Frequently (p : α → Prop) (f : Filter α) : Prop :=
  ¬∀ᶠ x in f, ¬p x

@[inherit_doc Filter.Frequently]
notation3 "∃ᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r
-/


/- `Filter.Tendsto` is the generic "limit of a function" predicate.
  `Tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood.

def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂
-/

/- `f.IsBounded r`: the filter `f` is eventually bounded w.r.t. the relation `r`,
i.e. eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `(· ≤ ·)` or `(· ≥ ·)`.

def IsBounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ᶠ x in f, r x b
-/

/- `IsCobounded (≺) f` states that the filter `f` does not tend to infinity w.r.t. `≺`. This is
also called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.IsCobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀ a, ∀ᶠ n in f, a ≤ n`
would not work as well in this case.

def IsCobounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ a, (∀ᶠ x in f, r x a) → r b a

-/

-- \allf → ∀ᶠ
#check isOpen_iff_eventually


#check AccPt
/- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.
See also `ClusterPt`.

def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)
-/

#check ClusterPt
/- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`.
Also known as an accumulation point or a limit point, but beware that terminology varies.
This is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`, which is called `AccPt` in Mathlib.
See `mem_closure_iff_clusterPt` in particular.

def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
-/


/- Two points `x` and `y` in a topological space are `Inseparable` if any of the following
equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_forall_isOpen`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_forall_isClosed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.

def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y
-/
#check Inseparable

#check IsCompact
#check isCompact_iff_finite_subcover -- We will use this as def


/- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`.

@[fun_prop]
def ContinuousAt (f : X → Y) (x : X) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
-/

/- A function between topological spaces is continuous
at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while
staying within `s`.

@[fun_prop]
def ContinuousWithinAt (f : X → Y) (s : Set X) (x : X) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))
-/

/- A function between topological spaces
is continuous on a subset `s`
when it's continuous at every point of `s` within `s`.

@[fun_prop]
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x
-/


/-
-----------------------------------------
               Metric Geometry
-----------------------------------------
-/

#check MetricSpace
#check dist
#check dist_comm -- first axiom
#check dist_triangle -- second axiom
#check dist_nonneg -- third axiom
#check dist_eq_zero -- fourth axiom

-- MetricSpace is topological (It's T0 space, so it's topological space)
#check MetricSpace.instT0Space



#check Cauchy -- Generalization of CauchySeq
/- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence.

def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α
-/
#check Metric.cauchy_iff

/-
A set `s` is called *complete*, if any
Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it
satisfies `f ≤ 𝓝 x` for some `x ∈ s`).

def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x
-/
#check CompleteSpace
#check CompleteSpace.complete -- def
#check IsClosed.isComplete

#check CauchySeq
#check cauchySeq_bdd -- Cauchy seq is bounded

#check TotallyBounded
/-
def TotallyBounded (s : Set α) : Prop :=
  ∀ d ∈ 𝓤 α, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d }
-/

#check TotallyBounded.closure


#check Metric.ball
#check Metric.ball_subset





/-
-----------------------------------------
               Vector Spaces
-----------------------------------------
-/

section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

end


/-
-----------------------------------------
               Normed Spaces
-----------------------------------------
-/

#check NormedSpace
#check norm -- use ‖...‖ where \|| → ‖
#check norm_smul -- axiom for a normed space
#check dist_eq_norm


/-
-----------------------------------------
               Measurable space
-----------------------------------------
-/
#check MeasurableSpace
#check MeasurableSet
#check MeasurableSet.empty -- first axiom
#check MeasurableSet.compl -- second axiom
#check MeasurableSet.iUnion -- third axiom


#check Measure
#check measure_eq_iInf -- ???
#check Measure.m_iUnion
#check measure_iUnion_le
section
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
end




-- Deriving from axioms:
#check MeasurableSet.univ
#check MeasurableSet.iInter
#check MeasurableSet.union
#check MeasurableSet.inter

#check ae -- almost everywhere
#check ae.eq_1
