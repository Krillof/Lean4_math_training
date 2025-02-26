import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always
open Set
open Function
open Finset


#check Ordinal.card_mul
/-
(a b : Ordinal.{u_4})
: (a * b).card = a.card * b.card
-/

#check Ordinal.card_add
/-
(o₁ o₂ : Ordinal.{u_3})
: (o₁ + o₂).card = o₁.card + o₂.card
-/


/-
Look in Nat.Choose.Basic
-/

#check Nat.choose

/-
/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. -/
def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)
-/

#eval Nat.choose 3 2 -- 3


#check Nat.choose_zero_right
-- (n : ℕ) : n.choose 0 = 1

#check Nat.choose_zero_succ
-- (k : ℕ) : Nat.choose 0 k.succ = 0

#check Nat.choose_self
-- (n : ℕ) : n.choose n = 1

#check Nat.choose_eq_zero_of_lt
-- {n k : ℕ} : n < k → n.choose k = 0

#check Nat.choose_eq_factorial_div_factorial
/-
{n k : ℕ} (hk : k ≤ n) :
  n.choose k =
    n.factorial
    / (k.factorial * (n - k).factorial)
-/


#check Nat.choose_symm
/-
{n k : ℕ} (hk : k ≤ n) :
  n.choose (n - k) = n.choose k
-/




#check Nat.multichoose
/-
def multichoose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 =>
    multichoose n (k + 1) + multichoose (n + 1) k
-/

#check Nat.multichoose_zero_right
-- (n : ℕ) : n.multichoose 0 = 1

#check Nat.multichoose_zero_succ
-- (k : ℕ) : Nat.multichoose 0 (k + 1) = 0

#check Nat.multichoose_two
-- (k : ℕ) : Nat.multichoose 2 k = k + 1



#check Nat.multichoose_eq
-- (n k : ℕ) : n.multichoose k = (n + k - 1).choose k




/-
Binominal theorem!
-/

#check add_pow
/-
{R : Type u_1} [CommSemiring R]
(x y : R) (n : ℕ) :
  (x + y) ^ n =
  ∑ m ∈ Finset.range (n + 1),
    x ^ m * y ^ (n - m) * (n.choose m)
-/





#check Equiv.Perm
/-
Bijections of type to itself
-/

#check permsOfFinset
/-
It's definition here is more complicated...
-/


#check mem_perms_of_finset_iff
/-
As definition we can use this

[DecidableEq α] {s : Finset α} {f : Equiv.Perm α} :
  f ∈ permsOfFinset s ↔ ∀ {x : α}, f x ≠ x → x ∈ s
-/


#check card_perms_of_finset
/-
[DecidableEq α] (s : Finset α)
: (permsOfFinset s).card = s.card.factorial
-/


/- When `s` is a finset,
 `s.powerset` is the finset
 of all subsets of `s` (seen as finsets).
-/
#check Finset.powerset

#check Finset.mem_powerset -- use as definition!
-- {s t : Finset α} : s ∈ t.powerset ↔ s ⊆ t

#check Finset.empty_mem_powerset
-- (s : Finset α) : ∅ ∈ s.powerset

#check Finset.mem_powerset_self
-- (s : Finset α) : s ∈ s.powerset

#check Finset.powerset_mono
-- {s t : Finset α} : s.powerset ⊆ t.powerset ↔ s ⊆ t

#check Finset.powerset_eq_singleton_empty
-- {s : Finset α} : s.powerset = {∅} ↔ s = ∅

#check Finset.card_powerset
-- (s : Finset α) : #s.powerset = 2 ^ #s


/- Given an integer `n`
and a finset `s`, then `powersetCard n s`
is the finset of subsets of `s`
of cardinality `n`.
-/
#check powersetCard
--  (n : ℕ) (s : Finset α) : Finset (Finset α)

#check mem_powersetCard -- use as definition
/-
{n : ℕ} {s t : Finset α}
: s ∈ powersetCard n t ↔ s ⊆ t ∧ #s = n
-/

#check card_powersetCard
/-
(n : ℕ) (s : Finset α)
: #(powersetCard n s) = (#s).choose n
-/



/-
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
Bad attempts:
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-------------------------
-/



/-
-- Short name: kcomb
structure
  kCombinationOf
  (kcomb s : Finset α)
  (k : ℕ)
  where
  kcomb_is_subs : kcomb ⊆ s
  kcomb_has_card : kcomb.card = k


-- Short name: kcombs
structure
  kCombinationsOf
  (kcombs : Finset (Finset α))
  (s : Finset α)
  (k : ℕ)
  where
  -- Opening
  kcombs_def : ∀ kcomb ∈ kcombs, kCombinationOf kcomb s k


-- Short name: am_of_kcombs
structure
  AmountOfkCombinationsOf
  (am_of_kcombs : ℕ)
  (_kcombs : kCombinationsOf kcombs s k)
  where
  am_of_kcombs_defintion : kcombs.card = val





theorem
  calc_am_of_kcombs
  {_kcombs : kCombinationsOf kcombs s k}
  {_am_of_kcombs : AmountOfkCombinationsOf am_of_kcombs _kcombs}
  : am_of_kcombs =
    s.card.factorial
    / (k.factorial
        * (s.card - k).factorial)
  := by
  induction k with
  | zero => dsimp
            -- ⊢ am_of_kcombs = s.card.factorial
            --    / (1 * s.card.factorial)
            rw [
              one_mul,
              Nat.div_self
            ]
            -- ⊢ am_of_kcombs = 1
            have a := _kcombs.kcombs_def
            -- a : ∀ kcomb ∈ kcombs, kCombinationOf kcomb s 0
            specialize a ∅
            -- a : ∅ ∈ kcombs → kCombinationOf ∅ s 0
            have b : ∅ ∉ kcombs := by
              by_contra contr
              have ba := a contr
              -- ba : kCombinationOf ∅ s 0
              sorry
            by_contra contr

  | succ k' h => sorry

-/






















/-
Short names for theorems:
combs - combinations
am - amount

-/









/-
def
  iskCombinationOf
  {α : Type*}
  (comb s : Finset α)
  (k : ℕ)
  := comb ⊆ s ∧ comb.card = k

def
  kCombinationsAmount
  {α : Type*}

-/



/-
-- m-combination set
def kCombinationsSet
  {α : Type*}
  (s : Finset α)
  (k : ℕ)
  := { t ∈ s.powerset
      | t.card = k}

def CombinationsSet
  {α : Type*}
  (s : Finset α)
  := kCombinationsSet s s.card

-- m-combinations amount
def kCombinationsAmount
  {α : Type*}
  (s : Finset α)
  (m : ℕ)
  := (kCombinationsSet s m).card


/-
Short names for theorems:
combs - combinations
am - amount

-/



#check Finset.card_eq_zero
#check Finset.card_eq_zero.not.mpr
#check Finset.nonempty_iff_ne_empty
#check Finset.mem_filter -- !!!
#check Finset.card_le_card
#check Finset.card_lt_card
#check Finset.eq_iff_card_le_of_subset
#check Nat.ne_zero_iff_zero_lt



#check Nat.factorial
#check Nat.factorial_mul_descFactorial

#check mem_powerset
#check subset_of_mem_powerset
#check Finset.mem_powerset -- !!!

#check Fin.eq_of_val_eq
#check Eq.refl

#check Iff.trans

#check not_le_of_lt

#check Set.not_mem_empty

-- ↑ = \u

--#eval (-1).factorial

-- Completed proof!
theorem
  k_combs_am_gt_set_card_eq_zero
  {_ : Type*}
  (h : s.card < m)
  : kCombinationsAmount s m = 0
  := by
  rw [
    kCombinationsAmount
  ]
  -- ⊢ (kCombinationsSet s m).card = 0
  apply Finset.card_eq_zero.mpr
  -- ⊢ kCombinationsSet s m = ∅
  rw [
    kCombinationsSet
  ]
  -- Finset.filter (fun t ↦ t.card = m) s.powerset = ∅
  ext x -- !!!
  -- x ∈ Finset.filter (fun t ↦ t.card = m) s.powerset ↔ x ∈ ∅
  apply Iff.trans Finset.mem_filter
  constructor
  . intro g
    rcases g with ⟨g1, g2⟩
    /-
      g1 : x ∈ s.powerset
      g2 : x.card = m
    -/
    have g11 : x ⊆ s := by
      apply Finset.mem_powerset.mp g1
    rw [<- g2] at h
    -- h : s.card < x.card
    have z : x.card ≤ s.card := by
      apply Finset.card_le_card g11
    -- z : x.card ≤ s.card
    apply not_le_of_lt at h
    -- h : ¬x.card ≤ s.card
    contradiction
  . intro g
    -- g : x ∈ ∅
    have contradicting : x ∉ ∅
      := Set.not_mem_empty x
    contradiction



theorem
  emptyset_in_k_combs_set
  : ∅ ∈ kCombinationsSet s m
  := by
  rw [kCombinationsSet]


#check Finset.card_eq_zero
#check Finset.card_eq_one
#check Set.ncard_eq_one
#check Nat.factorial_pos

#check lt_of_le_of_ne

#check Nat.lt_one_iff

theorem
  combs_am_calc
  {α : Type*}
  (h : s.Nonempty)
  : kCombinationsAmount s m
    = s.card.factorial /
        (m.factorial
         * (s.card - m).factorial)
  := by
  by_cases m_property : m = 0
  . rw [m_property]
    dsimp
    -- ⊢ kCombinationsAmount s 0
    --  = s.card.factorial / (1 * s.card.factorial)
    rw [one_mul]
    -- ⊢ kCombinationsAmount s 0
    --  = s.card.factorial / s.card.factorial
    rw [Nat.div_self <| Nat.factorial_pos s.card]
    -- ⊢ kCombinationsAmount s 0 = 1
    by_cases z : kCombinationsAmount s 0 > 1
    . -- z : kCombinationsAmount s 0 > 1
      have z1 : kCombinationsAmount s 0 > 0
        := by
        apply lt_trans zero_lt_one z
      -- z1 : kCombinationsAmount s 0 > 0
      apply Finset.card_pos.mp at z1
      -- z1 : kCombinationsAmount s 0.Nonempty
      sorry
    . apply le_of_not_lt at z
      -- z : kCombinationsAmount s 0 ≤ 1
      sorry


  . sorry








  . sorry






  . have s_card_gt_zero : 0 < s.card := by
      apply Nat.ne_zero_iff_zero_lt.mp s_card
    sorry

/-
theorem
  my_combinations_amount_calculated
  {α : Type*}
  (t : kCombinationsSet s m)
  : kCombinationsAmount s m = s.card.factorial.div (m.factorial * (s.card - m).factorial)
  := by
  by_cases s_emptiness : s.Nonempty
  .   -- s_emptiness : s.Nonempty
    have s_card_pos : 0 < s.card := by
      have h1 : s.card ≠ 0 := by
        -- Finset.card_eq_zero : s.card = 0 ↔ s = ∅
        apply Finset.card_eq_zero.not.mpr
        -- ⊢ ¬s = ∅
        -- Finset.nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅
        apply Finset.nonempty_iff_ne_empty.mp s_emptiness
      apply Nat.ne_zero_iff_zero_lt.mp h1
    induction m
    . dsimp
      rw [one_mul]
      -- kCombinationsAmount s 0 = s.card.factorial.div s.card.factorial
      dsimp [
        kCombinationsAmount
        ]
      apply Nat.div_self s_emptiness s.card.factorial

      -- (kCombinationsSet s 0).card
      --  = s.card.factorial.div s.card.factorial
      have h₁ : Fintype.card (kCombinationsSet s 0) = 0 := by
        have g₁ : kCombinationsSet s 0 = ∅ := by
          dsimp [
            kCombinationsSet
          ]


        rw [g₁]
        dsimp

    . sorry
  . sorry
-/

-- def Permutation ??


-- ?
#check List
#eval [1, 2, 3].permutations
-/
