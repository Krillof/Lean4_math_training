import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always


-- Let's use thouse as a starting point
#check Classical.axiomOfChoice
#check Classical.choice
#check propext -- Propositional extensionality
#check funext -- Function extensionality
#check Classical.em

#check Not.intro

#check Or
#check Or.inl
#check Or.inr

#check And
#check And.left
#check And.right

-- Imp and iff
#check Classical.or_iff_not_imp_left
#check Classical.or_iff_not_imp_right
#check Iff.intro
#check Iff.mp
#check Iff.mpr

-- About exists and forall
#check Classical.choose
#check not_exists -- As forall def



-- All ↔ theorems can be changed using dot
#check Classical.or_iff_not_imp_left.mp -- (a ↔ b) → a → b
#check Classical.or_iff_not_imp_left.mpr -- (a ↔ b) → b → a
#check Classical.or_iff_not_imp_left.not -- (a ↔ b) → (¬a ↔ ¬b)
#check Classical.or_iff_not_imp_left.not.mp
#check Classical.or_iff_not_imp_left.not.mpr
#check Classical.or_iff_not_imp_right

-------------------------------
-- Theorems
-------------------------------
-- Unfortanutely I may look more closely at fundamentals later
--    but I don't know for sure...



#check Classical.not_not
example
  (p : Prop)
  : ¬¬p ↔ p
  := by
  constructor
  . contrapose!
    intro h
    exact h
  . intro h
    by_contra q
    contradiction



#check Classical.exists_or_forall_not
example
  (p : α → Prop)
  : (∃ a, p a) ∨ ∀ (a : α), ¬p a
  := by
  by_cases h : ∃ a, p a
  . left
    exact h
  . right
    apply not_exists.mp h


#check Classical.not_forall_not
