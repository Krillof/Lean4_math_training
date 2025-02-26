import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always
open Set


#check univ
#check mem_union
#check subset_def
#check union_def
#check inter_def



/-
###################################################
#############Unions and intersections##############
###################################################
-/


/-
theorem
-/
#check and_comm
#check inter_comm
theorem my_inter_comm
  {α : Type*} (s t : Set α)
  : s ∩ t = t ∩ s := by
  ext x
  /-
  x : α
  ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  -/
  simp [and_comm]


#check mem_inter_iff
example {α : Type*} (s t : Set α)
  : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

/-
theorem
-/
#check union_comm
example {α : Type u} (a b : Set α)
  : a ∪ b = b ∪ a := by
  ext x
  /-
  x : α
  ⊢ x ∈ a ∪ b ↔ x ∈ b ∪ a
  -/
  simp [or_comm]

#check union_def
example {α : Type u} (a b : Set α)
  : a ∪ b = b ∪ a := by
  ext x
  simp [union_def]
  constructor
  . rintro xa_or_xb
    sorry
  . sorry

/-
theorem
-/
#check union_inter_distrib_left
example {α : Type u} (s t u : Set α)
  : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) := by
  ext x
  constructor
  . intro x_sutnu
    constructor
    . left
      sorry
    . sorry
  . sorry

#check union_inter_distrib_right


/-
theorem
-/
#check inter_union_distrib_left
#check inter_union_distrib_right


/-
###################################################
#############Subsets###############################
###################################################
-/
#check Subset.antisymm

/-
###################################################
#############Infinite unions and intersections#####
###################################################
-/

example {α I : Type*} (A : I → Set α) (s : Set α)
  : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example  {α I : Type*} (A B : I → Set α) (s : Set α)
  : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i

/-
###################################################
#############Functions#############################
###################################################
-/

/-
Here f ⁻¹' is an inverse image
-/
example
  {α β : Type*} (f : α → β) (u  : Set β)
 : f ⁻¹' u = {x | f x ∈ u} := by
  rfl


example
  {α β : Type*} (f : α → β) (u v : Set β)
 : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

/-
And f '' is an image
-/
example
  {α β : Type*} (f : α → β) (s : Set α)
  : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := by
  rfl

example
  {α β : Type*} (f : α → β) (s t : Set α)
 : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

#check mem_image_of_mem
