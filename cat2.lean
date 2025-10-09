/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-! Let $\mathcal{C}$ be a category. Show that the collection of isomorphisms in $\mathcal{C}$ defines a subcategory,
the maximal groupoid inside $\mathcal{C}$. -/

open CategoryTheory

universe u v

variable (C : Type u) [Category.{v, u} C]

/-- Define the category of the maximal groupoid of a category `C` -/
def maximalGroupoid : Category.{v, u} C := {
  Hom := fun x y => Iso x y
  id := fun x => Iso.refl x
  comp := fun f g => f ≪≫ g
}

/-- Prove the maximal groupoid is a groupoid -/
theorem maximalGroupoid_isGroupoid : @IsGroupoid C (maximalGroupoid C) := by
  apply @IsGroupoid.mk C (maximalGroupoid C)
  rw [autoParam]
  dsimp [maximalGroupoid]
  intro x y f
  apply @IsIso.mk C (maximalGroupoid C)
  dsimp [maximalGroupoid]
  use f.symm; cat_disch
