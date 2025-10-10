/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! Show that any map from a terminal object in a category to an initial one is an isomorphism.-/

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v, u} C] (x y : C)

theorem cat4 (hx : Limits.IsTerminal x) (hy : Limits.IsInitial y) (f : x ⟶ y) :
    IsIso f := by
  rcases hx with ⟨lift, h, hx⟩
  rcases hy with ⟨desc, h', hy⟩
  clear h h'
  simp only [Limits.asEmptyCone_pt, Limits.asEmptyCone_π_app, Functor.const_obj_obj, Discrete.mk_as,
    id_eq, IsEmpty.forall_iff, forall_const, Limits.asEmptyCocone_pt, Limits.asEmptyCocone_ι_app] at *
  constructor
  use lift (Limits.asEmptyCone y); constructor
  · specialize hx (Limits.asEmptyCone x)
    cat_disch
  specialize hy (Limits.asEmptyCocone y)
  cat_disch
