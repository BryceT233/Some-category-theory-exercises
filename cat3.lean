/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-! Assuming the axiom of choice, prove that any full, faithful, and essentially surjective functor
defines an equivalence of categories.-/

open CategoryTheory

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂}
    [Category.{v₂, u₂} D] (F : Functor C D)

theorem exists_equiv (h : F.FullyFaithful) (h' : F.EssSurj) :
    ∃ e : CategoryTheory.Equivalence C D, e.functor = F := by
-- `F.map` is bijective
  have F_map_bij := h.map_bijective
-- Extend `h` to get an inverse `preimg` of `F.map`
  rcases h with ⟨preimg, h1, h2⟩
-- Use the axiom of choice to extend `h'`, we get an inverse map `invF_obj : D ⟶ C` and isomorphisms `Y ⟶ F.obj (invF_obj Y)` for all `Y` in `D`
  rcases h' with ⟨h'⟩
  simp only [Functor.essImage] at h'
  choose invF_obj h' using h'
  replace h' : ∀ (Y : D), ∃ f : Y ⟶ F.obj (invF_obj Y), IsIso f := by
    convert h' with Y; constructor
    · rintro ⟨f, hf⟩; constructor; exact {
        hom := inv f
        inv := f
      }
    rintro ⟨f⟩; use f.inv; exact Iso.isIso_inv f
  choose invF_obj_iso hinvF using h'
-- Define the inverse functor `invF`
  let invF : Functor D C := {
    obj := invF_obj
    map := fun {x} {y} f => preimg (@inv D _ _ _ (invF_obj_iso x) (hinvF x) ≫ f ≫ invF_obj_iso y)
    map_id := by
      intro; simp only [Category.id_comp, IsIso.inv_hom_id]
      rw [← F.map_id, h2]
    map_comp := by
      intros; apply (F_map_bij _ _).injective
      cat_disch
  }
-- Define the unit natural isomorphism `unitIso : 𝟭 C ≅ F ⋙ invF` that is needed to get an equivalence
  let unitIso : 𝟭 C ≅ F ⋙ invF := {
    hom := {
      app := fun _ => by
        simp only [Functor.id_obj, Functor.comp_obj]
        apply preimg; apply invF_obj_iso
      naturality := by
        simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, id_eq, Functor.comp_map]
        intro x y f; apply (F_map_bij _ _).injective
        cat_disch
    }
    inv := {
      app := fun x => by
        simp only [Functor.comp_obj, Functor.id_obj]
        apply preimg; exact inv (invF_obj_iso (F.obj x))
      naturality := by
        simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, id_eq, Functor.id_map]
        intro x y f; apply (F_map_bij _ _).injective
        cat_disch
    }
    hom_inv_id := by
      ext; simp only [Functor.id_obj, Functor.comp_obj, id_eq, NatTrans.comp_app, NatTrans.id_app]
      apply (F_map_bij _ _).injective
      cat_disch
    inv_hom_id := by
      ext; simp only [Functor.id_obj, Functor.comp_obj, id_eq, NatTrans.comp_app, NatTrans.id_app]
      apply (F_map_bij _ _).injective
      cat_disch
  }
-- Define the counit natural isomorphism `counitIso : invF ⋙ F ≅ 𝟭 D` that is needed to get an equivalence
  let counitIso : invF ⋙ F ≅ 𝟭 D := {
    hom := {
      app := fun x => by
        simp only [Functor.comp_obj, Functor.id_obj]
        exact inv (invF_obj_iso x)
    }
    inv := {
      app := fun _ => by
        simp only [Functor.comp_obj, Functor.id_obj]
        exact invF_obj_iso _
    }
  }
-- Use `CategoryTheory.Equivalence.mk` to construct the desired equivalence
  let e := CategoryTheory.Equivalence.mk F invF unitIso counitIso
  use e; rfl
