/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open CategoryTheory Classical

/-! Let $\mathcal{G}$ be a connected groupoid and let $G$ be the group of automorphisms at any of its objects.
The inclusion $G \hookrightarrow \mathcal{G}$ defines an equivalence of categories.
Construct an inverse equivalence $\mathcal{G} \to G$.-/

universe u v

variable {𝓖 : Type u} [Category.{v, u} 𝓖] (x : 𝓖)

/-- Define the automorphism groups of `x` as a category with one object -/
def AutCat : Category (SingleObj 𝓖) := {
  Hom := fun _ _ => Aut x
  id := fun _ => Iso.refl x
  comp := fun f g => f ≪≫ g
}

/-- Define the inclusion functor from `AutCat x` to `𝓖` -/
def AutCat_inclusionFunctor := @CategoryTheory.Functor.mk (SingleObj 𝓖)
    (AutCat x) 𝓖 _ (fun _ => x) (by simp only [AutCat]; intro _ _ f; exact f.hom)
    (by cat_disch) (by cat_disch)

variable [IsPreconnected 𝓖] [IsGroupoid 𝓖]

/-- If `𝓖` is a preconnected groupoid, prove that for all `y` in `𝓖` there exists an isomorphism from `x` to `y` -/
private lemma exists_iso (y : 𝓖) : ∃ f : x ⟶ y, IsIso f := by
  suffices : ∀ y, y ∈ {y | ∃ f : x ⟶ y, IsIso f}
  · exact this y
  have : x ∈ {y | ∃ f : x ⟶ y, IsIso f} := by
    rw [Set.mem_setOf_eq]; use 𝟙 x
    exact IsIso.id x
  apply induct_on_objects _ this
  intro z w g; simp only [Set.mem_setOf_eq]; constructor
  · rintro ⟨f, hf⟩; use f ≫ g; apply IsIso.comp_isIso
  rintro ⟨f, hf⟩; use f ≫ inv g; apply IsIso.comp_isIso

/-- Choose an isomorphism `τ x y : x ⟶ y` for every `y` in `𝓖` and $τ x x = 𝟙 x$-/
private noncomputable def τ : (y : 𝓖) → (x ⟶ y) := fun y =>
    if h : x = y then eqToHom h else choose (exists_iso x y)

private lemma τ_xx : τ x x = 𝟙 x := by simp [τ]

/-- Define the inverse equivalence of the inclusion functor-/
noncomputable def AutCat_inverseFunctor := @CategoryTheory.Functor.mk 𝓖 _ (SingleObj 𝓖)
    (AutCat x) (fun _ => ()) (by simp only [AutCat]; intro y z f; exact {
      hom := τ x y ≫ f ≫ inv (τ x z)
      inv := τ x z ≫ inv f ≫ inv (τ x y)
    }) (by cat_disch) (by simp [AutCat])

/-- Prove that `AutCat_inclusionFunctor x ≫ AutCat_inverseFunctor x` is equal to the identity functor on `AutCat x`-/
lemma aux_eq : @Functor.id (SingleObj 𝓖) (AutCat x) =
    @Functor.comp (SingleObj 𝓖) (AutCat x) 𝓖 _ (SingleObj 𝓖) (AutCat x)
    (AutCat_inclusionFunctor x) (AutCat_inverseFunctor x) := by
  apply @Functor.hext (SingleObj 𝓖) (AutCat x) (SingleObj 𝓖) (AutCat x)
  · simp only [Functor.id_obj, AutCat_inclusionFunctor, id_eq, AutCat_inverseFunctor,
      Functor.comp_obj]
    intro; rfl
  simp only [Functor.id_obj, Functor.id_map, AutCat_inclusionFunctor, id_eq, AutCat_inverseFunctor,
    Functor.comp_obj, Functor.comp_map, τ_xx, IsIso.inv_id, Category.comp_id, Category.id_comp,
    IsIso.Iso.inv_hom, heq_eq_eq]
  cat_disch

/-- Define a natural isomorphism from `AutCat_inverseFunctor x ≫ AutCat_inclusionFunctor x` to the identity functor on `𝓖`-/
noncomputable def aux_iso : @Functor.comp 𝓖 _ (SingleObj 𝓖) (AutCat x) 𝓖 _
    (AutCat_inverseFunctor x) (AutCat_inclusionFunctor x) ≅ 𝟭 𝓖 := {
      hom := {
        app := by
          simp only [AutCat_inverseFunctor, id_eq, AutCat_inclusionFunctor, Functor.comp_obj,
            Functor.id_obj]
          intro y; exact τ x y
        naturality := by simp [AutCat_inverseFunctor, AutCat_inclusionFunctor]
      }
      inv := {
        app := by
          simp only [AutCat_inverseFunctor, id_eq, AutCat_inclusionFunctor, Functor.comp_obj,
            Functor.id_obj]
          intro y; exact inv (τ x y)
      }
    }

/-- Put together what we get so far to define the desired equivalence-/
noncomputable def desired_equiv := @CategoryTheory.Equivalence.mk (SingleObj 𝓖) (AutCat x)
    𝓖 _ (AutCat_inclusionFunctor x) (AutCat_inverseFunctor x) (eqToIso (aux_eq x)) (aux_iso x)
