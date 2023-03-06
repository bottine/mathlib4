/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.PathCategory
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Groupoid.Init


/-!
# Universal Groupoid

This file defines the universal groupoid given by a pair consisting of a groupoid and a map whose
domain is the object type of the groupoid.

-/

namespace CategoryTheory
namespace Groupoid
namespace Universal

variable {V V' : Type _} [Groupoid V] (σ : V → V')

scoped postfix:50 " * " => fun σ => Quiver.Push.of σ ⋙q Paths.of

@[simp]
def _root_.Quiver.Path.asHom {X Y : Quiver.Push σ} (f : Quiver.Path X Y) :
    Paths.of.obj X ⟶ Paths.of.obj Y := f

@[simp]
def _root_.Quiver.Hom.push {X Y : V} (f : X ⟶ Y) : (σ *).obj X ⟶ (σ *).obj Y := (σ *).map f

@[simp]
lemma PathsPush_id_eq (X : Paths $ Quiver.Push σ) : 𝟙 X = Quiver.Path.nil := rfl

@[simp]
lemma PathsPush_comp_eq {X Y Z : Paths $ Quiver.Push σ} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = Quiver.Path.comp f g := rfl

@[simp]
def _root_.Quiver.Hom.rev {σ : V → V'} {X Y : Paths $ Quiver.Push σ} (f : X ⟶ Y) : Y ⟶ X :=
  f.reverse.asHom

scoped infixl:100 " † " => Quiver.Hom.push

/-- Two reduction steps possible: compose composable arrows, or drop identity arrows -/
inductive red.atomic_step : HomRel (Paths (Quiver.Push σ))
  /-- Pushing a composite is the same as composing the pushes -/
  | comp (X Y Z : V) (f : X ⟶ Y) (g : Y ⟶ Z) :
      red.atomic_step (σ † f ≫ σ † g) (σ † (f ≫ g))
  /-- Pushing the id is the id path -/
  | id (X : V) :
      red.atomic_step (σ † 𝟙 X) (𝟙 $ (σ *).obj X) -- ugly

@[simp]
def red.step {X Y : Paths $ Quiver.Push σ} (p q : X ⟶ Y) :=
  Quotient.CompClosure (red.atomic_step σ) p q

abbrev red.step' (σ : V → V') {X Y : Paths $ Quiver.Push σ} (p q : X ⟶ Y) :=
  @red.step _ _ _ σ X Y p q

lemma red.atomic_step.reverse : {X Y : Paths $ Quiver.Push σ} → (f g : X ⟶ Y) →
  red.atomic_step σ f g → red.atomic_step σ f.rev g.rev
  | _, _, _, _, .comp X Y Z f g => by
    simp [Quiver.Push.of_obj, Quiver.Path.reverse, ←Prefunctor.map_reverse, reverse_eq_inv,
               inv_eq_inv, Quiver.Path.comp_nil, IsIso.inv_comp, Quiver.Hom.rev]
    apply red.atomic_step.comp
  | _, _, _, _, .id X => by
    simp only [Quiver.Push.of_obj, Quiver.Path.reverse, ←Prefunctor.map_reverse, reverse_eq_inv,
               inv_eq_inv, IsIso.inv_id, Quiver.Path.comp_nil, Quiver.Hom.rev]
    apply red.atomic_step.id X

/-- The underlying vertices of the Universal Groupoid -/
def _root_.CategoryTheory.Groupoid.UniversalGroupoid := Quotient (red.atomic_step σ)

instance : Category (UniversalGroupoid σ) := Quotient.category (red.atomic_step σ)

lemma red.step.reverse : {X Y : Paths $ Quiver.Push σ} → (p q : X ⟶ Y) →
    red.step σ p q → red.step σ (p.reverse) (q.reverse)
  | A, B, _, _, .intro f _ _ g hr => by
    convert Quotient.CompClosure.intro (g.rev) _ _ (f.rev) hr.reverse
    · simp
    · simp

lemma Quot_mk_self_comp_reverse {X} : ∀ {Y : Paths $ Quiver.Push σ} (p : X ⟶ Y),
    Quot.mk (red.step' σ) (p ≫ p.rev) = Quot.mk (red.step' σ) (𝟙 X)
  | _, .nil => by simp
  | _, .cons p ⟨e⟩ => by
    let pp := p.asHom
    let pr := pp.rev
    calc Quot.mk (red.step' σ) ((p.cons _).asHom ≫ Quiver.Hom.rev (p.cons ⟨e⟩).asHom)
       = Quot.mk _ (p.asHom ≫ (σ † e) ≫ (σ † e).rev ≫ pr) := by
          congr 1
          simp only [Paths.of_obj, Quiver.Path.asHom, Quiver.Hom.rev, Quiver.Path.reverse,
                     Quiver.Hom.toPath,PathsPush_comp_eq, Prefunctor.comp_obj, Quiver.Push.of_obj,
                     Quiver.Hom.push, Prefunctor.comp_map, Paths.of_map, Quiver.Path.comp_nil,
                     Quiver.Path.cons_comp, Quiver.Path.nil_comp, Quiver.Path.comp_assoc]
          rfl
     _ = Quot.mk _ (pp ≫ ((σ † e) ≫ (σ † e).rev) ≫ pr) := by
          simp
     _ = Quot.mk _ (pp ≫ (σ † (𝟙 _)) ≫ pr) := by
          apply Quot.sound (Quotient.CompClosure.intro _ _ _ _ _)
          convert @red.atomic_step.comp _ _ _ σ _ _ _ e (inv e)
          simp only [inv_eq_inv, IsIso.hom_inv_id]
     _ = Quot.mk _ (pp ≫ 𝟙 _ ≫ pr) :=
          Quot.sound (Quotient.CompClosure.intro _ _ _ _ $ @red.atomic_step.id _ _ _ σ _)
     _ = Quot.mk _ (pp ≫ pr) := by
           simp only [Paths.of_obj, Quiver.Path.asHom, PathsPush_id_eq, Quiver.Hom.rev,
                      PathsPush_comp_eq, Quiver.Path.nil_comp]
     _ = Quot.mk _ (𝟙 _) := Quot_mk_self_comp_reverse p

lemma Quot_mk_reverse_comp_self {X Y : Paths $ Quiver.Push σ} (p : X ⟶ Y) :
    Quot.mk (red.step' σ) (p.rev ≫ p) = Quot.mk (red.step' σ) (𝟙 Y) := by
  simpa using Quot_mk_self_comp_reverse σ p.rev


/-- The inverse of an arrow in the Universal Groupoid -/
def Quot_inv {X Y : UniversalGroupoid σ} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f
            (fun pp ↦ Quot.mk _ $ pp.rev)
            (fun _ _ con ↦ Quot.sound $ red.step.reverse σ _ _ con)

instance : Groupoid (UniversalGroupoid σ) where
  inv      f := Quot_inv σ f
  inv_comp f := Quot.inductionOn f $ fun pp ↦ Quot_mk_reverse_comp_self σ pp
  comp_inv f := Quot.inductionOn f $ fun pp ↦ Quot_mk_self_comp_reverse σ pp

/-- The extension of `σ` to a functor -/
def extend : V ⥤ (UniversalGroupoid σ) where
  obj X := ⟨σ X⟩
  map f := Quot.mk _ (σ † f)
  map_id X := Quot.sound $ Quotient.CompClosure.of _ _ _ (red.atomic_step.id X)
  map_comp f g := Eq.symm $ Quot.sound $
    Quotient.CompClosure.of _ _ _ (red.atomic_step.comp _ _ _ f g)

lemma extend_eq : (extend σ).toPrefunctor =
  Quiver.Push.of σ ⋙q Paths.of ⋙q (Quotient.functor $ red.atomic_step σ).toPrefunctor := rfl

abbrev as : UniversalGroupoid σ → V' := Quotient.as

section ump

variable {V'' : Type _} [Groupoid V''] (θ : V ⥤ V'') (τ₀ : V' → V'') (hτ₀ : ∀ x, θ.obj x = τ₀ (σ x))

/--
Any functor `θ` from `V` to a Groupoid `V''` with `θ.obj` factoring through `σ`
defines a functor from `V'`.
 -/
noncomputable def lift : UniversalGroupoid σ ⥤ V'' :=
Quotient.lift _
  ( Paths.lift $ Quiver.Push.lift σ θ.toPrefunctor τ₀ hτ₀ )
  ( fun _ _ _ _ h => by
      induction h <;>
      aesop_cat (add norm unfold [Quiver.Push.of, Quiver.Hom.toPath, Quiver.Push.lift, Paths.lift]))

lemma lift_spec_obj : (lift σ θ τ₀ hτ₀).obj = τ₀ ∘ as σ := rfl

lemma lift_spec_comp : extend σ ⋙ lift σ θ τ₀ hτ₀ = θ := by
  rw [Functor.toPrefunctor_ext,←Functor.toPrefunctor_comp, extend_eq, lift,
      Prefunctor.comp_assoc, Functor.toPrefunctor_comp, Quotient.lift_spec,
      Prefunctor.comp_assoc, Paths.lift_spec, Quiver.Push.lift_comp]

lemma lift_unique (Φ : UniversalGroupoid σ ⥤ V'')
    (Φ₀ : Φ.obj = τ₀ ∘ as σ) (Φc : extend σ ⋙ Φ = θ) : Φ = lift σ θ τ₀ hτ₀ := by
  apply Quotient.lift_unique
  apply Paths.lift_unique
  apply Quiver.Push.lift_unique
  · ext
    simp [Φ₀]
  · simpa only [Functor.toPrefunctor_ext, ←Functor.toPrefunctor_comp] using Φc

end ump

end Universal
end Groupoid
end CategoryTheory
