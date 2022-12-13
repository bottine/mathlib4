/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
import Mathlib.Algebra.Hom.Group
import Mathlib.Tactic.Basic

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `Monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `Algebra.Group.Defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `MonoidHom.map_div`, `MonoidHom.map_pow` etc.

## Tags
monoid, group, extensionality
-/

universe u

@[ext, to_additive]
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ := by
  have : m₁.toMulOneClass = m₂.toMulOneClass := MulOneClass.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) (this)
  let f : @MonoidHom M M m₁.toMulOneClass m₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := by
    ext (n x)
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  rcases m₁ with @⟨@⟨⟨_⟩⟩, ⟨_⟩⟩
  rcases m₂ with @⟨@⟨⟨_⟩⟩, ⟨_⟩⟩
  congr
#align monoid.ext Monoid.ext

@[to_additive]
theorem CommMonoid.toMonoid_injective {M : Type u} : Function.Injective (@CommMonoid.toMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr
#align comm_monoid.to_monoid_injective CommMonoid.toMonoid_injective

@[ext, to_additive]
theorem CommMonoid.ext {M : Type _} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul
#align comm_monoid.ext CommMonoid.ext

@[to_additive]
theorem LeftCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h
#align left_cancel_monoid.to_monoid_injective LeftCancelMonoid.toMonoid_injective

@[ext, to_additive]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  LeftCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align left_cancel_monoid.ext LeftCancelMonoid.ext

@[to_additive]
theorem RightCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@RightCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h
#align right_cancel_monoid.to_monoid_injective RightCancelMonoid.toMonoid_injective

@[ext, to_additive]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  RightCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align right_cancel_monoid.ext RightCancelMonoid.ext

@[to_additive]
theorem CancelMonoid.toLeftCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr
#align cancel_monoid.to_left_cancel_monoid_injective CancelMonoid.toLeftCancelMonoid_injective

@[ext, to_additive]
theorem CancelMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelMonoid.toLeftCancelMonoid_injective <| LeftCancelMonoid.ext h_mul
#align cancel_monoid.ext CancelMonoid.ext

@[to_additive]
theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  congr <;> {
    injection h with h'
    injection h' }
#align cancel_comm_monoid.to_comm_monoid_injective CancelCommMonoid.toCommMonoid_injective

@[ext, to_additive]
theorem CancelCommMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul
#align cancel_comm_monoid.ext CancelCommMonoid.ext

@[ext, to_additive]
theorem DivInvMonoid.ext {M : Type _} ⦃m₁ m₂ : DivInvMonoid M⦄ (h_mul : m₁.mul = m₂.mul)
  (h_inv : m₁.inv = m₂.inv) : m₁ = m₂ := by
  have h_mon := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  let f : @MonoidHom M M m₁.toMulOneClass m₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := congr_arg (·.npow) h_mon
  have : m₁.zpow = m₂.zpow := by
    ext (m x)
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have : m₁.div = m₂.div := by
    ext (a b)
    exact @map_div' _ _
      (@MonoidHom _ _ (_) _) (_) _
      (@MonoidHom.monoidHomClass _ _ (_) _) f (congr_fun h_inv) a b
  rcases m₁ with @⟨_, ⟨_⟩, ⟨_⟩⟩
  rcases m₂ with @⟨_, ⟨_⟩, ⟨_⟩⟩
  congr
#align div_inv_monoid.ext DivInvMonoid.ext

@[ext, to_additive]
theorem Group.ext {G : Type _} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ := by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
  let f : @MonoidHom G G g₁.toMulOneClass g₂.toMulOneClass :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ g₂.toDivisionMonoid f))
#align group.ext Group.ext

@[ext, to_additive]
theorem CommGroup.ext {G : Type _} ⦃g₁ g₂ : CommGroup G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul
#align comm_group.ext CommGroup.ext