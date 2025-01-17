/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Basic

/-!
# Lemma about the coercion `ℕ → WithBot ℕ`.

An orphaned lemma about casting from `ℕ` to `WithBot ℕ`,
exiled here to minimize imports to `data.rat.order` for porting purposes.
-/


theorem Nat.cast_withTop (n : ℕ) :  Nat.cast n = WithTop.some n :=
  rfl
#align nat.cast_with_top Nat.cast_withTop

theorem Nat.cast_withBot (n : ℕ) : Nat.cast n = WithBot.some n :=
  rfl
#align nat.cast_with_bot Nat.cast_withBot
