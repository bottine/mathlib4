/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Image

/-!
### Recursion on the natural numbers and `Set.range`
-/


namespace Nat

section Set

open Set

theorem zero_union_range_succ : {0} ∪ range succ = univ := by
  ext n
  cases n <;> simp
#align nat.zero_union_range_succ Nat.zero_union_range_succ

@[simp]
protected theorem range_succ : range succ = { i | 0 < i } := by
  ext (_ | i) <;> simp [succ_pos, succ_ne_zero, Set.mem_setOf]
#align nat.range_succ Nat.range_succ

variable {α : Type _}

theorem range_of_succ (f : ℕ → α) : {f 0} ∪ range (f ∘ succ) = range f := by
  rw [← image_singleton, range_comp, ← image_union, zero_union_range_succ, image_univ]
#align nat.range_of_succ Nat.range_of_succ

theorem range_rec {α : Type _} (x : α) (f : ℕ → α → α) :
    (Set.range fun n => Nat.rec x f n : Set α) =
      {x} ∪ Set.range fun n => Nat.rec (f 0 x) (f ∘ succ) n := by
  convert (range_of_succ (fun n => Nat.rec x f n : ℕ → α)).symm
  dsimp
  apply congr_arg Set.range
  ext n
  induction' n with n ihn
  · rfl
  · dsimp at ihn⊢
    rw [ihn]
#align nat.range_rec Nat.range_rec

theorem range_casesOn {α : Type _} (x : α) (f : ℕ → α) :
    (Set.range fun n => Nat.casesOn n x f : Set α) = {x} ∪ Set.range f :=
  (range_of_succ _).symm
#align nat.range_cases_on Nat.range_casesOn

end Set

end Nat
