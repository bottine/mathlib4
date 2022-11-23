/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury G. Kudryashov
-/
import Mathlib.Order.Basic
import Mathlib.Logic.IsEmpty
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Unbundled relation classes

In this file we prove some properties of `Is*` classes defined in `Init.Algebra.Classes`. The main
difference between these classes and the usual order classes (`Preorder` etc) is that usual classes
extend `LE` and/or `LT` while these classes take a relation as an explicit argument.

-/


universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open Function

theorem of_eq [IsRefl α r] : ∀ {a b}, a = b → r a b
  | _, _, .refl _ => refl _

theorem comm [IsSymm α r] {a b : α} : r a b ↔ r b a :=
  ⟨symm, symm⟩

theorem antisymm' [IsAntisymm α r] {a b : α} : r a b → r b a → b = a := fun h h' => antisymm h' h

theorem antisymm_iff [IsRefl α r] [IsAntisymm α r] {a b : α} : r a b ∧ r b a ↔ a = b :=
  ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩

/-- A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there.  -/
@[elab_without_expected_type]
theorem antisymm_of (r : α → α → Prop) [IsAntisymm α r] {a b : α} : r a b → r b a → a = b :=
  antisymm

/-- A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there.  -/
@[elab_without_expected_type]
theorem antisymm_of' (r : α → α → Prop) [IsAntisymm α r] {a b : α} : r a b → r b a → b = a :=
  antisymm'

/-- A version of `comm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there.  -/
theorem comm_of (r : α → α → Prop) [IsSymm α r] {a b : α} : r a b ↔ r b a :=
  comm

theorem IsRefl.swap (r) [IsRefl α r] : IsRefl α (swap r) :=
  ⟨refl_of r⟩

theorem IsIrrefl.swap (r) [IsIrrefl α r] : IsIrrefl α (swap r) :=
  ⟨irrefl_of r⟩

theorem IsTrans.swap (r) [IsTrans α r] : IsTrans α (swap r) :=
  ⟨fun _ _ _ h₁ h₂ => trans_of r h₂ h₁⟩

theorem IsAntisymm.swap (r) [IsAntisymm α r] : IsAntisymm α (swap r) :=
  ⟨fun _ _ h₁ h₂ => _root_.antisymm h₂ h₁⟩

theorem IsAsymm.swap (r) [IsAsymm α r] : IsAsymm α (swap r) :=
  ⟨fun _ _ h₁ h₂ => asymm_of r h₂ h₁⟩

theorem IsTotal.swap (r) [IsTotal α r] : IsTotal α (swap r) :=
  ⟨fun a b => (total_of r a b).symm⟩

theorem IsTrichotomous.swap (r) [IsTrichotomous α r] : IsTrichotomous α (swap r) :=
  ⟨fun a b => by simpa [Function.swap, or_comm, or_left_comm] using trichotomous_of r a b⟩

theorem IsPreorder.swap (r) [IsPreorder α r] : IsPreorder α (swap r) :=
  { @IsRefl.swap α r _, @IsTrans.swap α r _ with }

theorem IsStrictOrder.swap (r) [IsStrictOrder α r] : IsStrictOrder α (swap r) :=
  { @IsIrrefl.swap α r _, @IsTrans.swap α r _ with }

theorem IsPartialOrder.swap (r) [IsPartialOrder α r] : IsPartialOrder α (swap r) :=
  { @IsPreorder.swap α r _, @IsAntisymm.swap α r _ with }

theorem IsTotalPreorder.swap (r) [IsTotalPreorder α r] : IsTotalPreorder α (swap r) :=
  { @IsPreorder.swap α r _, @IsTotal.swap α r _ with }

theorem IsLinearOrder.swap (r) [IsLinearOrder α r] : IsLinearOrder α (swap r) :=
  { @IsPartialOrder.swap α r _, @IsTotal.swap α r _ with }

protected theorem IsAsymm.is_antisymm (r) [IsAsymm α r] : IsAntisymm α r :=
  ⟨fun _ _ h₁ h₂ => (_root_.asymm h₁ h₂).elim⟩

protected theorem IsAsymm.is_irrefl [IsAsymm α r] : IsIrrefl α r :=
  ⟨fun _ h => _root_.asymm h h⟩

protected theorem IsTotal.is_trichotomous (r) [IsTotal α r] : IsTrichotomous α r :=
  ⟨fun a b => or_left_comm.1 (Or.inr <| total_of r a b)⟩

-- see Note [lower instance priority]
instance (priority := 100) IsTotal.to_is_refl (r) [IsTotal α r] : IsRefl α r :=
  ⟨fun a => or_self_iff.1 <| total_of r a a⟩

theorem ne_of_irrefl {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → x ≠ y
  | _, _, h, rfl => irrefl _ h

theorem ne_of_irrefl' {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → y ≠ x
  | _, _, h, rfl => irrefl _ h

theorem not_rel_of_subsingleton (r) [IsIrrefl α r] [Subsingleton α] (x y) : ¬r x y :=
  Subsingleton.elim x y ▸ irrefl x

theorem rel_of_subsingleton (r) [IsRefl α r] [Subsingleton α] (x y) : r x y :=
  Subsingleton.elim x y ▸ refl x

@[simp]
theorem empty_relation_apply (a b : α) : EmptyRelation a b ↔ False :=
  Iff.rfl

theorem eq_empty_relation (r) [IsIrrefl α r] [Subsingleton α] : r = EmptyRelation :=
  funext₂ <| by simpa using not_rel_of_subsingleton r

instance : IsIrrefl α EmptyRelation :=
  ⟨fun _ => id⟩

theorem trans_trichotomous_left [IsTrans α r] [IsTrichotomous α r] {a b c : α} :
    ¬r b a → r b c → r a c := by
  intro h₁ h₂
  rcases trichotomous_of r a b with (h₃ | h₃ | h₃)
  exact trans h₃ h₂
  rw [h₃]
  exact h₂
  exfalso
  exact h₁ h₃

theorem trans_trichotomous_right [IsTrans α r] [IsTrichotomous α r] {a b c : α} :
    r a b → ¬r c b → r a c := by
  intro h₁ h₂
  rcases trichotomous_of r b c with (h₃ | h₃ | h₃)
  exact trans h₁ h₃
  rw [← h₃]
  exact h₁
  exfalso
  exact h₂ h₃

theorem transitive_of_trans (r : α → α → Prop) [IsTrans α r] : Transitive r := fun _ _ _ => trans

/-- In a trichotomous irreflexive order, every element is determined by the set of predecessors. -/
theorem extensional_of_trichotomous_of_irrefl (r : α → α → Prop) [IsTrichotomous α r] [IsIrrefl α r]
    {a b : α} (H : ∀ x, r x a ↔ r x b) : a = b :=
  ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl a).resolve_right <| mt (H _).1
    <| irrefl b

/-- Construct a partial order from a `isStrictOrder` relation.

See note [reducible non-instances]. -/
@[reducible]
def partialOrderOfSO (r) [IsStrictOrder α r] : PartialOrder α where
  le x y := x = y ∨ r x y
  lt := r
  le_refl x := Or.inl rfl
  le_trans x y z h₁ h₂ :=
    match y, z, h₁, h₂ with
    | _, _, Or.inl rfl, h₂ => h₂
    | _, _, h₁, Or.inl rfl => h₁
    | _, _, Or.inr h₁, Or.inr h₂ => Or.inr (trans h₁ h₂)
  le_antisymm x y h₁ h₂ :=
    match y, h₁, h₂ with
    | _, Or.inl rfl, _ => rfl
    | _, _, Or.inl rfl => rfl
    | _, Or.inr h₁, Or.inr h₂ => (asymm h₁ h₂).elim
  lt_iff_le_not_le x y :=
    ⟨fun h => ⟨Or.inr h, not_or_of_not (fun e => by rw [e] at h; exact irrefl _ h) (asymm h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂ <| e ▸ Or.inl rfl⟩

/-- Construct a linear order from an `IsStrictTotalOrder` relation.

See note [reducible non-instances]. -/
@[reducible]
def linearOrderOfSTO (r) [IsStrictTotalOrder α r] [∀ x y, Decidable ¬r x y] : LinearOrder α :=
  let hD : DecidableRel (fun x y => x = y ∨ r x y) := fun x y =>
      decidable_of_iff (¬r y x)
        ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id, fun h =>
          h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩
  { partialOrderOfSO r with
    le_total := fun x y =>
      match y, trichotomous_of r x y with
      | y, Or.inl h => Or.inl (Or.inr h)
      | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
      | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    toMin := minOfLe,
    toMax := maxOfLe,
    decidable_le := hD }

theorem IsStrictTotalOrder.swap (r) [IsStrictTotalOrder α r] : IsStrictTotalOrder α (swap r) :=
  { IsTrichotomous.swap r, IsStrictOrder.swap r with }

/-! ### Order connection -/


/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`.  -/
class IsOrderConnected (α : Type u) (lt : α → α → Prop) : Prop where
  /-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`. -/
  conn : ∀ a b c, lt a c → lt a b ∨ lt b c

theorem IsOrderConnected.neg_trans {r : α → α → Prop} [IsOrderConnected α r] {a b c}
    (h₁ : ¬r a b) (h₂ : ¬r b c) : ¬r a c :=
  mt (IsOrderConnected.conn a b c) <| by simp [h₁, h₂]

theorem isStrictWeakOrder_of_isOrderConnected [IsAsymm α r] [IsOrderConnected α r] :
    IsStrictWeakOrder α r :=
  { @IsAsymm.is_irrefl α r _ with
    trans := fun _ _ c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }
#align is_strict_weak_order_of_is_order_connected isStrictWeakOrder_of_isOrderConnected

-- see Note [lower instance priority]
instance (priority := 100) isStrictOrderConnected_of_isStrictTotalOrder [IsStrictTotalOrder α r] :
    IsOrderConnected α r :=
  ⟨λ _ _ _ h => (trichotomous _ _).imp_right fun o => o.elim (fun e => e ▸ h) fun h' => trans h' h⟩
#align is_order_connected_of_is_strict_total_order isStrictOrderConnected_of_isStrictTotalOrder

-- see Note [lower instance priority]
instance (priority := 100) isStrictTotalOrder_of_isStrictTotalOrder [IsStrictTotalOrder α r] :
    IsStrictWeakOrder α r :=
  { isStrictWeakOrder_of_isOrderConnected with }
#align is_strict_weak_order_of_is_strict_total_order isStrictTotalOrder_of_isStrictTotalOrder

/-! ### Well-order -/


-- Porting note: no `mk_iff` yet, so hard-coded iff
/-- A well-founded relation. Not to be confused with `isWellOrder`. -/
@[mk_iff] class IsWellFounded (α : Type u) (r : α → α → Prop) : Prop where
  /-- The relation is `WellFounded`, as a proposition. -/
  wf : WellFounded r

#align has_well_founded WellFoundedRelation
#align has_well_founded.R WellFoundedRelation.rel
instance [h : WellFoundedRelation α] : IsWellFounded α WellFoundedRelation.rel :=
  { h with }

theorem WellFoundedRelation.asymmetric {α : Sort _} [WellFoundedRelation α] {a b : α} :
    WellFoundedRelation.rel a b → ¬ WellFoundedRelation.rel b a :=
  fun hab hba => WellFoundedRelation.asymmetric hba hab
termination_by _ => a

namespace IsWellFounded

variable (r) [IsWellFounded α r]

/-- Induction on a well-founded relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, r y x → C y) → C x) → C a :=
  wf.induction

/-- All values are accessible under the well-founded relation. -/
theorem apply : ∀ a, Acc r a :=
  wf.apply

-- Porting note: WellFounded.fix is noncomputable, at 2022-10-29 lean
/-- Creates data, given a way to generate a value from all that compare as less under a well-founded
relation. See also `IsWellFounded.fix_eq`. -/
noncomputable
def fix {C : α → Sort _} : (∀ x : α, (∀ y : α, r y x → C y) → C x) → ∀ x : α, C x :=
  wf.fix

/-- The value from `IsWellFounded.fix` is built from the previous ones as specified. -/
theorem fix_eq {C : α → Sort _} (F : ∀ x : α, (∀ y : α, r y x → C y) → C x) :
    ∀ x, fix r F x = F x fun y _ => fix r F y :=
  wf.fix_eq F

/-- Derive a `WellFoundedRelation` instance from an `isWellFounded` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  ⟨r, IsWellFounded.wf⟩

end IsWellFounded

theorem WellFounded.asymmetric {α : Sort _} {r : α → α → Prop} (h : WellFounded r) (a b) :
    r a b → ¬r b a :=
  @WellFoundedRelation.asymmetric _ ⟨_, h⟩ _ _

-- see Note [lower instance priority]
instance (priority := 100) (r : α → α → Prop) [IsWellFounded α r] : IsAsymm α r :=
  ⟨IsWellFounded.wf.asymmetric⟩

-- see Note [lower instance priority]
instance (priority := 100) (r : α → α → Prop) [IsWellFounded α r] : IsIrrefl α r :=
  IsAsymm.is_irrefl

/-- A class for a well founded relation `<`. -/
@[reducible]
def WellFoundedLt (α : Type _) [LT α] : Prop :=
  IsWellFounded α (· < ·)

/-- A class for a well founded relation `>`. -/
@[reducible]
def WellFoundedGt (α : Type _) [LT α] : Prop :=
  IsWellFounded α (· > ·)

-- See note [lower instance priority]
instance (priority := 100) (α : Type _) [LT α] [h : WellFoundedLt α] : WellFoundedGt αᵒᵈ :=
  h

-- See note [lower instance priority]
instance (priority := 100) (α : Type _) [LT α] [h : WellFoundedGt α] : WellFoundedLt αᵒᵈ :=
  h

theorem wellFoundedGt_dual_iff (α : Type _) [LT α] : WellFoundedGt αᵒᵈ ↔ WellFoundedLt α :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

theorem wellFoundedLt_dual_iff (α : Type _) [LT α] : WellFoundedLt αᵒᵈ ↔ WellFoundedGt α :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

/-- A well order is a well-founded linear order. -/
class IsWellOrder (α : Type u) (r : α → α → Prop) extends
  IsTrichotomous α r, IsTrans α r, IsWellFounded α r : Prop

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] :
    IsStrictTotalOrder α r where

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] : IsTrichotomous α r :=
  by infer_instance

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] : IsTrans α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] : IsIrrefl α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] : IsAsymm α r := by
  infer_instance

namespace WellFoundedLt

variable [LT α] [WellFoundedLt α]

/-- Inducts on a well-founded `<` relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, y < x → C y) → C x) → C a :=
  IsWellFounded.induction _

/-- All values are accessible under the well-founded `<`. -/
theorem apply : ∀ a : α, Acc (· < ·) a :=
  IsWellFounded.apply _

-- Porting note: WellFounded.fix is noncomputable, at 2022-10-29 lean
/-- Creates data, given a way to generate a value from all that compare as lesser. See also
`WellFoundedLt.fix_eq`. -/
noncomputable
def fix {C : α → Sort _} : (∀ x : α, (∀ y : α, y < x → C y) → C x) → ∀ x : α, C x :=
  IsWellFounded.fix (· < ·)

/-- The value from `WellFoundedLt.fix` is built from the previous ones as specified. -/
theorem fix_eq {C : α → Sort _} (F : ∀ x : α, (∀ y : α, y < x → C y) → C x) :
    ∀ x, fix F x = F x fun y _ => fix F y :=
  IsWellFounded.fix_eq _ F

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedLt` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· < ·)

end WellFoundedLt

namespace WellFoundedGt

variable [LT α] [WellFoundedGt α]

/-- Inducts on a well-founded `>` relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, x < y → C y) → C x) → C a :=
  IsWellFounded.induction _

/-- All values are accessible under the well-founded `>`. -/
theorem apply : ∀ a : α, Acc (· > ·) a :=
  IsWellFounded.apply _

-- Porting note: WellFounded.fix is noncomputable, at 2022-10-29 lean
/-- Creates data, given a way to generate a value from all that compare as greater. See also
`WellFoundedGt.fix_eq`. -/
noncomputable
def fix {C : α → Sort _} : (∀ x : α, (∀ y : α, x < y → C y) → C x) → ∀ x : α, C x :=
  IsWellFounded.fix (· > ·)

/-- The value from `WellFoundedGt.fix` is built from the successive ones as specified. -/
theorem fix_eq {C : α → Sort _} (F : ∀ x : α, (∀ y : α, x < y → C y) → C x) :
    ∀ x, fix F x = F x fun y _ => fix F y :=
  IsWellFounded.fix_eq _ F

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedGt` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· > ·)

end WellFoundedGt

/-- Construct a decidable linear order from a well-founded linear order. -/
noncomputable def IsWellOrder.LinearOrder (r : α → α → Prop) [IsWellOrder α r] : LinearOrder α :=
  letI := fun x y => Classical.dec ¬r x y
  linearOrderOfSTO r

/-- Derive a `WellFoundedRelation` instance from a `IsWellOrder` instance. -/
def IsWellOrder.toHasWellFounded [LT α] [hwo : IsWellOrder α (· < ·)] : WellFoundedRelation α where
  rel := (· < ·)
  wf := hwo.wf

-- This isn't made into an instance as it loops with `is_irrefl α r`.
theorem Subsingleton.isWellOrder [Subsingleton α] (r : α → α → Prop) [hr : IsIrrefl α r] :
    IsWellOrder α r :=
  { hr with
    trichotomous := fun a b => Or.inr <| Or.inl <| Subsingleton.elim a b,
    trans := fun a b _ h => (not_rel_of_subsingleton r a b h).elim,
    wf := ⟨fun a => ⟨_, fun y h => (not_rel_of_subsingleton r y a h).elim⟩⟩ }

instance [Subsingleton α] : IsWellOrder α EmptyRelation :=
  Subsingleton.isWellOrder _

instance (priority := 100) [IsEmpty α] (r : α → α → Prop) : IsWellOrder α r where
  trichotomous := isEmptyElim
  trans := isEmptyElim
  wf := wellFounded_of_isEmpty r

instance [IsWellFounded α r] [IsWellFounded β s] : IsWellFounded (α × β) (Prod.Lex r s) :=
  ⟨(Prod.lex (IsWellFounded.toWellFoundedRelation _) (IsWellFounded.toWellFoundedRelation _)).wf⟩

instance [IsWellOrder α r] [IsWellOrder β s] : IsWellOrder (α × β) (Prod.Lex r s) where
  trichotomous := fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ =>
    match @trichotomous _ r _ a₁ b₁ with
    | Or.inl h₁ => Or.inl <| Prod.Lex.left _ _ h₁
    | Or.inr (Or.inr h₁) => Or.inr <| Or.inr <| Prod.Lex.left _ _ h₁
    | Or.inr (Or.inl (.refl _)) =>
        match @trichotomous _ s _ a₂ b₂ with
        | Or.inl h => Or.inl <| Prod.Lex.right _ h
        | Or.inr (Or.inr h) => Or.inr <| Or.inr <| Prod.Lex.right _ h
        | Or.inr (Or.inl (.refl _)) => Or.inr <| Or.inl rfl
  trans a b c h₁ h₂ := by
    cases' h₁ with a₁ a₂ b₁ b₂ ab a₁ b₁ b₂ ab <;> cases' h₂ with _ _ c₁ c₂ bc _ _ c₂ bc
    · exact Prod.Lex.left _ _ (trans ab bc)
    · exact Prod.Lex.left _ _ ab
    · exact Prod.Lex.left _ _ bc
    · exact Prod.Lex.right _ (trans ab bc)
  wf := (Prod.lex (IsWellFounded.toWellFoundedRelation _)
    (IsWellFounded.toWellFoundedRelation _)).wf

instance (r : α → α → Prop) [IsWellFounded α r] (f : β → α) : IsWellFounded _ (InvImage r f) :=
  ⟨InvImage.wf f IsWellFounded.wf⟩

instance (f : α → ℕ) : IsWellFounded _ (Measure f) :=
  ⟨(measure f).wf⟩

theorem Subrelation.isWellFounded (r : α → α → Prop) [IsWellFounded α r] {s : α → α → Prop}
    (h : Subrelation s r) : IsWellFounded α s :=
  ⟨h.wf IsWellFounded.wf⟩

namespace Set

/-- An unbounded or cofinal set. -/
def Unbounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∀ a, ∃ b ∈ s, ¬r b a

/-- A bounded or final set. Not to be confused with `Metric.bounded`. -/
def Bounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∃ a, ∀ b ∈ s, r b a

@[simp]
theorem not_bounded_iff {r : α → α → Prop} (s : Set α) : ¬Bounded r s ↔ Unbounded r s := by
  simp only [Bounded, Unbounded, not_forall, not_exists, exists_prop, not_and, not_not, iff_self]

@[simp]
theorem not_unbounded_iff {r : α → α → Prop} (s : Set α) : ¬Unbounded r s ↔ Bounded r s := by
  rw [not_iff_comm, not_bounded_iff]

theorem unbounded_of_isEmpty [IsEmpty α] {r : α → α → Prop} (s : Set α) : Unbounded r s :=
  isEmptyElim

end Set

namespace Prod

instance isRefl_preimage_fst {r : α → α → Prop} [IsRefl α r] : IsRefl (α × α) (Prod.fst ⁻¹'o r) :=
  ⟨fun a => refl_of r a.1⟩

instance isRefl_preimage_snd {r : α → α → Prop} [IsRefl α r] : IsRefl (α × α) (Prod.snd ⁻¹'o r) :=
  ⟨fun a => refl_of r a.2⟩

instance isTrans_preimage_fst {r : α → α → Prop} [IsTrans α r] :
    IsTrans (α × α) (Prod.fst ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

instance isTrans_preimage_snd {r : α → α → Prop} [IsTrans α r] :
    IsTrans (α × α) (Prod.snd ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

end Prod

/-! ### Strict-non strict relations -/


/-- An unbundled relation class stating that `r` is the nonstrict relation corresponding to the
strict relation `s`. Compare `Preorder.lt_iff_le_not_le`. This is mostly meant to provide dot
notation on `(⊆)` and `(⊂)`. -/
class IsNonstrictStrictOrder (α : Type _) (r s : α → α → Prop) where
  /-- The relation `r` is the nonstrict relation corresponding to the strict relation `s`. -/
  right_iff_left_not_left (a b : α) : s a b ↔ r a b ∧ ¬r b a

theorem right_iff_left_not_left {r s : α → α → Prop} [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  IsNonstrictStrictOrder.right_iff_left_not_left _ _

/-- A version of `right_iff_left_not_left` with explicit `r` and `s`. -/
theorem right_iff_left_not_left_of (r s : α → α → Prop) [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  right_iff_left_not_left

-- Porting note: no `dangerous_instance` linter
-- The free parameter `r` is strictly speaking not uniquely determined by `s`, but in practice it
-- always has a unique instance, so this is not dangerous.
-- see Note [lower instance priority]
-- @[nolint dangerous_instance]
instance (priority := 100) {r : α → α → Prop} {s : α → α → Prop}
    [IsNonstrictStrictOrder α r s] : IsIrrefl α s :=
  ⟨fun _ h => ((right_iff_left_not_left_of r s).1 h).2 ((right_iff_left_not_left_of r s).1 h).1⟩

/-! #### `⊆` and `⊂` -/


section Subset

variable [HasSubset α] {a b c : α}

@[refl]
theorem subset_refl [IsRefl α (· ⊆ ·)] (a : α) : a ⊆ a :=
  refl _

theorem subset_rfl [IsRefl α (· ⊆ ·)] : a ⊆ a :=
  refl _

theorem subset_of_eq [IsRefl α (· ⊆ ·)] : a = b → a ⊆ b := fun h => h ▸ subset_rfl

theorem superset_of_eq [IsRefl α (· ⊆ ·)] : a = b → b ⊆ a := fun h => h ▸ subset_rfl

theorem ne_of_not_subset [IsRefl α (· ⊆ ·)] : ¬a ⊆ b → a ≠ b :=
  mt subset_of_eq

theorem ne_of_not_superset [IsRefl α (· ⊆ ·)] : ¬a ⊆ b → b ≠ a :=
  mt superset_of_eq

@[trans]
theorem subset_trans [IsTrans α (· ⊆ ·)] {a b c : α} : a ⊆ b → b ⊆ c → a ⊆ c :=
  trans

theorem subset_antisymm [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) (h' : b ⊆ a) : a = b :=
  antisymm h h'

theorem superset_antisymm [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) (h' : b ⊆ a) : b = a :=
  antisymm' h h'

alias subset_of_eq ← Eq.subset'

--TODO: Fix it and kill `Eq.subset`
alias superset_of_eq ← Eq.superset
#align eq.superset Eq.superset

alias subset_trans ← HasSubset.Subset.trans

alias subset_antisymm ← HasSubset.Subset.antisymm

alias superset_antisymm ← HasSubset.Subset.antisymm'

theorem subset_antisymm_iff [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun h => ⟨h.subset', h.superset⟩, fun h => h.1.antisymm h.2⟩

theorem superset_antisymm_iff [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a = b ↔ b ⊆ a ∧ a ⊆ b :=
  ⟨fun h => ⟨h.superset, h.subset'⟩, fun h => h.1.antisymm' h.2⟩

end Subset

section Ssubset

variable [HasSSubset α]

theorem ssubset_irrefl [IsIrrefl α (· ⊂ ·)] (a : α) : ¬a ⊂ a :=
  irrefl _

theorem ssubset_irrfl [IsIrrefl α (· ⊂ ·)] {a : α} : ¬a ⊂ a :=
  irrefl _

theorem ne_of_ssubset [IsIrrefl α (· ⊂ ·)] {a b : α} : a ⊂ b → a ≠ b :=
  ne_of_irrefl

theorem ne_of_ssuperset [IsIrrefl α (· ⊂ ·)] {a b : α} : a ⊂ b → b ≠ a :=
  ne_of_irrefl'

@[trans]
theorem ssubset_trans [IsTrans α (· ⊂ ·)] {a b c : α} : a ⊂ b → b ⊂ c → a ⊂ c :=
  trans

theorem ssubset_asymm [IsAsymm α (· ⊂ ·)] {a b : α} (h : a ⊂ b) : ¬b ⊂ a :=
  asymm h

alias ssubset_irrfl ← HasSSubset.SSubset.false

alias ne_of_ssubset ← HasSSubset.SSubset.ne
#align has_ssubset.ssubset.ne HasSSubset.SSubset.ne

alias ne_of_ssuperset ← HasSSubset.SSubset.ne'

alias ssubset_trans ← HasSSubset.SSubset.trans

alias ssubset_asymm ← HasSSubset.SSubset.asymm

end Ssubset

section SubsetSsubset

variable [HasSubset α] [HasSSubset α] [IsNonstrictStrictOrder α (· ⊆ ·) (· ⊂ ·)] {a b c : α}

theorem ssubset_iff_subset_not_subset : a ⊂ b ↔ a ⊆ b ∧ ¬b ⊆ a :=
  right_iff_left_not_left

theorem subset_of_ssubset (h : a ⊂ b) : a ⊆ b :=
  (ssubset_iff_subset_not_subset.1 h).1

theorem not_subset_of_ssubset (h : a ⊂ b) : ¬b ⊆ a :=
  (ssubset_iff_subset_not_subset.1 h).2

theorem not_ssubset_of_subset (h : a ⊆ b) : ¬b ⊂ a := fun h' => not_subset_of_ssubset h' h

theorem ssubset_of_subset_not_subset (h₁ : a ⊆ b) (h₂ : ¬b ⊆ a) : a ⊂ b :=
  ssubset_iff_subset_not_subset.2 ⟨h₁, h₂⟩

alias subset_of_ssubset ← HasSSubset.SSubset.subset
#align has_ssubset.ssubset.subset HasSSubset.SSubset.subset

alias not_subset_of_ssubset ← HasSSubset.SSubset.not_subset

alias not_ssubset_of_subset ← HasSubset.Subset.not_ssubset

alias ssubset_of_subset_not_subset ← HasSubset.Subset.ssubset_of_not_subset

theorem ssubset_of_subset_of_ssubset [IsTrans α (· ⊆ ·)] (h₁ : a ⊆ b) (h₂ : b ⊂ c) : a ⊂ c :=
  (h₁.trans h₂.subset).ssubset_of_not_subset fun h => h₂.not_subset <| h.trans h₁

theorem ssubset_of_ssubset_of_subset [IsTrans α (· ⊆ ·)] (h₁ : a ⊂ b) (h₂ : b ⊆ c) : a ⊂ c :=
  (h₁.subset.trans h₂).ssubset_of_not_subset fun h => h₁.not_subset <| h₂.trans h

theorem ssubset_of_subset_of_ne [IsAntisymm α (· ⊆ ·)] (h₁ : a ⊆ b) (h₂ : a ≠ b) : a ⊂ b :=
  h₁.ssubset_of_not_subset <| mt h₁.antisymm h₂

theorem ssubset_of_ne_of_subset [IsAntisymm α (· ⊆ ·)] (h₁ : a ≠ b) (h₂ : a ⊆ b) : a ⊂ b :=
  ssubset_of_subset_of_ne h₂ h₁

theorem eq_or_ssubset_of_subset [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) : a = b ∨ a ⊂ b :=
  (em (b ⊆ a)).imp h.antisymm h.ssubset_of_not_subset

theorem ssubset_or_eq_of_subset [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) : a ⊂ b ∨ a = b :=
  (eq_or_ssubset_of_subset h).symm

alias ssubset_of_subset_of_ssubset ← HasSubset.Subset.trans_ssubset

alias ssubset_of_ssubset_of_subset ← HasSSubset.SSubset.trans_subset

alias ssubset_of_subset_of_ne ← HasSubset.Subset.ssubset_of_ne

alias ssubset_of_ne_of_subset ← Ne.ssubset_of_subset

alias eq_or_ssubset_of_subset ← HasSubset.Subset.eq_or_ssubset

alias ssubset_or_eq_of_subset ← HasSubset.Subset.ssubset_or_eq

theorem ssubset_iff_subset_ne [IsAntisymm α (· ⊆ ·)] : a ⊂ b ↔ a ⊆ b ∧ a ≠ b :=
  ⟨fun h => ⟨h.subset, h.ne⟩, fun h => h.1.ssubset_of_ne h.2⟩

theorem subset_iff_ssubset_or_eq [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] :
    a ⊆ b ↔ a ⊂ b ∨ a = b :=
  ⟨fun h => h.ssubset_or_eq, fun h => h.elim subset_of_ssubset subset_of_eq⟩

end SubsetSsubset

/-! ### Conversion of bundled order typeclasses to unbundled relation typeclasses -/


instance [Preorder α] : IsRefl α (· ≤ ·) :=
  ⟨le_refl⟩

instance [Preorder α] : IsRefl α (· ≥ ·) :=
  IsRefl.swap _

instance [Preorder α] : IsTrans α (· ≤ ·) :=
  ⟨@le_trans _ _⟩

instance [Preorder α] : IsTrans α (· ≥ ·) :=
  IsTrans.swap _

instance [Preorder α] : IsPreorder α (· ≤ ·) where

instance [Preorder α] : IsPreorder α (· ≥ ·) where

instance [Preorder α] : IsIrrefl α (· < ·) :=
  ⟨lt_irrefl⟩

instance [Preorder α] : IsIrrefl α (· > ·) :=
  IsIrrefl.swap _

instance [Preorder α] : IsTrans α (· < ·) :=
  ⟨@lt_trans _ _⟩

instance [Preorder α] : IsTrans α (· > ·) :=
  IsTrans.swap _

instance [Preorder α] : IsAsymm α (· < ·) :=
  ⟨@lt_asymm _ _⟩

instance [Preorder α] : IsAsymm α (· > ·) :=
  IsAsymm.swap _

instance [Preorder α] : IsAntisymm α (· < ·) :=
  IsAsymm.is_antisymm _

instance [Preorder α] : IsAntisymm α (· > ·) :=
  IsAsymm.is_antisymm _

instance [Preorder α] : IsStrictOrder α (· < ·) where

instance [Preorder α] : IsStrictOrder α (· > ·) where

instance [Preorder α] : IsNonstrictStrictOrder α (· ≤ ·) (· < ·) :=
  ⟨@lt_iff_le_not_le _ _⟩

instance [PartialOrder α] : IsAntisymm α (· ≤ ·) :=
  ⟨@le_antisymm _ _⟩

instance [PartialOrder α] : IsAntisymm α (· ≥ ·) :=
  IsAntisymm.swap _

instance [PartialOrder α] : IsPartialOrder α (· ≤ ·) where

instance [PartialOrder α] : IsPartialOrder α (· ≥ ·) where

instance [LinearOrder α] : IsTotal α (· ≤ ·) :=
  ⟨le_total⟩

instance [LinearOrder α] : IsTotal α (· ≥ ·) :=
  IsTotal.swap _

-- Porting note: this was `by infer_instance` before
instance [LinearOrder α] : IsTotalPreorder α (· ≤ ·) where

instance [LinearOrder α] : IsTotalPreorder α (· ≥ ·) where

instance [LinearOrder α] : IsLinearOrder α (· ≤ ·) where

instance [LinearOrder α] : IsLinearOrder α (· ≥ ·) where

instance [LinearOrder α] : IsTrichotomous α (· < ·) :=
  ⟨lt_trichotomy⟩

instance [LinearOrder α] : IsTrichotomous α (· > ·) :=
  IsTrichotomous.swap _

instance [LinearOrder α] : IsTrichotomous α (· ≤ ·) :=
  IsTotal.is_trichotomous _

instance [LinearOrder α] : IsTrichotomous α (· ≥ ·) :=
  IsTotal.is_trichotomous _

instance [LinearOrder α] : IsStrictTotalOrder α (· < ·) where

instance [LinearOrder α] : IsOrderConnected α (· < ·) := by infer_instance

instance [LinearOrder α] : IsIncompTrans α (· < ·) := by infer_instance

instance [LinearOrder α] : IsStrictWeakOrder α (· < ·) := by infer_instance

theorem transitive_le [Preorder α] : Transitive (@LE.le α _) :=
  transitive_of_trans _

theorem transitive_lt [Preorder α] : Transitive (@LT.lt α _) :=
  transitive_of_trans _

theorem transitive_ge [Preorder α] : Transitive (@GE.ge α _) :=
  transitive_of_trans _

theorem transitive_gt [Preorder α] : Transitive (@GT.gt α _) :=
  transitive_of_trans _

instance OrderDual.is_total_le [LE α] [h : IsTotal α (· ≤ ·)] : IsTotal αᵒᵈ (· ≤ ·) :=
  @IsTotal.swap α _ h

instance : WellFoundedLt ℕ :=
  ⟨Nat.lt_wfRel.wf⟩
#align nat.lt_wf Nat.lt_wfRel

instance Nat.lt.isWellOrder : IsWellOrder ℕ (· < ·) where
#align nat.lt.is_well_order Nat.lt.isWellOrder

instance [LinearOrder α] [h : IsWellOrder α (· < ·)] : IsWellOrder αᵒᵈ (· > ·) := h

instance [LinearOrder α] [h : IsWellOrder α (· > ·)] : IsWellOrder αᵒᵈ (· < ·) := h