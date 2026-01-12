/-
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.Small.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Type of players

This file implements the two-element type of players (`Left`, `Right`), alongside other basic
notational machinery to be used within game theory.
-/

universe u

/-! ### Players -/

/-- Either the Left or Right player. -/
@[aesop safe cases, grind cases]
inductive Player where
  /-- The Left player. -/
  | left  : Player
  /-- The Right player. -/
  | right : Player
deriving DecidableEq, Fintype, Inhabited

namespace Player

/-- Specify a function `Player → α` from its two outputs. -/
@[simp]
abbrev cases {α : Sort*} (l r : α) : Player → α
  | left => l
  | right => r

lemma apply_cases {α β : Sort*} (f : α → β) (l r : α) (p : Player) :
    f (cases l r p) = cases (f l) (f r) p := by
  cases p <;> rfl

@[simp]
theorem cases_inj {α : Sort*} {l₁ r₁ l₂ r₂ : α} :
    cases l₁ r₁ = cases l₂ r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ :=
  ⟨fun h ↦ ⟨congr($h left), congr($h right)⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

theorem const_of_left_eq_right {α : Sort*} {f : Player → α} (hf : f left = f right) :
    ∀ p q, f p = f q
  | left, left | right, right => rfl
  | left, right => hf
  | right, left => hf.symm

theorem const_of_left_eq_right' {f : Player → Prop} (hf : f left ↔ f right) (p q) : f p ↔ f q :=
  (const_of_left_eq_right hf.eq ..).to_iff

@[simp]
protected lemma «forall» {p : Player → Prop} :
    (∀ x, p x) ↔ p left ∧ p right :=
  ⟨fun h ↦ ⟨h left, h right⟩, fun ⟨hl, hr⟩ ↦ fun | left => hl | right => hr⟩

@[simp]
protected lemma «exists» {p : Player → Prop} :
    (∃ x, p x) ↔ p left ∨ p right :=
  ⟨fun | ⟨left, h⟩ => .inl h | ⟨right, h⟩ => .inr h, fun | .inl h | .inr h => ⟨_, h⟩⟩

instance : Neg Player where
  neg := cases right left

@[simp, grind =] lemma neg_left : -left = right := rfl
@[simp, grind =] lemma neg_right : -right = left := rfl
@[simp] theorem eq_neg : ∀ {p q : Player}, p = -q ↔ p ≠ q := by decide
@[simp] theorem neg_eq : ∀ {p q : Player}, -p = q ↔ p ≠ q := by decide
theorem ne_neg : ∀ {p q : Player}, p ≠ -q ↔ p = q := by decide
theorem neg_ne : ∀ {p q : Player}, -p ≠ q ↔ p = q := by decide
theorem neg_ne_self : ∀ (p : Player), -p ≠ p := by decide
theorem self_ne_neg : ∀ (p : Player), p ≠ -p := by decide

instance : InvolutiveNeg Player where
  neg_neg := by decide

/--
The multiplication of `Player`s is used to state the lemmas about the multiplication of
combinatorial games, such as `IGame.mulOption_mem_moves_mul`.
-/
instance : Mul Player where mul
  | left, p => p
  | right, p => -p

@[simp, grind =] lemma left_mul (p : Player) : left * p = p := rfl
@[simp, grind =] lemma right_mul (p : Player) : right * p = -p := rfl
@[simp, grind =] lemma mul_left : ∀ p, p * left = p := by decide
@[simp, grind =] lemma mul_right : ∀ p, p * right = -p := by decide
@[simp, grind =] lemma mul_self : ∀ p, p * p = left := by decide

instance : HasDistribNeg Player where
  neg_mul := by decide
  mul_neg := by decide

instance : CommGroup Player where
  one := left
  inv := id
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

@[simp, grind =] lemma one_eq_left : 1 = left := rfl
@[simp, grind =] lemma inv_eq_self (p : Player) : p⁻¹ = p := rfl

section LE
variable {α : Type*} [LE α] (p : Player) (a b : α)

@[to_dual self (reorder := a b)] def le : Prop := p.casesOn (a ≤ b) (b ≤ a)
@[simp, to_dual self] theorem left_le_eq : left.le a b = (a ≤ b) := rfl
@[simp, to_dual self] theorem right_le_eq : right.le a b = (b ≤ a) := rfl
@[simp, to_dual self] theorem neg_le : (-p).le a b = p.le b a := p.casesOn rfl rfl

end LE

section LT
variable {α : Type*} [LT α] (p : Player) (a b : α)

@[to_dual self (reorder := a b)] def lt : Prop := p.casesOn (a < b) (b < a)
@[simp, to_dual self] theorem left_lt_eq : left.lt a b = (a < b) := rfl
@[simp, to_dual self] theorem right_lt_eq : right.lt a b = (b < a) := rfl
@[simp, to_dual self] theorem neg_lt : (-p).lt a b = p.lt b a := p.casesOn rfl rfl

end LT

section Preorder

variable {α : Type*} [Preorder α] {p : Player} {a b c : α}

@[simp] lemma le_refl : ∀ a : α, p.le a a := p.casesOn _root_.le_refl _root_.le_refl

lemma le_rfl : p.le a a := le_refl a

@[to_dual ge_trans] lemma le_trans : p.le a b → p.le b c → p.le a c :=
  p.casesOn _root_.le_trans _root_.ge_trans

@[to_dual self]
lemma lt_iff_le_not_ge : p.lt a b ↔ p.le a b ∧ ¬p.le b a :=
  p.casesOn _root_.lt_iff_le_not_ge _root_.lt_iff_le_not_ge

@[to_dual self]
lemma lt_of_le_not_ge (hab : p.le a b) (hba : ¬p.le b a) : p.lt a b := lt_iff_le_not_ge.2 ⟨hab, hba⟩

@[to_dual ge_of_eq]
lemma le_of_eq (hab : a = b) : p.le a b := hab ▸ le_rfl
@[to_dual self] lemma le_of_lt (hab : p.lt a b) : p.le a b := (lt_iff_le_not_ge.1 hab).1
@[to_dual self] lemma not_le_of_gt (hab : p.lt a b) : ¬p.le b a := (lt_iff_le_not_ge.1 hab).2
@[to_dual self] lemma not_lt_of_ge (hab : p.le a b) : ¬p.lt b a := imp_not_comm.1 not_le_of_gt hab

@[to_dual self] alias lt.not_ge := not_le_of_gt
@[to_dual self] alias le.not_gt := not_lt_of_ge

@[to_dual self] lemma lt_irrefl (a : α) : ¬p.lt a a := fun h ↦ not_le_of_gt h le_rfl

@[to_dual lt_of_lt_of_le']
lemma lt_of_lt_of_le (hab : p.lt a b) (hbc : p.le b c) : p.lt a c :=
  lt_of_le_not_ge (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_gt hab (le_trans hbc hca)

@[to_dual lt_of_le_of_lt']
lemma lt_of_le_of_lt (hab : p.le a b) (hbc : p.lt b c) : p.lt a c :=
  lt_of_le_not_ge (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_gt hbc (le_trans hca hab)

@[to_dual gt_trans]
lemma lt_trans : p.lt a b → p.lt b c → p.lt a c := fun h₁ h₂ => lt_of_lt_of_le h₁ (le_of_lt h₂)

@[to_dual ne_of_gt]
lemma ne_of_lt (h : p.lt a b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual self]
lemma lt_asymm (h : p.lt a b) : ¬p.lt b a := fun h1 : p.lt b a => lt_irrefl a (lt_trans h h1)

@[to_dual self] alias not_lt_of_gt := lt_asymm

@[to_dual le_of_lt_or_eq']
lemma le_of_lt_or_eq (h : p.lt a b ∨ a = b) : p.le a b := h.elim le_of_lt le_of_eq
@[to_dual le_of_eq_or_lt']
lemma le_of_eq_or_lt (h : a = b ∨ p.lt a b) : p.le a b := h.elim le_of_eq le_of_lt

instance instTransLE : @Trans α α α p.le p.le p.le := ⟨le_trans⟩
instance instTransLT : @Trans α α α p.lt p.lt p.lt := ⟨lt_trans⟩
instance instTransLTLE : @Trans α α α p.lt p.le p.lt := ⟨lt_of_lt_of_le⟩
instance instTransLELT : @Trans α α α p.le p.lt p.lt := ⟨lt_of_le_of_lt⟩
-- we have to express the following 4 instances in terms of `≥` instead of flipping the arguments
-- to `≤`, because otherwise `calc` gets confused.
@[to_dual existing instTransLE]
instance instTransGE : @Trans α α α (fun a b => p.le b a) (fun a b => p.le b a)
    (fun a b => p.le b a) := ⟨ge_trans⟩
@[to_dual existing instTransLT]
instance instTransGT : @Trans α α α (fun a b => p.lt b a) (fun a b => p.lt b a)
    (fun a b => p.lt b a) := ⟨gt_trans⟩
@[to_dual existing instTransLTLE]
instance instTransGTGE : @Trans α α α (fun a b => p.lt b a) (fun a b => p.le b a)
    (fun a b => p.lt b a) := ⟨lt_of_lt_of_le'⟩
@[to_dual existing instTransLELT]
instance instTransGEGT : @Trans α α α (fun a b => p.le b a) (fun a b => p.lt b a)
    (fun a b => p.lt b a) := ⟨lt_of_le_of_lt'⟩

end Preorder

section PartialOrder
variable {α : Type*} [PartialOrder α] {p : Player} {a b c : α}

@[to_dual ge_antisymm]
lemma le_antisymm : p.le a b → p.le b a → a = b := p.casesOn _root_.le_antisymm _root_.ge_antisymm

@[to_dual eq_of_ge_of_le]
alias eq_of_le_of_ge := le_antisymm

@[to_dual ge_antisymm_iff]
lemma le_antisymm_iff : a = b ↔ p.le a b ∧ p.le b a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

@[to_dual lt_of_le_of_ne']
lemma lt_of_le_of_ne : p.le a b → a ≠ b → p.lt a b := fun h₁ h₂ =>
  lt_of_le_not_ge h₁ <| mt (le_antisymm h₁) h₂

end PartialOrder

end Player

open Player

/-! ### OfSets -/

/--
Type class for the `ofSets` operation.
Used to implement the `!{st}` and `!{s | t}` syntax.
-/
class OfSets (α : Type (u + 1)) (Valid : outParam ((Player → Set α) → Prop)) where
  /-- Construct a combinatorial game from its left and right sets. -/
  ofSets (st : Player → Set α) (h : Valid st) [Small.{u} (st left)] [Small.{u} (st right)] : α
export OfSets (ofSets)

@[inherit_doc OfSets.ofSets]
macro "!{" st:term "}'" h:term:max : term => `(OfSets.ofSets $st $h)

@[inherit_doc OfSets.ofSets]
macro "!{" s:term " | " t:term "}'" h:term:max : term => `(!{Player.cases $s $t}'$h)

macro "of_sets_tactic" : tactic =>
  `(tactic| first
    | done
    | trivial
    | assumption
    | aesop
    | fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
where `h` is a proof that sets are valid"
   )

@[inherit_doc OfSets.ofSets]
macro:max "!{" st:term "}" : term => `(!{$st}'(by of_sets_tactic))

@[inherit_doc OfSets.ofSets]
macro:max "!{" s:term " | " t:term "}" : term => `(!{$s | $t}'(by of_sets_tactic))

recommended_spelling "ofSets" for "!{st}'h" in [ofSets, «term!{_}'_»]
recommended_spelling "ofSets" for "!{s | t}'h" in [ofSets, «term!{_|_}'_»]
recommended_spelling "ofSets" for "!{st}" in [ofSets, «term!{_}»]
recommended_spelling "ofSets" for "!{s | t}" in [ofSets, «term!{_|_}»]

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab OfSets.ofSets]
def delabOfSets : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``OfSets.ofSets 7
  withNaryArg 3 do
    let e ← getExpr
    if e.isAppOfArity' ``Player.cases 3 then
      let s ← withNaryArg 1 delab
      let t ← withNaryArg 2 delab
      `(!{$s | $t})
    else
      let st ← delab
      `(!{$st})

theorem ofSets_eq_ofSets_cases {α} {Valid : (Player → Set α) → Prop} [OfSets α Valid]
    (st : Player → Set α) (h : Valid st) [Small (st left)] [Small (st right)] :
    !{st} = !{st left | st right}'(by convert h; aesop) := by
  congr; ext1 p; cases p <;> rfl
