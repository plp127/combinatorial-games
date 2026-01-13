/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Surreal.Basic

universe u

namespace Surreal.Multiplication
open IGame

def Rel2 (a b : IGame × IGame) : Prop :=
  ((a.1 = b.1 ∨ Subposition a.1 b.1) ∨ (a.1 = b.2 ∨ Subposition a.1 b.2)) ∧
  (Subposition a.2 b.1 ∨ Subposition a.2 b.2) ∨
  (Subposition a.1 b.1 ∨ Subposition a.1 b.2) ∧
  ((a.2 = b.1 ∨ Subposition a.2 b.1) ∨ (a.2 = b.2 ∨ Subposition a.2 b.2))

def WRel2 (a b : IGame × IGame) : Prop :=
  ((a.1 = b.1 ∨ Subposition a.1 b.1) ∨ (a.1 = b.2 ∨ Subposition a.1 b.2)) ∧
  ((a.2 = b.1 ∨ Subposition a.2 b.1) ∨ (a.2 = b.2 ∨ Subposition a.2 b.2))

theorem rel2_wf : WellFounded Rel2 := by
  sorry

end Surreal.Multiplication
