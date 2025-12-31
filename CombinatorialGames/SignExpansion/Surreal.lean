/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.SignExpansion.Basic
import CombinatorialGames.Surreal.Birthday.Basic

/-!
# Sign Expansions

Every surreal number has a sign expansion, a function from its birthday to the set `{-1, 1}`.
This sign expansion uniquely identifies the number.
-/

universe u

noncomputable section

namespace Surreal
open IGame SignExpansion

def truncate (o : NatOrdinal.{u}) : Surreal.{u} →o Surreal.{u} where
  toFun x := @mk !{fun p => {s : IGame.{u} | s.birthday < o} ∩
    {s | ∃ _ : s.Numeric, p.cases (.mk s < x) (x < .mk s)}} <| by
      rw [numeric_def]
      refine ⟨fun y hy z hz => ?_, fun p y hy => ?_⟩
      · rw [moves_ofSets] at hy hz
        exact (@mk_lt_mk y z hy.2.1 hz.2.1).mp (hy.2.2.trans hz.2.2)
      · rw [moves_ofSets] at hy
        exact hy.2.1
  monotone' := by
    intro x y hxy
    simp_rw [Surreal.mk_le_mk]
    rw [le_iff_forall_lf]
    refine ⟨fun z hz => left_lf ?_, fun z hz => lf_right ?_⟩ <;> rw [moves_ofSets] at hz ⊢
    · exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hxy⟩
    · exact ⟨hz.1, hz.2.1, lt_of_le_of_lt hxy hz.2.2⟩

theorem truncate_apply (o : NatOrdinal.{u}) (x : Surreal.{u}) :
    ∃ h : Numeric _, truncate o x = @mk !{fun p => {s : IGame.{u} | s.birthday < o} ∩
      {s | ∃ _ : s.Numeric, p.cases (.mk s < x) (x < .mk s)}} h := ⟨_, rfl⟩

theorem birthday_truncate_le (o : NatOrdinal.{u}) (x : Surreal.{u}) :
    (truncate o x).birthday ≤ o := by
  obtain ⟨_, h⟩ := truncate_apply o x
  rw [h]
  apply (birthday_mk_le _).trans
  rw [birthday_le_iff, ← @Player.forall fun p => ∀ y ∈ moves p _, y.birthday < o]
  intro p y hy
  rw [moves_ofSets] at hy
  exact hy.1

theorem truncate_of_birthday_le {o : NatOrdinal.{u}} {x : Surreal.{u}}
    (h : x.birthday ≤ o) : x.truncate o = x := by
  obtain ⟨k, nk, rfl, hk⟩ := x.birthday_eq_iGameBirthday
  rw [← hk] at h
  obtain ⟨_, ht⟩ := truncate_apply o (mk k)
  rw [ht, Surreal.mk_eq_mk]
  symm
  apply Fits.equiv_of_forall_birthday_le
  · constructor <;> simp +contextual
  · intro z nz hz
    apply le_of_not_gt
    intro hbb
    have hne : mk z ≠ mk k := by
      intro eq
      rw [hk, ← eq] at hbb
      exact not_le_of_gt hbb (birthday_mk_le z)
    obtain hzk | hkz := lt_or_gt_of_ne hne
    · refine hz.left z ?_ le_rfl
      rw [moves_ofSets]
      exact ⟨hbb.trans_le h, nz, hzk⟩
    · refine hz.right z ?_ le_rfl
      rw [moves_ofSets]
      exact ⟨hbb.trans_le h, nz, hkz⟩

@[simp]
theorem truncate_eq_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    x.truncate o = x ↔ x.birthday ≤ o := by
  refine ⟨fun h => ?_, truncate_of_birthday_le⟩
  refine le_of_not_gt fun ho => ?_
  refine ne_of_lt ?_ (congrArg birthday h)
  exact (x.birthday_truncate_le o).trans_lt ho

def ofSurreal (x : Surreal.{u}) : SignExpansion where
  sign i := .sign (x - x.truncate i)
  isUpperSet_preimage_singleton_zero' := by
    intro a b hab ha
    rw [Set.mem_preimage, Set.mem_singleton_iff,
      sign_eq_zero_iff, sub_eq_zero, eq_comm, truncate_eq_iff] at ha ⊢
    exact ha.trans hab

@[simp]
theorem size_ofSurreal (x : Surreal.{u}) :
    (ofSurreal x).length = x.birthday := by
  apply eq_of_forall_ge_iff
  intro c
  cases c with
  | top => simp
  | coe c =>
    rw [← apply_eq_zero, WithTop.coe_le_coe, ofSurreal, coe_mk,
      sign_eq_zero_iff, sub_eq_zero, eq_comm, truncate_eq_iff]

theorem ofSurreal_apply (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    ofSurreal x o = .sign (x - x.truncate o) := rfl

end Surreal
