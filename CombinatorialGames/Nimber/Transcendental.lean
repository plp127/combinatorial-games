/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Nimber.SimplestExtension.Algebraic

universe u

noncomputable section

open Ordinal Polynomial
namespace Nimber.IsAlgClosed

variable {t : Nimber.{u}} (ht : IsAlgClosed t)
include ht

theorem isRing_pow_omega0 : IsRing (of (val t ^ ω)) := by
  refine ⟨ht.opow _, fun y z hy hz ↦ ?_, ne_of_gt (by simp [ht.one_lt])⟩
  obtain ⟨py, hyd, rfl⟩ := eq_oeval_of_lt_opow_omega0 hy
  obtain ⟨pz, hzd, rfl⟩ := eq_oeval_of_lt_opow_omega0 hz
  rw [← ht.eval_eq_of_lt hyd, ← ht.eval_eq_of_lt hzd, ← eval_mul, ht.eval_eq_of_lt]
  on_goal 1 => apply oeval_lt_opow_omega0
  all_goals exact forall_coeff_mul_lt ht.toIsRing hyd hzd

-- not an instance because `ht` is not inferrable
abbrev algebraPowOmega0 : Algebra ht.toIsField.toSubfield ht.isRing_pow_omega0.toSubring :=
  (Subring.inclusion (Set.Iio_subset_Iio (val_le_iff.1 (left_le_opow _ omega0_pos)))).toAlgebra

def algEquivPolynomial :
    letI := ht.algebraPowOmega0
    ht.isRing_pow_omega0.toSubring ≃ₐ[ht.toIsField.toSubfield]
    ht.toIsField.toSubfield[X] :=
  letI := ht.algebraPowOmega0
  .symm <| .ofBijective (Polynomial.aeval
      ⟨t, val_lt_iff.1 (left_lt_opow ht.one_lt one_lt_omega0)⟩) <| by
    have algMap (x : ht.toIsField.toSubfield) :
        algebraMap ht.toIsField.toSubfield ht.isRing_pow_omega0.toSubring x = ⟨x, _⟩ := rfl
    refine ⟨fun p q hpq => ?_, ?_⟩
    · rw [aeval_def, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map,
        ← ht.isRing_pow_omega0.toSubring.subtype_injective.eq_iff,
        ← eval_map_apply, ← eval_map_apply, Subring.subtype_apply,
        ht.eval_eq_of_lt (by simp [algMap]), ht.eval_eq_of_lt (by simp [algMap]),
        oeval_eq_oeval_iff (by simp [algMap]) (by simp [algMap]),
        (map_injective _ (Subring.subtype_injective _)).eq_iff] at hpq
      refine map_injective _ ?_ hpq
      exact fun _ _ h => by simpa [algMap] using h
    · intro y
      obtain ⟨y, hy⟩ := y
      obtain ⟨py, hyd, rfl⟩ := eq_oeval_of_lt_opow_omega0 hy
      refine ⟨ht.toIsField.embed py hyd, ?_⟩
      rw [aeval_def, eval₂_eq_eval_map, ← ht.isRing_pow_omega0.toSubring.subtype_injective.eq_iff,
        ← eval_map_apply, map_map]
      change eval t (map ht.toIsField.toSubfield.subtype (ht.toIsField.embed py hyd)) = oeval t py
      rw [ht.toIsField.map_embed, ht.eval_eq_of_lt hyd]

theorem coe_algEquivPolynomial_symm_apply (p : ht.toIsField.toSubfield[X]) :
    letI := ht.algebraPowOmega0
    (ht.algEquivPolynomial.symm p : Nimber) = p.eval₂ ht.toIsField.toSubfield.subtype t := by
  unfold algEquivPolynomial
  rw [← ht.isRing_pow_omega0.toSubring.subtype_apply,
    @AlgEquiv.symm_symm, @AlgEquiv.ofBijective_apply,
    @aeval_def, ← eval_map, ← eval_map_apply, map_map, eval_map]
  rfl

def ringEquivPolynomial : ht.isRing_pow_omega0.toSubring ≃+* ht.toIsField.toSubfield[X] :=
  letI := ht.algebraPowOmega0
  ht.algEquivPolynomial.toRingEquiv

theorem coe_ringEquivPolynomial_symm_apply (p : ht.toIsField.toSubfield[X]) :
    (ht.ringEquivPolynomial.symm p : Nimber) = p.eval₂ ht.toIsField.toSubfield.subtype t :=
  ht.coe_algEquivPolynomial_symm_apply p

theorem opow_omega0_mul_add_eq {x : Nimber} (hx : x < t) (n : ℕ) :
    ∗(val t ^ (ω * (1 + val x) + n)) = ((t - x) ^ (n + 1))⁻¹ := by
  induction x using WellFoundedLT.induction generalizing n with | ind x ihx
  induction n with
  | zero =>
    rw [← inv_eq_iff_eq_inv]
    have hy {y : Nimber} (hy : y < ∗(val t ^ (ω * (1 + val x)))) : (t - x) * y ≠ 1 := by
      -- `y` is a `t`-linear combination of [powers] of `t`
      -- which must be either powers of `t` or negative powers of `t - z` for `z < x`
      -- these all lie in the localization of `t[t]` at `t - z` for `z < x`
      -- which admits a ring homomorphism into `t` sending `t` to `x`
      -- this sends `t - x` to `0`, so it cannot have an inverse
      sorry
    sorry
  | succ n ihn =>
    sorry

end Nimber.IsAlgClosed
