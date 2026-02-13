/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Nimber.SimplestExtension.Algebraic

universe u

theorem Ordinal.opow_eq_one_iff {a b : Ordinal} : a ^ b = 1 ↔ a = 1 ∨ b = 0 := by
  refine ⟨fun h => ?_, by simp +contextual [or_imp]⟩
  contrapose! h
  by_cases ha : a = 0
  · simp [ha, h.2]
  apply ne_of_gt
  have h1a : 1 < a := lt_of_not_ge (by simp [le_one_iff, ha, h.1])
  rw [← opow_zero a, opow_lt_opow_iff_right h1a]
  exact pos_of_ne_zero h.2

theorem Ordinal.exists_omega0_mul_add_natCast (o : Ordinal) :
    ∃ a b, omega0 * a + Nat.cast b = o := by
  obtain ⟨b, hb⟩ := lt_omega0.1 (mod_lt o omega0_ne_zero)
  refine ⟨o / omega0, b, ?_⟩
  rw [← hb, div_add_mod]

theorem Ordinal.one_le_of_lt {a b : Ordinal} (hab : a < b) : 1 ≤ b := by
  rw [← succ_zero, Order.succ_le_iff]
  exact (zero_le a).trans_lt hab

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

private theorem subring_aux {x : Nimber} (hx : IsRing (∗(val t ^ (ω * (1 + val x))))) :
    ht.isRing_pow_omega0.toSubring ≤ hx.toSubring :=
  Set.Iio_subset_Iio (of.monotone (Ordinal.opow_le_opow_right
    (val_zero.symm.trans_lt (val.strictMono ht.zero_lt)) (by simp)))

private theorem next_field_aux {x : Nimber} (hx : x < t) (n : ℕ) :
    ∗(val t ^ (ω * (1 + val x) + n)) = ((t - x) ^ (n + 1))⁻¹ ∧
      ∃ rx : IsRing (∗(val t ^ (ω * (1 + val x)))),
        letI : Algebra ht.isRing_pow_omega0.toSubring rx.toSubring :=
          (Subring.inclusion (subring_aux ht rx)).toAlgebra
        IsLocalization (Submonoid.comap ht.ringEquivPolynomial.toMonoidHom
          (Submonoid.closure ((fun u => Polynomial.X - Polynomial.C u) '' Set.Iio ⟨x, hx⟩)))
          rx.toSubring := by
  induction x using WellFoundedLT.induction generalizing n with | ind x ihx
  induction n with
  | zero =>
    rw [← inv_eq_iff_eq_inv]
    have hr : IsRing (∗(val t ^ (ω * (1 + val x)))) := by
      refine ht.toIsField.isRing_opow_of_mul_lt
        (mul_ne_zero Ordinal.omega0_ne_zero
          (add_pos_of_pos_of_nonneg zero_lt_one (_root_.zero_le (val x))).ne')
        fun u v hu hv => ?_
      obtain ⟨ua, ub, rfl⟩ := exists_omega0_mul_add_natCast u
      obtain ⟨va, vb, rfl⟩ := exists_omega0_mul_add_natCast v
      wlog! haa : va < ua generalizing ua ub va vb with ih
      · obtain haa | rfl := haa.lt_or_eq
        · rw [mul_comm]
          exact ih va vb hv ua ub hu haa
        obtain ha1 | h1a := lt_or_ge ua 1
        · cases Ordinal.lt_one_iff_zero.1 ha1
          simp only [mul_zero, zero_add]
          refine lt_of_lt_of_le (ht.isRing_pow_omega0.mul_lt ?_ ?_) ?_
          · rw [of.lt_iff_lt, opow_lt_opow_iff_right (by simp [ht.one_lt])]
            exact nat_lt_omega0 _
          · rw [of.lt_iff_lt, opow_lt_opow_iff_right (by simp [ht.one_lt])]
            exact nat_lt_omega0 _
          · rw [of.le_iff_le, opow_le_opow_iff_right (by simp [ht.one_lt])]
            simp
        · obtain ⟨ua, rfl⟩ := exists_add_of_le h1a
          have hux : ∗ua < x := by simpa using lt_of_add_lt_of_nonneg_left hu
          specialize ihx (∗ua) hux (hux.trans hx)
          simp_rw [val_of] at ihx
          rw [(ihx ub).left, (ihx vb).left, ← mul_inv, ← pow_add, ← add_assoc, ← (ihx _).left,
            of.lt_iff_lt, opow_lt_opow_iff_right (by simp [ht.one_lt])]
          refine lt_of_lt_of_le (add_lt_add_right (nat_lt_omega0 _) _) ?_
          rw [← mul_add_one, add_assoc]
          exact mul_le_mul_right (add_le_add_right (Order.add_one_le_of_lt (of_lt_iff.1 hux)) 1) ω
      obtain ⟨ua, rfl⟩ := exists_add_of_le (one_le_of_lt haa)
      obtain ha1 | h1a := lt_or_ge va 1
      · cases Ordinal.lt_one_iff_zero.1 ha1
        clear hv haa ha1
        rw [mul_zero, zero_add, opow_natCast, ← ht.pow_eq/-, ← one_mul (_ * t ^ vb)-/]
        -- doesn't respect transparency, generalizes (1 : Ordinal) too
        -- have hc : 1 < t := ht.one_lt
        -- generalize (1 : Nimber) = c at hc ⊢
        -- obtain ⟨c, hc⟩ : ∃ c : Nimber, c = 1 := ⟨1, rfl⟩
        -- rw [← hc]
        -- replace hc : c < t := hc ▸ ht.one_lt
        induction vb with
        | zero =>
          rw [pow_zero, mul_one, of.lt_iff_lt, opow_lt_opow_iff_right (by simpa using ht.one_lt)]
          exact hu
        | succ vb ih =>
          rw [pow_succ', ← mul_assoc]
          sorry
      · sorry
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
