import Mathlib
import ChallengeDeps
import Submission.Obl.k4_mk_visibility.Variation
import Submission.Obl.k4_polynomial_variation_tube
import Submission.Obl.k4_prescribed_polynomial_visibility
import Submission.Obl.k4_mk_visibility.Normalization
set_option linter.unusedVariables false

/-!
# `Submission.k4_mk_visibility`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_mk_visibility`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_mk_visibility/`
belong to this obligation.
-/

open Submission.Obl.k4_mk_visibility in
theorem Submission.k4_mk_visibility : ∀ n : ℕ, 3 ≤ n → n ≤ 4 → ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (z : Fin m → Fin n → ℤ), Function.Injective z → ∀ M : Fin m → ℝ, (∀ q : Fin m, 0 ≤ M q) → (∑ q : Fin m, M q) = 1 → ∃ A : Fin m → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)), (∀ q : Fin m, M q ≤ |LinearMap.det (A q)|) ∧ ∀ a e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 → (∑ q : Fin m, (Metric.thickening (3 : ℝ) (Set.range fun t : ℝ => a + t • e)).indicator (fun _ => (1 : ℝ)) (WithLp.toLp 2 (fun j : Fin n => (z q j : ℝ))) * ‖A q e‖) ≤ K := by
  classical
  intro n hn hn4
  obtain ⟨C, hC, _hintegrable, harea⟩ :=
    Submission.k4_polynomial_variation_tube n (by omega)
  obtain ⟨L, hL, hvis⟩ := Submission.k4_prescribed_polynomial_visibility n hn hn4
  let J : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  have hJ : 0 < J := mul_pos (by exact_mod_cast (show 0 < n by omega)) (by positivity)
  refine ⟨J * (1 + C * L), by positivity, ?_⟩
  intro m z hz M hM hmass
  obtain ⟨D, hD, r, p, w, V, hcontinuous, hw, hweight, hdegree, hV, hdom, hvolume⟩ :=
    hvis m z hz M hM hmass
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity : 0 < (m : ℝ) + 1) hD
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hB : ∀ q : Fin m,
      ∃ B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
        D ^ n * M q ≤ |LinearMap.det B| ∧
          ∀ v : EuclideanSpace ℝ (Fin n), ‖B v‖ ≤ J * V q v := by
    intro q
    by_cases hpos : 0 < M q
    · have ht : 0 < D ^ n * M q := mul_pos (pow_pos hDpos n) hpos
      have hvol : ENNReal.ofReal (D ^ n * M q) *
          MeasureTheory.volume {v | V q v ≤ 1} ≤ 1 := by
        calc
          ENNReal.ofReal (D ^ n * M q) * MeasureTheory.volume {v | V q v ≤ 1} ≤
              ENNReal.ofReal (D ^ n * M q) * ENNReal.ofReal ((D ^ n * M q)⁻¹) :=
            mul_le_mul_of_nonneg_left (hvolume q hpos) (by positivity)
          _ = 1 := by
            rw [← ENNReal.ofReal_mul ht.le, mul_inv_cancel₀ ht.ne', ENNReal.ofReal_one]
      exact exists_map_of_volume_bound (V q) (hcontinuous q)
        ⟨1, zero_lt_one, fun v => by simpa only [one_mul] using hdom q v⟩
        (D ^ n * M q) hvol
    · have hzero : M q = 0 := le_antisymm (le_of_not_gt hpos) (hM q)
      refine ⟨0, ?_, ?_⟩
      · simpa only [hzero, mul_zero] using
          abs_nonneg (LinearMap.det
            (0 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
      · intro v
        simpa only [LinearMap.zero_apply, norm_zero] using
          mul_nonneg hJ.le (apply_nonneg (V q) v)
  choose B hBdet hBnorm using hB
  refine ⟨fun q => D⁻¹ • B q, ?_, ?_⟩
  · intro q
    calc
      M q = (D⁻¹) ^ n * (D ^ n * M q) := by
        rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hDne), one_mul]
      _ ≤ (D⁻¹) ^ n * |LinearMap.det (B q)| :=
        mul_le_mul_of_nonneg_left (hBdet q) (by positivity)
      _ = |LinearMap.det (D⁻¹ • B q)| := by
        rw [LinearMap.det_smul, finrank_euclideanSpace_fin, abs_mul,
          abs_of_pos (pow_pos (inv_pos.mpr hDpos) n)]
  · intro a e he
    let c : Fin m → EuclideanSpace ℝ (Fin n) :=
      fun q => WithLp.toLp 2 (fun j : Fin n => (z q j : ℝ))
    let b : Fin m → ℝ := fun q =>
      (Metric.thickening (3 : ℝ) (Set.range fun t : ℝ => a + t • e)).indicator
        (fun _ => (1 : ℝ)) (c q)
    have hb : ∀ q, 0 ≤ b q := by
      intro q
      dsimp [b]
      apply Set.indicator_nonneg
      intro _ _
      exact zero_le_one
    have hb1 : ∀ q, b q ≤ 1 := by
      intro q
      simp only [b, Set.indicator_apply]
      split_ifs <;> norm_num
    have hV' : ∀ (q : Fin m) (v : EuclideanSpace ℝ (Fin n)),
        V q v = ‖v‖ + ∑ h : Fin r, w h * directionalVariation (p h) (c q) v := hV
    have hbudget : ∀ h : Fin r,
        (∑ q : Fin m, b q * directionalVariation (p h) (c q) e) ≤
          C * ((p h).totalDegree : ℝ) := fun h => harea m z hz (p h) a e he
    have hexpand : (∑ q : Fin m, b q * V q e) =
        (∑ q : Fin m, b q) +
          ∑ h : Fin r, w h * (∑ q : Fin m, b q * directionalVariation (p h) (c q) e) := by
      simp_rw [hV', he, mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hsum : (∑ q : Fin m, b q * V q e) ≤ (1 + C * L) * D := by
      calc
        (∑ q : Fin m, b q * V q e) =
            (∑ q : Fin m, b q) +
              ∑ h : Fin r, w h * (∑ q : Fin m, b q * directionalVariation (p h) (c q) e) :=
          hexpand
        _ ≤ (m : ℝ) + ∑ h : Fin r, w h * (C * ((p h).totalDegree : ℝ)) := by
          apply add_le_add
          · calc
              (∑ q : Fin m, b q) ≤ ∑ _q : Fin m, (1 : ℝ) :=
                Finset.sum_le_sum fun q _ => hb1 q
              _ = (m : ℝ) := by simp
          · exact Finset.sum_le_sum fun h _ =>
              mul_le_mul_of_nonneg_left (hbudget h) (hw h)
        _ ≤ (m : ℝ) + ∑ h : Fin r, w h * (C * (L * D)) := by
          apply add_le_add le_rfl
          exact Finset.sum_le_sum fun h _ =>
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hdegree h) hC.le) (hw h)
        _ = (m : ℝ) + C * L * D := by
          rw [← Finset.sum_mul, hweight]
          ring
        _ ≤ (1 + C * L) * D := by linarith
    have hAnorm : ∀ q : Fin m, ‖(D⁻¹ • B q) e‖ ≤ (D⁻¹ * J) * V q e := by
      intro q
      simpa only [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hDpos), mul_assoc] using
        mul_le_mul_of_nonneg_left (hBnorm q e) (inv_pos.mpr hDpos).le
    change (∑ q : Fin m, b q * ‖(D⁻¹ • B q) e‖) ≤ J * (1 + C * L)
    calc
      (∑ q : Fin m, b q * ‖(D⁻¹ • B q) e‖) ≤
          ∑ q : Fin m, b q * ((D⁻¹ * J) * V q e) :=
        Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hAnorm q) (hb q)
      _ = (D⁻¹ * J) * ∑ q : Fin m, b q * V q e := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ ≤ (D⁻¹ * J) * ((1 + C * L) * D) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = J * (1 + C * L) := by field_simp
