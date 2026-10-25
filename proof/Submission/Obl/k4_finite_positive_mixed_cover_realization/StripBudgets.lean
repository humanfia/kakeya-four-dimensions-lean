/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/StripBudgets.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripGeometry

/-!
Actual path budgets for the strip constructor. The geometric slack below is
polynomial only in the supplied path slack; a candidate's power slack has
already been absorbed into the strictly larger rounding width.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open Submission.Lib.K4VelocityStrips
open Submission.Lib.K4XInterface
open Submission.Obl.k4_native_finite_terminal_atlas_lift
open scoped RealInnerProductSpace

theorem strip_bias_le {n v : Plane} {β ε V : ℝ}
    (hn : ‖n‖ = 1) (hv : ‖v‖ ≤ V) (hfit : |inner ℝ v n - β| ≤ ε) :
    |β| ≤ V + ε := by
  calc
    |β| = |inner ℝ v n - (inner ℝ v n - β)| := by congr 1; ring
    _ ≤ |inner ℝ v n| + |inner ℝ v n - β| := abs_sub _ _
    _ ≤ V + ε := add_le_add
      ((abs_real_inner_le_norm v n).trans (by simpa only [hn, mul_one] using hv)) hfit

/-- The binned midpoint center and an actual representative's bias have
only incoming path slack. -/
theorem strip_center_velocity_le {κ ρ s β : ℝ} {n : Plane}
    (hκ : 1 ≤ κ) (hρ : ρ ≤ 1) (hn : ‖n‖ = 1)
    (hs : |s| ≤ κ + ρ) (hβ : |β| ≤ 3 * κ) :
    ‖stripCenter n s β‖ + ‖stripVelocity n β‖ ≤ 7 * κ := by
  simp only [stripCenter, stripVelocity, norm_smul, Real.norm_eq_abs, hn, mul_one]
  have htri : |s - β / 2| ≤ |s| + |β| / 2 := by
    simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using abs_sub s (β / 2)
  linarith

/-- The local narrowed frame has a path-sized entry sum. -/
theorem strip_frame_size_le {κ ρ : ℝ} {e n : Plane}
    (hκ : 1 ≤ κ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) :
    frameSize (stripLocalFrame κ (4 + 6 * κ) ρ e n) ≤ 24 * κ := by
  have hs := Submission.Lib.K4FinitePlankAtlases.plankFrame_entries
    (show 0 < κ by linarith) (show 0 < (1 + (4 + 6 * κ)) * ρ by positivity) he hn
  change frameSize (stripLocalFrame κ (4 + 6 * κ) ρ e n) ≤
    2 * (κ + (1 + (4 + 6 * κ)) * ρ) at hs
  have hline : (1 + (4 + 6 * κ)) * ρ ≤ 11 * κ := by nlinarith
  exact hs.trans (by linarith)

/-- The inverse-frame cost depends polynomially on the reciprocal new width;
it enlarges the fixed format, while the chart slack stays path-sized. -/
theorem strip_frame_budget_le {κ ρ : ℝ} {e n : Plane}
    (hκ : 1 ≤ κ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|stripLocalFrame κ (4 + 6 * κ) ρ e n i j| +
        |(stripLocalFrame κ (4 + 6 * κ) ρ e n)⁻¹ i j|)) ≤ 28 * κ / ρ := by
  have hκ₀ : 0 < κ := by linarith
  have hs := stripLocalFrame_entry_budget hκ₀ (show 0 ≤ 4 + 6 * κ by linarith)
    hρ he hn hen
  have hline : (1 + (4 + 6 * κ)) * ρ ≤ 11 * κ := by nlinarith
  have hki : κ⁻¹ ≤ 1 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hκ
  have hdi : ((1 + (4 + 6 * κ)) * ρ)⁻¹ ≤ ρ⁻¹ :=
    inv_anti₀ hρ (by nlinarith)
  have hkρ : κ ≤ κ / ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
  have h1ρ : 1 ≤ κ / ρ := le_trans hκ hkρ
  have hiρ : ρ⁻¹ ≤ κ / ρ := by
    rw [div_eq_mul_inv]
    simpa using mul_le_mul_of_nonneg_right hκ (inv_nonneg.mpr hρ.le)
  apply hs.trans
  rw [mul_div_assoc]
  linarith

/-- Composition through the old frame preserves a path-sized spatial-entry
budget on the unchanged old time block. -/
theorem composed_strip_size_le {κ ρ : ℝ} {T : ℕ} {Q : Frame} {e n : Plane}
    (hκ : 1 ≤ κ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (hQ : frameSize Q ≤ κ / (2 : ℝ) ^ T) :
    frameSize (Q * stripLocalFrame κ (4 + 6 * κ) ρ e n) ≤
      (24 * κ ^ 2) / (2 : ℝ) ^ T := by
  calc
    _ ≤ frameSize Q * frameSize (stripLocalFrame κ (4 + 6 * κ) ρ e n) := frameSize_mul _ _
    _ ≤ (κ / (2 : ℝ) ^ T) * (24 * κ) :=
      mul_le_mul hQ (strip_frame_size_le hκ hρ hρ' he hn)
        (frameSize_nonneg _) (by positivity)
    _ = _ := by ring

/-- The composed frame and its inverse have a fixed polynomial format cost. -/
theorem frame_product_budget_le (Q R : Frame) :
    (∑ i : Fin 2, ∑ j : Fin 2, (|(Q * R) i j| + |(Q * R)⁻¹ i j|)) ≤
      (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) *
        (∑ i : Fin 2, ∑ j : Fin 2, (|R i j| + |R⁻¹ i j|)) := by
  simp only [Finset.sum_add_distrib]
  change frameSize (Q * R) + frameSize (Q * R)⁻¹ ≤
    (frameSize Q + frameSize Q⁻¹) * (frameSize R + frameSize R⁻¹)
  rw [Matrix.mul_inv_rev]
  have h₁ := frameSize_mul Q R
  have h₂ := frameSize_mul R⁻¹ Q⁻¹
  nlinarith [mul_nonneg (frameSize_nonneg Q) (frameSize_nonneg R⁻¹),
    mul_nonneg (frameSize_nonneg Q⁻¹) (frameSize_nonneg R)]

/-- A scalar constant in the fixed format is absorbed by five powers of the
original sample scale. -/
private theorem absorb_frame_constant {N : ℝ} (hN : 2 ≤ N) (k : ℕ) :
    28 * N ^ k ≤ N ^ (k + 5) := by
  have hconst : 28 ≤ N ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 5
    norm_num at hp
    linarith
  calc
    _ ≤ N ^ 5 * N ^ k := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- The strip constructor with every numerical budget discharged. Its
geometric slack is `32 κ²`; the reciprocal narrowing width enlarges only
the fixed polynomial format exponent. -/
theorem gchart_strip_path_slack
    {Nk κ j r₀ Bv ρ s β : ℝ} {M Mr D D' T : ℕ}
    {Ev : Set (Line × ℝ)} {c u e n : Plane} {Q : Frame}
    {R : MvPolynomial (Fin 4) ℝ} {A A' : Set Line} {F F' : Set (Line × ℝ)} {ex ex' : Prop}
    (h : gchart Nk M D κ T j r₀ Bv Ev c u Q R A F ex)
    (hNk : 2 ≤ Nk) (hκ : 1 ≤ κ) (hκN : κ ≤ Nk) (hD : D ≤ D') (hB : 0 ≤ Bv)
    (hj : 0 ≤ j) (hj' : j ≤ (2 : ℝ) ^ T) (hT : (2 : ℝ) ^ T ≤ Nk ^ M)
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1) (hρinv : ρ⁻¹ ≤ Nk ^ Mr)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (hs : |s| ≤ κ + ρ) (hβ : |β| ≤ 3 * κ)
    (hvel : ∀ l ∈ A',
      |inner ℝ (((2 : ℝ) ^ T)⁻¹ • Matrix.toEuclideanLin Q⁻¹ (gv l - u)) n - β| ≤
        (4 + 6 * κ) * ρ)
    (hmid : ∀ l ∈ A', |inner ℝ (Matrix.toEuclideanLin Q⁻¹
      (gy l (j / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ / 2) - c -
        (j / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ / 2) • u)) n - s| ≤ ρ)
    (hA : A' ⊆ A) (hF : F' ⊆ F) (hFA : ∀ p ∈ F', p.1 ∈ A')
    (hmA : MeasurableSet A') (hmF : MeasurableSet F')
    (hfmt : ∀ i, gfmt 6 (Nk ^ (2 * M + Mr + 8)) D' {x | (i, x) ∈ A'} ∧
      gfmt 7 (Nk ^ (2 * M + Mr + 8)) D'
        {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F'})
    (hex : ex') :
    gchart Nk (2 * M + Mr + 8) D' (32 * κ ^ 2) T j r₀ Bv Ev
      (compositeCenter (j / (2 : ℝ) ^ T) (((2 : ℝ) ^ T)⁻¹)
        c (stripCenter n s β) u (stripVelocity n β) Q)
      (compositeVelocity (((2 : ℝ) ^ T)⁻¹) u (stripVelocity n β) Q)
      (Q * stripLocalFrame κ (4 + 6 * κ) ρ e n) R A' F' ex' := by
  have hN1 : 1 ≤ Nk := by linarith
  have hN0 : 0 ≤ Nk := by linarith
  have hκ₀ : 0 < κ := by linarith
  have hframe := h.2.2.1
  have hseparate : frameSize Q + frameSize Q⁻¹ ≤ Nk ^ M := by
    simpa only [frameSize, Finset.sum_add_distrib] using hframe
  have hQ : frameSize Q ≤ Nk ^ M := by linarith [frameSize_nonneg Q⁻¹]
  have hQsize : frameSize Q ≤ κ / (2 : ℝ) ^ T := h.2.2.2.1
  have hH : 1 ≤ Nk ^ M := one_le_pow₀ hN1
  have ht₀ : |j / (2 : ℝ) ^ T| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hj (by positivity))]
    exact (div_le_one (by positivity)).mpr hj'
  have hq : |((((2 : ℝ) ^ T)⁻¹)⁻¹)| ≤ Nk ^ M := by simpa using hT
  have hcenter := composite_center_velocity_bound hH (show 1 ≤ 7 * κ by linarith)
    ht₀ hq h.2.1 (strip_center_velocity_le hκ hρ' hn hs hβ) hQ
  have hcenter' :
      ‖compositeCenter (j / (2 : ℝ) ^ T) (((2 : ℝ) ^ T)⁻¹)
        c (stripCenter n s β) u (stripVelocity n β) Q‖ +
      ‖compositeVelocity (((2 : ℝ) ^ T)⁻¹) u (stripVelocity n β) Q‖ ≤
        Nk ^ (2 * M + Mr + 8) := by
    apply hcenter.trans
    calc
      _ = 28 * Nk ^ (2 * M) * κ := by rw [← pow_mul, Nat.mul_comm M 2]; ring
      _ ≤ 28 * Nk ^ (2 * M) * Nk :=
        mul_le_mul_of_nonneg_left hκN (by positivity)
      _ = 28 * Nk ^ (2 * M + 1) := by rw [pow_add, pow_one]; ring
      _ ≤ Nk ^ (2 * M + 1 + 5) := absorb_frame_constant hNk _
      _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
  have hbudget : (∑ i : Fin 2, ∑ j : Fin 2,
      (|(Q * stripLocalFrame κ (4 + 6 * κ) ρ e n) i j| +
        |(Q * stripLocalFrame κ (4 + 6 * κ) ρ e n)⁻¹ i j|)) ≤
        Nk ^ (2 * M + Mr + 8) := by
    apply (frame_product_budget_le Q _).trans
    calc
      _ ≤ Nk ^ M * (28 * κ / ρ) :=
        mul_le_mul hframe (strip_frame_budget_le hκ hρ hρ' he hn hen)
          (by positivity) (by positivity)
      _ ≤ Nk ^ M * (28 * (Nk * Nk ^ Mr)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_div_assoc, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hκN hρinv (by positivity) hN0) (by norm_num)
      _ = 28 * Nk ^ (M + Mr + 1) := by rw [pow_add, pow_add, pow_one]; ring
      _ ≤ Nk ^ (M + Mr + 1 + 5) := absorb_frame_constant hNk _
      _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
  have hsize : frameSize (Q * stripLocalFrame κ (4 + 6 * κ) ρ e n) ≤
      (32 * κ ^ 2) / (2 : ℝ) ^ T := by
    apply (composed_strip_size_le hκ hρ hρ' he hn hQsize).trans
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg κ]) (by positivity)
  exact gchart_composed_strip h hN1 (by omega) hD hκ₀ (by nlinarith) (by nlinarith) hB
    (by linarith) hρ he hn hen hvel hmid hcenter' hbudget hsize hA hF hFA hmA hmF hfmt hex

end Submission.Obl.k4_finite_positive_mixed_cover_realization
