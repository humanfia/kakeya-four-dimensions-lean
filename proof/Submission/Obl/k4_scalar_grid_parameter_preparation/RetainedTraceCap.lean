/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/RetainedTraceCap.lean -/
import Submission.Lib.K4Homogenization.RetainedDuration
import Submission.Obl.k4_scalar_grid_parameter_preparation.TraceRectangle
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarMotion

/-! Fixed-time original-prior caps from retained duration and original joint ceilings. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

/-- Retaining at least `ε*δ` of original incidence duration in the fine time
window converts the original rectangular joint caps into a fixed-time prior
cap. The fine time scale cancels, including when the two spatial widths differ. -/
theorem retained_trace_prior_cap {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (G : α × ℝ → ℝ≥0∞) (hG : Measurable G)
    (Y X : α → ℝ → ℝ) (V : α → ℝ)
    (C : Set α) (hC : MeasurableSet C) (I : Set ℝ) (hIm : MeasurableSet I)
    (P : Set ℝ) (p : ℝ≥0∞) (t₀ τ ξ ζ δ A U B ε : ℝ) (q a : ℤ)
    (hδ : 0 < δ) (hξ : δ ≤ ξ) (hζ : 0 < ζ) (hA : 1 ≤ A)
    (hU : 0 ≤ U) (hB : 0 ≤ B) (hε : 0 < ε)
    (hI : I ⊆ Set.Icc τ (τ + δ))
    (hY : ∀ l ∈ C, Y l t₀ ∈ scalarVelocityBin ξ q)
    (hX : ∀ l ∈ C, X l t₀ ∈ scalarVelocityBin ζ a)
    (hV : ∀ l ∈ C, V l ∈ P)
    (hYmove : ∀ l ∈ C, ∀ t ∈ I, dist (Y l t) (Y l t₀) ≤ A * δ)
    (hXmove : ∀ l ∈ C, ∀ t ∈ I, dist (X l t) (X l t₀) ≤ ζ)
    (hcap : ∀ i j b : ℤ,
      (ν.prod volume).withDensity G
        {ω | (⌊ω.2 / δ⌋ : ℤ) = i ∧ (⌊Y ω.1 ω.2 / δ⌋ : ℤ) = j ∧
          (⌊X ω.1 ω.2 / ζ⌋ : ℤ) = b ∧ V ω.1 ∈ P} ≤
            ENNReal.ofReal (U * δ ^ 2 * B) * p) :
    ν (Submission.Lib.K4Homogenization.durationRetained volume G I
        (ENNReal.ofReal (ε * δ)) ∩ C) ≤
      ENNReal.ofReal (256 * A * U * ξ * B / ε) * p := by
  have hrect := propagated_rectangle_mass_le ((ν.prod volume).withDensity G)
    Y X V C I P p t₀ τ ξ ζ δ A U B q a hδ hξ hζ hA hU hB hI hY hX hV hYmove hXmove hcap
  have hretain := Submission.Lib.K4Homogenization.retained_duration_prior_cap_div
    ν volume hG hIm (ENNReal.ofReal (ε * δ))
    (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top hC
    (C ×ˢ I) (fun l hl t ht => ⟨hl, ht⟩)
  have hevent : (C ×ˢ I) ∩ (Set.univ ×ˢ I) = C ×ˢ I := by
    ext ω
    simp
  rw [hevent] at hretain
  apply hretain.trans
  calc
    (ν.prod volume).withDensity G (C ×ˢ I) / ENNReal.ofReal (ε * δ) ≤
        (ENNReal.ofReal (256 * A * U * ξ * δ * B) * p) / ENNReal.ofReal (ε * δ) :=
      by
        simpa only [div_eq_mul_inv] using
          (mul_le_mul hrect (le_refl ((ENNReal.ofReal (ε * δ))⁻¹)) bot_le bot_le)
    _ = ENNReal.ofReal ((256 * A * U * ξ * δ * B) / (ε * δ)) * p := by
      rw [ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [div_eq_mul_inv]
      ring
    _ = ENNReal.ofReal (256 * A * U * ξ * B / ε) * p := by
      congr 2
      field_simp

/-- Concrete version for the scalar quadratic trajectories of the frozen
problem. A sufficiently fine time mesh supplies both propagation hypotheses. -/
theorem retained_scalar_trace_prior_cap {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (G : α × ℝ → ℝ≥0∞) (hG : Measurable G)
    (a : α → Fin 5 → ℝ) (C : Set α) (hC : MeasurableSet C)
    (I : Set ℝ) (hIm : MeasurableSet I) (P : Set ℝ) (p : ℝ≥0∞)
    (t₀ τ ξ ζ δ H U B ε : ℝ) (qY qX : ℤ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ : δ ≤ ξ) (hζ : 0 < ζ) (hH : 1 ≤ H)
    (hU : 0 ≤ U) (hB : 0 ≤ B) (hε : 0 < ε) (hsmall : 5 * H * δ ≤ ζ)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) (htI : t₀ ∈ Set.Icc τ (τ + δ))
    (hI : I ⊆ Set.Icc τ (τ + δ)) (ha : ∀ l ∈ C, ∀ e, |a l e| ≤ H)
    (hY : ∀ l ∈ C, a l 0 + t₀ * a l 1 ∈ scalarVelocityBin ξ qY)
    (hX : ∀ l ∈ C, a l 2 + t₀ * a l 3 + t₀ ^ 2 * a l 4 ∈ scalarVelocityBin ζ qX)
    (hV : ∀ l ∈ C, a l 1 ∈ P)
    (hcap : ∀ i j b : ℤ,
      (ν.prod volume).withDensity G
        {ω | (⌊ω.2 / δ⌋ : ℤ) = i ∧ (⌊(a ω.1 0 + ω.2 * a ω.1 1) / δ⌋ : ℤ) = j ∧
          (⌊(a ω.1 2 + ω.2 * a ω.1 3 + ω.2 ^ 2 * a ω.1 4) / ζ⌋ : ℤ) = b ∧ a ω.1 1 ∈ P} ≤
            ENNReal.ofReal (U * δ ^ 2 * B) * p) :
    ν (Submission.Lib.K4Homogenization.durationRetained volume G I
        (ENNReal.ofReal (ε * δ)) ∩ C) ≤
      ENNReal.ofReal (256 * H * U * ξ * B / ε) * p := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have ht₀abs : |t₀| ≤ 1 := by rw [abs_of_nonneg ht₀.1]; exact ht₀.2
  have hdist (t : ℝ) (ht : t ∈ I) : dist t t₀ ≤ δ := by
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [(hI ht).1, htI.2], by linarith [(hI ht).2, htI.1]⟩
  have htab (t : ℝ) (ht : t ∈ I) : |t| ≤ 2 := by
    calc
      |t| ≤ |t - t₀| + |t₀| := by simpa only [sub_add_cancel] using abs_add_le (t - t₀) t₀
      _ ≤ δ + 1 := add_le_add (hdist t ht) ht₀abs
      _ ≤ 2 := by linarith
  apply retained_trace_prior_cap ν G hG
    (fun l t => a l 0 + t * a l 1)
    (fun l t => a l 2 + t * a l 3 + t ^ 2 * a l 4) (fun l => a l 1)
    C hC I hIm P p t₀ τ ξ ζ δ H U B ε qY qX hδ hξ hζ hH hU hB hε hI hY hX hV
    ?_ ?_ hcap
  · intro l hl t ht
    have hm := scalar_quadratic_motion_le (a l) H t₀ t hH0 (ha l hl)
      (ht₀abs.trans (by norm_num)) (htab t ht)
    exact hm.1.trans (mul_le_mul_of_nonneg_left (hdist t ht) hH0)
  · intro l hl t ht
    have hm := scalar_quadratic_motion_le (a l) H t₀ t hH0 (ha l hl)
      (ht₀abs.trans (by norm_num)) (htab t ht)
    exact (hm.2.trans (mul_le_mul_of_nonneg_left (hdist t ht) (by positivity))).trans hsmall

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
