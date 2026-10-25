-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceNative
import Submission.Obl.k4_finite_affine_parent_sources.MajorFrame

/-!
# `EH1` and `EH4` of a source stage

With the parent frame rotated to its major axis (`MajorFrame.frame`), the parent chart's tube
gives `EH1` of `SourceData.stage` through `eh1_model` (slack `3 κ`), provided the prepared set
lies in the parent's counted incidences and carries the model loss. Nesting `EH4` follows from
actual ancestry and the common parent-time normalization.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

theorem t₀_add_q₀ : D.t₀ + D.q₀ = ((p.bin D.parent : ℝ) + 1) / (2 : ℝ) ^ p.T D.i₀ := by
  simp only [t₀, q₀]; field_simp

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The parent chart's tube in the rotated parent frame, with slack `3 κ`. -/
theorem parent_tube (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) :
    ∀ l ∈ p.assigned D.parent, ∀ t ∈ Icc D.t₀ (D.t₀ + D.q₀),
      ‖Matrix.toEuclideanLin D.D₀⁻¹ (gy l t - p.center D.parent - t • p.velocity D.parent)‖ ≤
          3 * p.κ ∧
        |eval (gx l t) (p.test D.parent)| ≤ 3 * p.κ * δ Nk (p.r D.i₀) ∧
        |eval (gx l t) (pderiv 3 (p.test D.parent))| ≤ 3 * p.κ * B D.w₀ ∧
        |eval (gx l t) (pderiv 3 (pderiv 3 (p.test D.parent)))| ≤
          3 * p.κ * B D.w₀ ^ 2 / δ Nk (p.r D.i₀) := by
  intro l hl t ht
  have hc := hp.chart D.parent
  have hκ := hp.one_le_slack
  rw [D.t₀_add_q₀] at ht
  obtain ⟨-, -, htube⟩ := hc.2.2.2.2.2.2.2.2.2.1 l hl
  obtain ⟨h1, h2, h3, h4⟩ := htube t ht
  have hδ : 0 < δ Nk (p.r D.i₀) := by
    show 0 < (2 : ℝ) ^ (-(⌊p.r D.i₀ * Real.log Nk / Real.log 2⌋ : ℤ))
    positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD₀]
    exact MajorFrame.fit hc.1 _ p.κ h1
  · calc _ ≤ p.κ * δ Nk (p.r D.i₀) := h2
      _ ≤ 3 * p.κ * δ Nk (p.r D.i₀) := by nlinarith
  · have hB : 0 ≤ B D.w₀ := (abs_nonneg _).trans h3 |>.trans' (le_refl _) |> fun _ => by
      by_contra hneg; push Not at hneg
      have : p.κ * B (p.world D.parent) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
      linarith [abs_nonneg (eval (gx l t) (pderiv 3 (p.test D.parent))), h3]
    calc _ ≤ p.κ * B D.w₀ := h3
      _ ≤ 3 * p.κ * B D.w₀ := by nlinarith
  · calc _ ≤ p.κ * B D.w₀ ^ 2 / δ Nk (p.r D.i₀) := h4
      _ ≤ 3 * p.κ * B D.w₀ ^ 2 / δ Nk (p.r D.i₀) := by
        apply div_le_div_of_nonneg_right _ hδ.le
        nlinarith [sq_nonneg (B D.w₀)]

/-- **`EH1` of the source stage.** -/
theorem eh1_stage (unit : ℝ) (hνw : IsProbabilityMeasure (ν D.w₀)) (hBw : 0 < B D.w₀)
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) (hπ : IsProbabilityMeasure D.π)
    (hK : 18 * p.κ ≤ D.K) (hSm : MeasurableSet D.S)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hScount : D.S ⊆ p.counted D.parent) (hA₀ : ν D.w₀ (p.assigned D.parent) ≠ 0)
    (hρmass : ENNReal.ofReal (D.K)⁻¹ ≤ (D.stage Nk L unit ν B).ρ Set.univ) :
    EH1 (D.stage Nk L unit ν B) := by
  have hc := hp.chart D.parent
  have hκ := hp.one_le_slack
  have hδ : 0 < δ Nk (p.r D.i₀) := by
    show 0 < (2 : ℝ) ^ (-(⌊p.r D.i₀ * Real.log Nk / Real.log 2⌋ : ℤ))
    positivity
  have hD : IsUnit (D.frame Nk B).F.D.det := by
    rw [D.frame_F]
    show IsUnit D.D₀.det
    rw [hD₀]
    exact isUnit_iff_ne_zero.mpr (MajorFrame.det_ne_zero hc.1)
  have hSsub : D.S ⊆ p.assigned D.parent ×ˢ
      Icc (D.frame Nk B).F.t₀ ((D.frame Nk B).F.t₀ + (D.frame Nk B).F.q) := by
    intro z hz
    exact ⟨(hSo hz).1, Ioo_subset_Icc_self (hSo hz).2⟩
  refine eh1_model (D.stage Nk L unit ν B) (ν D.w₀) (p.assigned D.parent)
    hc.2.2.2.2.2.2.1 hA₀ (D.frame Nk B) D.q₀_pos hD (B D.w₀) (δ Nk (p.r D.i₀)) hBw hδ rfl
    (p.test D.parent) hc.2.2.2.2.1 (3 * p.κ) (by linarith) D.S Set.univ hSm hSsub rfl rfl
    (by simp only [stage, Set.inter_univ]; rfl) rfl rfl hπ
    (by show 6 * (3 * p.κ) ≤ D.K; linarith) hρmass ?_ ?_
  · intro l hl t ht
    exact D.parent_tube hp hD₀ l hl t ht
  · intro z hz
    have hzc := hScount hz
    have h := (hp.counted_support D.parent z hzc).2.2.2
    calc B D.w₀ / (3 * p.κ) ≤ B D.w₀ / p.κ := by
          apply div_le_div_of_nonneg_left hBw.le (by linarith) (by linarith)
      _ ≤ _ := h

/-- **`EH4` of the source stage**, for every range. -/
theorem eh4_stage (unit : ℝ) (hmono : Monotone D.depth) (hi₀ : ∀ s, D.i₀ ≤ D.depth s)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀)) (U R : ℝ) :
    EH4 U (D.stage Nk L unit ν B) R :=
  withActiveLabels_eh4 hp (D.stage Nk L unit ν B) D.Hm D.depth hmono D.relT D.relBin D.c
    (fun s i => (D.frame Nk B).normTest (δ Nk (p.r D.i₀)) (p.test (D.old s i)))
    D.t₀ D.q₀ D.q₀_pos.ne' (fun s i t => by
      have h := D.old_relBin_mem hp hSo s (hi₀ s) i t
      rw [D.old_level s i] at h
      exact h) U R

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
