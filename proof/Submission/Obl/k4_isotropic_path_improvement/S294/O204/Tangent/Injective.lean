-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Injective, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit c3fccb87c, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/Injective.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- Invertible tangent frames: injectivity and measurable embedding of the line/event maps
-- (x1078, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Frame

/-!
# Tangent images of original sets

For a frame with `q ≠ 0`, `det D ≠ 0` and hidden scale `sc ≠ 0`, the tangent line and event
maps are injective and continuous, hence measurable embeddings. Images of measurable sets are
then measurable tangent sets whose pull-backs are exactly the original sets: this supplies the
assignment and residual hypotheses `hAt_in`, `hAt_back`, `hH_back` of `directAt_return` for the
image sets `tanLine '' Ab` and `tanEvent '' H₀`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split

noncomputable section

lemma normCoeff_injective (F : Frame) (hq : F.q ≠ 0) (hD : F.D.det ≠ 0) :
    Function.Injective F.normCoeff := by
  intro l l' h
  have hDi : (F.D⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hD
  have hmv : ∀ v w : Fin 2 → ℝ, (F.D⁻¹).mulVec v = (F.D⁻¹).mulVec w → v = w := by
    intro v w hvw
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hDi))
    exact hinj hvw
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp only [Frame.normCoeff, Matrix.cons_val, Fin.isValue] at h0 h1 h2 h3 h4 h5
  -- velocities
  have hb : (![l 3 - F.u 0, l 4 - F.u 1] : Fin 2 → ℝ) = ![l' 3 - F.u 0, l' 4 - F.u 1] := by
    apply hmv
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have := mul_left_cancel₀ hq h3; linarith
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have := mul_left_cancel₀ hq h4; linarith
  have hv3 : l 3 = l' 3 := by have := congrFun hb 0; simp at this; linarith
  have hv4 : l 4 = l' 4 := by have := congrFun hb 1; simp at this; linarith
  have hv5 : l 5 = l' 5 := mul_left_cancel₀ hq h5
  -- positions
  have ha : (![l 0 + F.t₀ * l 3 - F.c 0 - F.t₀ * F.u 0, l 1 + F.t₀ * l 4 - F.c 1 - F.t₀ * F.u 1]
      : Fin 2 → ℝ) =
      ![l' 0 + F.t₀ * l' 3 - F.c 0 - F.t₀ * F.u 0, l' 1 + F.t₀ * l' 4 - F.c 1 - F.t₀ * F.u 1] := by
    apply hmv
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linarith
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linarith
  have hp0 : l 0 = l' 0 := by have := congrFun ha 0; simp at this; rw [hv3] at this; linarith
  have hp1 : l 1 = l' 1 := by have := congrFun ha 1; simp at this; rw [hv4] at this; linarith
  have hp2 : l 2 = l' 2 := by rw [hv5] at h2; linarith
  ext i
  fin_cases i <;> simp [hp0, hp1, hp2, hv3, hv4, hv5]

lemma residualCoeff_one_injective (a : Fin 4 → ℝ) : Function.Injective (residualCoeff a 1) := by
  intro b b' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp only [residualCoeff, Matrix.cons_val, Fin.isValue, div_one] at h0 h1 h2 h3 h4 h5
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · simp; rw [h0, h1] at h2; linarith
  · exact h3
  · exact h4
  · simp; rw [h3, h4] at h5; linarith

lemma eb_injective (Φ : PFrame) (hq : Φ.F.q ≠ 0) (hD : Φ.F.D.det ≠ 0) (hsc : Φ.sc ≠ 0) :
    Function.Injective (fun c : Fin 6 → ℝ => Φ.eb (0, c)) := by
  intro c c' h
  apply normCoeff_injective Φ.F hq hD
  have hh := fun i => congrFun h i
  ext i
  fin_cases i
  · simpa [PFrame.eb] using hh 0
  · simpa [PFrame.eb] using hh 1
  · simpa [PFrame.eb, hsc] using hh 2
  · simpa [PFrame.eb] using hh 3
  · simpa [PFrame.eb] using hh 4
  · simpa [PFrame.eb, hsc] using hh 5

lemma tanLine_injective (Φ : PFrame) (a : Fin 4 → ℝ) (hq : Φ.F.q ≠ 0) (hD : Φ.F.D.det ≠ 0)
    (hsc : Φ.sc ≠ 0) : Function.Injective (tanLine Φ a) := by
  rintro ⟨i, c⟩ ⟨i', c'⟩ h
  simp only [tanLine, Prod.mk.injEq] at h
  obtain ⟨hi, hc⟩ := h
  refine Prod.ext hi (eb_injective Φ hq hD hsc ?_)
  have := residualCoeff_one_injective a hc
  simpa [PFrame.eb] using this

lemma tanEvent_injective (Φ : PFrame) (a : Fin 4 → ℝ) (hq : Φ.F.q ≠ 0) (hD : Φ.F.D.det ≠ 0)
    (hsc : Φ.sc ≠ 0) : Function.Injective (tanEvent Φ a) := by
  rintro ⟨l, t⟩ ⟨l', t'⟩ h
  simp only [tanEvent, Prod.mk.injEq] at h
  obtain ⟨hl, ht⟩ := h
  refine Prod.ext (tanLine_injective Φ a hq hD hsc hl) ?_
  simp only
  have := (div_left_inj' hq).mp ht
  linarith

lemma continuous_tanLine (Φ : PFrame) (a : Fin 4 → ℝ) : Continuous (tanLine Φ a) := by
  unfold tanLine hiddenShear residualCoeff PFrame.eb Frame.normCoeff
  refine continuous_fst.prodMk ?_
  refine continuous_pi (fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

lemma continuous_tanEvent (Φ : PFrame) (a : Fin 4 → ℝ) : Continuous (tanEvent Φ a) :=
  ((continuous_tanLine Φ a).comp continuous_fst).prodMk
    ((continuous_snd.sub continuous_const).div_const _)

lemma measurableEmbedding_tanEvent (Φ : PFrame) (a : Fin 4 → ℝ) (hq : Φ.F.q ≠ 0)
    (hD : Φ.F.D.det ≠ 0) (hsc : Φ.sc ≠ 0) : MeasurableEmbedding (tanEvent Φ a) :=
  (continuous_tanEvent Φ a).measurableEmbedding (tanEvent_injective Φ a hq hD hsc)

lemma measurableEmbedding_tanLine (Φ : PFrame) (a : Fin 4 → ℝ) (hq : Φ.F.q ≠ 0)
    (hD : Φ.F.D.det ≠ 0) (hsc : Φ.sc ≠ 0) : MeasurableEmbedding (tanLine Φ a) :=
  (continuous_tanLine Φ a).measurableEmbedding (tanLine_injective Φ a hq hD hsc)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
