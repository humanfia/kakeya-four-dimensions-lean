-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/ModelEH1.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
-- Adapted from this LOT tree, o199, session x0700, commit 711b90f1.
-- Source: Submission/Obl/k4_finite_path_candidate_conversion/ModelEH1.lean.
import Submission.Obl.k4_finite_affine_candidate_return.ParentFrameInv
import Submission.Obl.k4_finite_affine_candidate_return.ModelMeasures

/-!
# The pointwise hypotheses `EH1` of the model at one parent

For a parent chart (frame `Φ`, assignment `A₀`, block `[t₀, t₀ + q]`, test `R₀` at thickness `δ₀`
and hidden derivative scale `B₀`, slack `κ`) and a prepared set `S` of its incidences, the model with
prior `nuE`, incidences `muE S`, residual `muE (S ∩ H)`, coefficients `Φ.eb` and native test
`Φ.normTest δ₀ R₀` satisfies `EH1` with any `K ≥ 6κ`, provided its residual carries `K⁻¹`.
Written by x0700 for o199.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory MvPolynomial Submission.Lib.K4XInterface
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

namespace PFrame

variable (Φ : PFrame)

theorem measurable_eb : Measurable Φ.eb := by
  unfold PFrame.eb Frame.normCoeff
  fun_prop

/-- The normalised planar offset is read off the model coefficients. -/
theorem toEuclideanLin_offset (hq : Φ.F.q ≠ 0) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    Matrix.toEuclideanLin Φ.F.D⁻¹ (gy l t - Φ.F.c - t • Φ.F.u) =
      WithLp.toLp 2 ![Φ.eb l 0 + (t - Φ.F.t₀) / Φ.F.q * Φ.eb l 3,
        Φ.eb l 1 + (t - Φ.F.t₀) / Φ.F.q * Φ.eb l 4] := by
  have h := Φ.F.planarPoint_normTraj hq l t
  have hgy : gy l t = planarPoint l t := rfl
  rw [hgy, ← h]
  rfl

/-- Model time `τ ∈ [0,1]` corresponds to original time `t₀ + q τ` in the block. -/
theorem tnorm_denorm (hq : Φ.F.q ≠ 0) (τ : ℝ) :
    (Φ.F.t₀ + Φ.F.q * τ - Φ.F.t₀) / Φ.F.q = τ := by
  field_simp; ring

theorem eval_normTest_at (hq : Φ.F.q ≠ 0) (hD : IsUnit Φ.F.D.det) (hsc : Φ.sc ≠ 0) (δ : ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (τ : ℝ) :
    eval (exS Φ.eb l τ) (Φ.normTest δ R) = δ⁻¹ * eval (gx l (Φ.F.t₀ + Φ.F.q * τ)) R := by
  have := Φ.eval_normTest hq hD hsc δ R l (Φ.F.t₀ + Φ.F.q * τ)
  rwa [Φ.tnorm_denorm hq] at this

end PFrame

/-- **`EH1` for the model at one parent.** -/
theorem eh1_model (st : EStage (ℕ × (Fin 6 → ℝ))) (ν₀ : Measure (ℕ × (Fin 6 → ℝ)))
    [IsFiniteMeasure ν₀] (A₀ : Set (ℕ × (Fin 6 → ℝ))) (hA₀ : MeasurableSet A₀)
    (h0 : ν₀ A₀ ≠ 0) (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    (B₀ δ₀ : ℝ) (hB : 0 < B₀) (hδ : 0 < δ₀) (hsc : Φ.sc = B₀ / δ₀)
    (R₀ : MvPolynomial (Fin 4) ℝ) (hR₀ : R₀.totalDegree ≤ 2) (κ : ℝ) (hκ : 1 ≤ κ)
    (S Hres : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hS : MeasurableSet S)
    (hSsub : S ⊆ A₀ ×ˢ Set.Icc Φ.F.t₀ (Φ.F.t₀ + Φ.F.q))
    (hν : st.ν = nuE ν₀ A₀) (hμ : st.μ = muE ν₀ A₀ Φ.F.t₀ Φ.F.q S)
    (hρ : st.ρ = muE ν₀ A₀ Φ.F.t₀ Φ.F.q (S ∩ Hres)) (hb : st.b = Φ.eb)
    (hP : st.P = Φ.normTest δ₀ R₀) (hπ : IsProbabilityMeasure st.π) (hK : 6 * κ ≤ st.K)
    (hρmass : ENNReal.ofReal (st.K)⁻¹ ≤ st.ρ Set.univ)
    (htube : ∀ l ∈ A₀, ∀ t ∈ Set.Icc Φ.F.t₀ (Φ.F.t₀ + Φ.F.q),
      ‖Matrix.toEuclideanLin Φ.F.D⁻¹ (gy l t - Φ.F.c - t • Φ.F.u)‖ ≤ κ ∧
      |eval (gx l t) R₀| ≤ κ * δ₀ ∧ |eval (gx l t) (pderiv 3 R₀)| ≤ κ * B₀ ∧
      |eval (gx l t) (pderiv 3 (pderiv 3 R₀))| ≤ κ * B₀ ^ 2 / δ₀)
    (hder : ∀ p ∈ S, B₀ / κ ≤ |eval (gx p.1 p.2) (pderiv 3 R₀)|) :
    EH1 st := by
  have hq0 : Φ.F.q ≠ 0 := hq.ne'
  have hsc0 : Φ.sc ≠ 0 := by rw [hsc]; positivity
  have hK1 : 1 ≤ st.K := by linarith
  have hKpos : 0 < st.K := by linarith
  have hT : ν₀ A₀ ≠ ⊤ := measure_ne_top ν₀ A₀
  refine ⟨?_, ?_, hπ, ?_, ?_, ?_, hρmass, ?_, ?_, ?_⟩
  · rw [hb]; exact Φ.measurable_eb
  · rw [hν]; exact nuE_isProb ν₀ A₀ h0 hT
  · rw [hμ, hν]
    refine (muE_le_prod ν₀ A₀ Φ.F.t₀ Φ.F.q hq hSsub).trans ?_
    calc (nuE ν₀ A₀).prod volume = (1 : ENNReal) • (nuE ν₀ A₀).prod volume := (one_smul _ _).symm
      _ ≤ ENNReal.ofReal st.K • (nuE ν₀ A₀).prod volume := by
          refine Measure.le_iff'.2 fun s => ?_
          simp only [Measure.smul_apply, smul_eq_mul]
          exact mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal hK1) _
  · rw [hρ, hμ]; exact muE_mono ν₀ A₀ _ _ Set.inter_subset_left
  · rw [hμ]; exact muE_compl_block ν₀ A₀ _ _ hq hSsub
  · rw [hP]; exact (Φ.totalDegree_normTest_le δ₀ R₀).trans hR₀
  · rw [hν, hb]
    refine ae_nuE_of_forall ν₀ hA₀ fun l hl => ?_
    have hb0 : Φ.F.t₀ ∈ Set.Icc Φ.F.t₀ (Φ.F.t₀ + Φ.F.q) := ⟨le_rfl, by linarith⟩
    have hb1 : Φ.F.t₀ + Φ.F.q ∈ Set.Icc Φ.F.t₀ (Φ.F.t₀ + Φ.F.q) := ⟨by linarith, le_rfl⟩
    have h0' := (htube l hl _ hb0).1
    have h1' := (htube l hl _ hb1).1
    rw [Φ.toEuclideanLin_offset hq0] at h0' h1'
    have e0 : (Φ.F.t₀ - Φ.F.t₀) / Φ.F.q = 0 := by simp
    have e1 : (Φ.F.t₀ + Φ.F.q - Φ.F.t₀) / Φ.F.q = 1 := by field_simp; ring
    rw [e0] at h0'; rw [e1] at h1'
    simp only [zero_mul, add_zero, one_mul] at h0' h1'
    have c0 : |Φ.eb l 0| ≤ κ := by
      have hc := PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb l 0, Φ.eb l 1]) 0
      simp at hc; linarith
    have c1 : |Φ.eb l 1| ≤ κ := by
      have hc := PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb l 0, Φ.eb l 1]) 1
      simp at hc; linarith
    have d0 : |Φ.eb l 0 + Φ.eb l 3| ≤ κ := by
      have hc := PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb l 0 + Φ.eb l 3, Φ.eb l 1 + Φ.eb l 4]) 0
      simp at hc; linarith
    have d1 : |Φ.eb l 1 + Φ.eb l 4| ≤ κ := by
      have hc := PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb l 0 + Φ.eb l 3, Φ.eb l 1 + Φ.eb l 4]) 1
      simp at hc; linarith
    have e3 : |Φ.eb l 3| ≤ 2 * κ := by
      calc |Φ.eb l 3| = |(Φ.eb l 0 + Φ.eb l 3) - Φ.eb l 0| := by ring_nf
        _ ≤ |Φ.eb l 0 + Φ.eb l 3| + |Φ.eb l 0| := abs_sub _ _
        _ ≤ 2 * κ := by linarith
    have e4 : |Φ.eb l 4| ≤ 2 * κ := by
      calc |Φ.eb l 4| = |(Φ.eb l 1 + Φ.eb l 4) - Φ.eb l 1| := by ring_nf
        _ ≤ |Φ.eb l 1 + Φ.eb l 4| + |Φ.eb l 1| := abs_sub _ _
        _ ≤ 2 * κ := by linarith
    linarith
  · rw [hμ, hb, hP]
    refine ae_muE_of_forall ν₀ A₀ _ _ hq0 hS fun p hp => ?_
    obtain ⟨hpA, hpt⟩ := (hSsub hp)
    refine ⟨fun τ hτ => ?_, ?_⟩
    · have ht : Φ.F.t₀ + Φ.F.q * τ ∈ Set.Icc Φ.F.t₀ (Φ.F.t₀ + Φ.F.q) :=
        ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
      obtain ⟨-, hv, hd1, hd2⟩ := htube p.1 hpA _ ht
      simp only [tnorm]
      have e1 := Φ.eval_normTest_at hq0 hD hsc0 δ₀ R₀ p.1 τ
      have e2 : eval (exS Φ.eb p.1 τ) (pderiv 3 (Φ.normTest δ₀ R₀)) =
          Φ.sc⁻¹ * (δ₀⁻¹ * eval (gx p.1 (Φ.F.t₀ + Φ.F.q * τ)) (pderiv 3 R₀)) := by
        rw [Φ.pderiv_normTest, smul_eval, Φ.eval_normTest_at hq0 hD hsc0]
      have e3 : eval (exS Φ.eb p.1 τ) (pderiv 3 (pderiv 3 (Φ.normTest δ₀ R₀))) =
          Φ.sc⁻¹ * Φ.sc⁻¹ * (δ₀⁻¹ * eval (gx p.1 (Φ.F.t₀ + Φ.F.q * τ)) (pderiv 3 (pderiv 3 R₀))) := by
        rw [Φ.pderiv_normTest, Derivation.map_smul, Φ.pderiv_normTest, smul_smul, smul_eval,
          Φ.eval_normTest_at hq0 hD hsc0]
      rw [e1, e2, e3, hsc]
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hδ)]
        calc δ₀⁻¹ * |eval (gx p.1 (Φ.F.t₀ + Φ.F.q * τ)) R₀| ≤ δ₀⁻¹ * (κ * δ₀) :=
              mul_le_mul_of_nonneg_left hv (inv_pos.mpr hδ).le
          _ = κ := by field_simp
          _ ≤ st.K := by linarith
      · have : (B₀ / δ₀)⁻¹ * (δ₀⁻¹ * eval (gx p.1 (Φ.F.t₀ + Φ.F.q * τ)) (pderiv 3 R₀)) =
            eval (gx p.1 (Φ.F.t₀ + Φ.F.q * τ)) (pderiv 3 R₀) / B₀ := by field_simp
        rw [this, abs_div, abs_of_pos hB, div_le_iff₀ hB]
        nlinarith
      · have : (B₀ / δ₀)⁻¹ * (B₀ / δ₀)⁻¹ * (δ₀⁻¹ *
            eval (gx p.1 (Φ.F.t₀ + Φ.F.q * τ)) (pderiv 3 (pderiv 3 R₀))) =
            δ₀ * eval (gx p.1 (Φ.F.t₀ + Φ.F.q * τ)) (pderiv 3 (pderiv 3 R₀)) / B₀ ^ 2 := by
          field_simp
        rw [this, abs_div, abs_mul, abs_of_pos hδ, abs_of_pos (by positivity : (0:ℝ) < B₀ ^ 2),
          div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hd2 hδ.le
        calc δ₀ * |eval (gx p.1 (Φ.F.t₀ + Φ.F.q * τ)) (pderiv 3 (pderiv 3 R₀))|
            ≤ δ₀ * (κ * B₀ ^ 2 / δ₀) := this
          _ = κ * B₀ ^ 2 := by field_simp
          _ ≤ st.K * B₀ ^ 2 := by nlinarith [sq_nonneg B₀]
    · have hτ : Φ.F.t₀ + Φ.F.q * ((p.2 - Φ.F.t₀) / Φ.F.q) = p.2 := by field_simp; ring
      show (st.K)⁻¹ ≤ |eval (exS Φ.eb (tnorm Φ.F.t₀ Φ.F.q p).1 (tnorm Φ.F.t₀ Φ.F.q p).2)
        (pderiv 3 (Φ.normTest δ₀ R₀))|
      simp only [tnorm]
      rw [Φ.pderiv_normTest, smul_eval, Φ.eval_normTest_at hq0 hD hsc0, hτ, hsc]
      have hl := hder p hp
      have : (B₀ / δ₀)⁻¹ * (δ₀⁻¹ * eval (gx p.1 p.2) (pderiv 3 R₀)) =
          eval (gx p.1 p.2) (pderiv 3 R₀) / B₀ := by field_simp
      rw [this, abs_div, abs_of_pos hB, le_div_iff₀ hB]
      have h1 : (st.K)⁻¹ ≤ κ⁻¹ := inv_anti₀ (by linarith) (by linarith)
      calc (st.K)⁻¹ * B₀ ≤ κ⁻¹ * B₀ := mul_le_mul_of_nonneg_right h1 hB.le
        _ = B₀ / κ := by ring
        _ ≤ _ := hl

end

end Submission.Obl.k4_finite_affine_candidate_return
