-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.OriginalBaseLocalization
import Submission.Obl.k4_finite_affine_parent_sources.SourceLabelGroups
import Submission.Obl.k4_finite_affine_parent_sources.ActiveLabels

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

section Valid

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- A label's full original assignment has bounded velocity in its own
major-axis normalization, independently of its hidden scale. -/
theorem labelFrame_native_velocity (Q : Fin p.C) (Bw δp : ℝ)
    (l : Trajectory) (hl : l ∈ p.assigned Q) :
    ‖gv (0, (labelFrame p Q Bw δp).eb l)‖ ≤ 6 * p.κ := by
  change ‖WithLp.toLp 2 ![(labelFrame p Q Bw δp).eb l 3,
    (labelFrame p Q Bw δp).eb l 4]‖ ≤ _
  rw [PFrame.velocity_eq, norm_smul, labelFrame_F,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ p.T (p.lev Q))⁻¹)]
  have hv := gchart_velocity (hp.chart Q) hl
  have hmajor := MajorFrame.fit (hp.chart Q).1 _ _ hv
  calc
    _ ≤ ((2 : ℝ) ^ p.T (p.lev Q))⁻¹ * (3 * (2 * p.κ * (2 : ℝ) ^ p.T (p.lev Q))) :=
      mul_le_mul_of_nonneg_left hmajor (by positivity)
    _ = 6 * p.κ := by field_simp <;> ring

/-- The original no-candidate hypothesis localizes every descendant
packet in the native base of an actual ancestor's oscillation groups.
The required velocity bound holds on the full descendant assignment. -/
theorem labelFrame_original_descendant_base_diameter
    (hNk : 0 < Nk) (Mc : ℕ) (d₁ ρ gain ε : ℝ) (Hres : Fin W → Set Incidence)
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned Hres)
    (Q child : Fin p.C) (hlev : p.lev Q ≤ p.lev child)
    (hdesc : forestAncestor p.lev p.par child (p.lev Q) = Q)
    (Bw δp h H : ℝ) (hgain : gain ≤ h) (hupper : h ≤ 1 / 8)
    (hroom : p.r (p.lev child) + 2 * h * L ≤ L)
    (hprior : 0 < ν (p.world child) (p.assigned child))
    (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (V : Set Incidence) (hne : V.Nonempty)
    (hV : ∀ z ∈ V, z ∈ Hres (p.world child) ∧ z.1 ∈ p.assigned child ∧
      z.2 ∈ Icc ((p.bin child : ℝ) / (2 : ℝ) ^ p.T (p.lev child))
        (((p.bin child : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev child)))
    (hfloor : ENNReal.ofReal (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev child)) *
      ν (p.world child) (p.assigned child) ≤ (ν (p.world child)).prod volume V)
    (hH : 1 ≤ H) (hκH : 6 * p.κ ≤ H)
    (hrow : 12 * p.κ / (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) ≤ H)
    (x x' : Incidence) (hx : x ∈ p.packet child) (hx' : x' ∈ p.packet child) :
    ‖nativeBase (framePoint (labelFrame p Q Bw δp) x) -
        nativeBase (framePoint (labelFrame p Q Bw δp) x')‖ ≤
      16 * H ^ 4 * ((((2 : ℝ) ^ p.T (p.lev child))⁻¹) /
        (((2 : ℝ) ^ p.T (p.lev Q))⁻¹)) := by
  have hsub := hp.ancestor_assignment_subset child (p.lev Q) hlev
  rw [hdesc] at hsub
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.one_le_slack
  have hvel : ∀ l ∈ p.assigned child, ‖gv (0, (labelFrame p Q Bw δp).eb l)‖ ≤ 6 * p.κ :=
    fun l hl => labelFrame_native_velocity hp Q Bw δp l (hsub hl)
  have hdiam := (labelFrame p Q Bw δp).original_end_label_base_diameter hp hNk Mc
    d₁ ρ gain ε Hres hno child h hgain hupper hroom hprior hbias V hne hV hfloor
    (labelFrame_q_pos hp Q Bw δp) (isUnit_iff_ne_zero.mp (labelFrame_det hp Q Bw δp))
    (6 * p.κ) H (by positivity) hH (by linarith) hκH hvel
    (by convert hrow using 1 <;> ring) x.1 hx.1 x'.1 hx'.1 x.2 x'.2 hx.2 hx'.2
  simpa only [framePoint, nativeBase_pointS, tnorm, labelFrame_F] using hdiam

end Valid

end

end Submission.Obl.k4_finite_affine_parent_sources
