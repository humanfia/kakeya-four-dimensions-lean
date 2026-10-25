-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NormalizedPosteriors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NormalizedPosteriors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NormalizedPosteriors.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NormalizedPosteriors.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NormalizedPosteriors.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeLightParents

/-! The fixed normalized velocity posterior is a genuine probability law,
has the original whole-packet velocity envelope, and keeps the angular ball cap. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

noncomputable def PathData.normalizedVelocity {W : ℕ} (p : PathData W) (b : Fin p.C)
    (z : (ℕ × (Fin 6 → ℝ)) × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  ((2 : ℝ) ^ p.T (p.lev b))⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹ (v z.1 - p.u b)

theorem PathData.measurable_normalizedVelocity {W : ℕ} (p : PathData W) (b : Fin p.C) :
    Measurable (p.normalizedVelocity b) := by
  have hv : Continuous v :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.continuous_planarVelocity
  have hs : Continuous (fun l : ℕ × (Fin 6 → ℝ) => v l - p.u b) :=
    hv.sub (continuous_const : Continuous (fun _ : ℕ × (Fin 6 → ℝ) => p.u b))
  have hc : Continuous (fun l : ℕ × (Fin 6 → ℝ) =>
      ((2 : ℝ) ^ p.T (p.lev b))⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹ (v l - p.u b)) :=
    ((LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin (p.Q b)⁻¹)).comp
      hs).const_smul (((2 : ℝ) ^ p.T (p.lev b))⁻¹)
  exact hc.measurable.comp measurable_fst

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

noncomputable def PreparedAngularPath.velocityPosterior (b : Fin p.C) :
    Measure (EuclideanSpace ℝ (Fin 2)) :=
  (ProbabilityTheory.cond (Q.currentParentLaw b) univ).map (p.normalizedVelocity b)

theorem PreparedAngularPath.velocity_posterior_probability (hd : d.Valid) (b : Fin p.C)
    (hcurrent : Q.currentParentLaw b univ ≠ 0) : IsProbabilityMeasure (Q.velocityPosterior b) := by
  have ht : Q.currentParentLaw b univ ≠ ∞ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞)
    rw [currentParentLaw, Measure.restrict_apply_univ]
    exact (measure_mono (subset_univ _)).trans (hd.selected_incidence_mass_le_one k _)
  let := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hcurrent ht
  exact inferInstanceAs (IsProbabilityMeasure
    ((ProbabilityTheory.cond (Q.currentParentLaw b) univ).map (p.normalizedVelocity b)))

/-- The posterior is supported on the same normalized velocity ball supplied
by the full original assignment's whole-block fit. -/
theorem PreparedAngularPath.velocity_posterior_envelope
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) : ∀ᵐ w ∂Q.velocityPosterior b, ‖w‖ ≤ 2 * p.κ := by
  let bad : Set (EuclideanSpace ℝ (Fin 2)) := {w | ¬ ‖w‖ ≤ 2 * p.κ}
  have hbad : MeasurableSet bad := (measurableSet_le measurable_norm measurable_const).compl
  have hm : MeasurableSet (p.normalizedVelocity b ⁻¹' bad) :=
    hbad.preimage (p.measurable_normalizedVelocity b)
  have hz : Q.currentParentLaw b (p.normalizedVelocity b ⁻¹' bad) = 0 := by
    rw [currentParentLaw, Measure.restrict_apply hm]
    have he : (p.normalizedVelocity b ⁻¹' bad) ∩ (Q.residual (p.γ b) ∩ p.F b) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hFz := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.2.2.2.1 z hz.2.2
      exact hz.1 (hp.normalized_velocity_bound b z.1 hFz.2.1)
    rw [he, measure_empty]
  apply ae_iff.mpr
  change Q.velocityPosterior b bad = 0
  rw [velocityPosterior, Measure.map_apply (p.measurable_normalizedVelocity b) hbad]
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply, smul_eq_mul,
    hz, mul_zero]

/-- This is the single probability palette to use for both heavy strip
thresholds and the small-ball cap in strip packing. -/
theorem PreparedAngularPath.velocity_posterior_ball_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (b : Fin p.C) (t : T)
    {θ : ENNReal} (hθ : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hcurrent : Q.currentParentLaw b univ ≠ 0)
    (hfloor : θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ)
    {r : ℝ} (hscale : p.κ * r ≤ δ (d.N k) (u t))
    (center : EuclideanSpace ℝ (Fin 2)) :
    Q.velocityPosterior b (Metric.closedBall center r) ≤
      100 * ((ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)) *
        (angularPreparationEpsilon m p.κ)⁻¹) * θ⁻¹) := by
  have hF (a : Fin p.C) : MeasurableSet (p.F a) :=
    (hp.2.2.2.2.2.2.2 a).2.2.2.2.2.2.2.2.2.1
  rw [velocityPosterior, Measure.map_apply (p.measurable_normalizedVelocity b)
    Metric.isClosed_closedBall.measurableSet, Q.current_parent_cond_eq_original hHE hF b]
  simpa only [PathData.normalizedVelocity, preimage_ofPred_eq, Metric.closedBall,
    dist_eq_norm] using Q.parent_ball_cap hd hp hHE b t hθ hθtop hcurrent hfloor hscale center

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
