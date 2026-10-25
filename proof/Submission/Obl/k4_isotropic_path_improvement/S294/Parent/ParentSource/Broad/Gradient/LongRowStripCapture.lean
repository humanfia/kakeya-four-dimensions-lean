-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.LongRowStripCapture, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/LongRowStripCapture.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit af69463910936c02b3e287e9153c4781be3e7639,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/LongRowStripCapture.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.RenewalCaptureCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentPrediction

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric

noncomputable section

/-- Constants from the existing degree-24 analytic long-row theorem.
They are chosen before every problem, source, depth and format. -/
def captureRowK₀ : ℝ := Classical.choose (Analytic.quarter_core_constant_fit_first_jet 24)

def captureRowC₀ : ℝ :=
  Classical.choose (Classical.choose_spec (Analytic.quarter_core_constant_fit_first_jet 24))

theorem captureRow_constants : 0 < captureRowK₀ ∧ 1 ≤ captureRowC₀ := by
  have h := Classical.choose_spec
    (Classical.choose_spec (Analytic.quarter_core_constant_fit_first_jet 24))
  exact ⟨h.1,h.2.1⟩

def captureDirectionalFactor (B θ : ℝ) : ℝ :=
  2*captureRowK₀*(1+2*B)*θ^(-captureRowC₀)

def captureGradientCoeff (A δ θ : ℝ) (J : ℕ) : ℝ :=
  6*A^J*(1+((1/2:ℝ)+2)/δ)*captureDirectionalFactor (1/2) θ

/-- Genuine returning rows in the same analytic core give the actual
directional tests used by strip capture. The representation, denominator
and first-jet estimate come from the existing core analytic package. -/
theorem directional_test_from_original_long_rows
    {Ω : Type*} (Z : Ω → EuclideanSpace ℝ (Fin 3))
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (S : Set Ω)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : CorePredictionAnalytic g)
    {B θ ε : ℝ} (hB : 0 ≤ B) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hε : 0 ≤ ε)
    (hcore : ∀ ω∈S, ‖Z ω‖ ≤ 1/4) (hspeed : ∀ ω∈S, ‖V ω‖ ≤ B)
    (hrows : ∀ ω∈S, ∃ T : Set ℝ, ∃ intercept : ℝ,
      MeasurableSet T ∧ ENNReal.ofReal θ ≤ volume T ∧
      (∀ t∈T, ‖Z ω+t • spacetimeDirection (V ω)‖ ≤ 1/4) ∧
      ∀ t∈T, |g (Z ω+t • spacetimeDirection (V ω))-intercept| ≤ ε) :
    ∀ ω∈S, |fderiv ℝ g (Z ω) (spacetimeDirection (V ω))| ≤
      captureDirectionalFactor B θ*ε := by
  obtain ⟨⟨Δ,U,V',Wd,sq,Q,hΔ,hU,hV',hWd,hroot,hrep,hQ,hreal,hden⟩,_,_⟩ := hg
  have hfirst := (Classical.choose_spec
    (Classical.choose_spec (Analytic.quarter_core_constant_fit_first_jet 24))).2.2
  intro ω hω
  have hdir : 1 ≤ ‖spacetimeDirection (V ω)‖ := by
    have hh := PiLp.norm_apply_le (spacetimeDirection (V ω)) 0
    simpa [spacetimeDirection] using hh
  have hupper : ‖spacetimeDirection (V ω)‖ ≤ 1+2*B := by
    have hs := Submission.Lib.K4PlankGeometry.rawDirection_norm_sq (V ω)
    change ‖spacetimeDirection (V ω)‖^2=1+‖V ω‖^2 at hs
    have hv := hspeed ω hω
    have hsq := pow_le_pow_left₀ (norm_nonneg (V ω)) hv 2
    nlinarith [norm_nonneg (spacetimeDirection (V ω)),sq_nonneg B]
  obtain ⟨T,intercept,hT,hvol,hTcore,hfit⟩ := hrows ω hω
  have hh := hfirst Δ U V' Wd hΔ hU hV' hWd sq Q g hroot hrep hQ hreal
    (Z ω) (spacetimeDirection (V ω)) (hcore ω hω) hdir
    (hden _ (by linarith [hcore ω hω])) T θ ε intercept hT hθ hθ1 hε hvol hTcore hfit
  change |fderiv ℝ g (Z ω) (spacetimeDirection (V ω))| ≤
    2*captureRowK₀*‖spacetimeDirection (V ω)‖*θ^(-captureRowC₀)*ε at hh
  apply hh.trans
  unfold captureDirectionalFactor
  have hK := captureRow_constants.1
  gcongr

/-- A genuine long-row source at ANY depth either controls the analytic
core gradient or has all but one original floor captured by explicit
renewal-cell strips. No broadness is assumed at that depth. -/
theorem original_long_rows_gradient_or_strip_capture
    {D J : ℕ} (hjets : ValueJetBound D J) (hD : 578 ≤ D)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3)) (hZ : Measurable Z)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V)
    (S : Set Ω) (hS : MeasurableSet S)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : CorePredictionAnalytic g)
    {K A β δ B θ ε : ℝ} {q : ℕ} (hK : 2 ≤ K) (hA : 2 ≤ A) (hAK : A ≤ K)
    (hβ : 0 < β) (hδ : 0 < δ) (hδfloor : (K^q)⁻¹ ≤ δ)
    (hB : 0 ≤ B) (hBK : B ≤ K) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hε : 0 ≤ ε)
    (hcore : ∀ ω∈S, ‖Z ω‖ ≤ 1/4) (hspeed : ∀ ω∈S, ‖V ω‖ ≤ B)
    (hcap : ∀ U, MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β*volume U)
    (hrows : ∀ ω∈S, ∃ T : Set ℝ, ∃ intercept : ℝ,
      MeasurableSet T ∧ ENNReal.ofReal θ ≤ volume T ∧
      (∀ t∈T, ‖Z ω+t • spacetimeDirection (V ω)‖ ≤ 1/4) ∧
      ∀ t∈T, |g (Z ω+t • spacetimeDirection (V ω))-intercept| ≤ ε) :
    (∀ x∈closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ 6*A^J*(1+(B+2)/δ)*captureDirectionalFactor B θ*ε) ∨
    ∃ (normal : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 2)) (center : (Fin 3 → ℤ) → ℝ),
      (∀ i, ‖normal i‖=1 ∧ |center i| ≤ B+δ) ∧
      MeasurableSet (⋃ i, (renewalCellCode K J (q+1) ∘ Z) ⁻¹' {i}∩
        V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ) ∧
      μ (S\⋃ i, (renewalCellCode K J (q+1) ∘ Z) ⁻¹' {i}∩
        V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ) <
          ENNReal.ofReal (β/A) := by
  have hK0 := captureRow_constants.1
  have hE : 0 ≤ captureDirectionalFactor B θ*ε := by unfold captureDirectionalFactor; positivity
  have hh := original_renewal_gradient_or_strip_capture hjets μ Z hZ V hV S hS
    (fun ω hω => by rw [mem_closedBall,dist_zero_right]; linarith [hcore ω hω])
    g hg.2.1 (hg.2.2 D hD) hK hA hAK hβ hδ hδfloor hE hB hBK hcap hspeed
    (directional_test_from_original_long_rows Z V S g hg hB hθ hθ1 hε hcore hspeed hrows)
  rcases hh with hgrad | hcapture
  · left
    intro x hx
    exact (hgrad x hx).trans_eq (by ring)
  · exact Or.inr hcapture

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
