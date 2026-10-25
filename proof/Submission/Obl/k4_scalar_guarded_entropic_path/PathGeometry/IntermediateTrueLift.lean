/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/IntermediateTrueLift.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SaturatedCalibration
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueChosenCharts
import Submission.Obl.k4_scalar_true_terminal_lifting.Glue
import Submission.Obl.k4_scalar_chart_normalization.Coarsening

/-! Reuse the accepted finite TRUE terminal lift at arbitrary intermediate
endpoints. The endpoint codes retain every original law and profile value;
no exactness assertion for these auxiliary endpoint codes is needed. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.IntermediateTrueLift

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting

noncomputable section

variable {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)

/-- Only the terminal length of the auxiliary code matters in this finite
lifting argument. All priors, events, weights and profile values are literal. -/
def parentEndpoint (s : ℝ) : Code :=
  Submission.Obl.k4_scalar_chart_normalization.coarsen p (r + s) 0

def childEndpoint (s : ℝ) : Code :=
  Submission.Obl.k4_scalar_chart_normalization.coarsen q s 0

/-- The SAME literal refinement body works at every auxiliary endpoint. -/
theorem endpointBody (s : ℝ) :
    RefBody (parentEndpoint (p := p) (r := r) s) (childEndpoint (q := q) s) r b h
      w.sample w.loss w.exponent w.T w.world w.block w.assignment w.selected
      w.center w.speed w.width w.polynomial w.lists w.trajectory := w.refBody

/-- One finite index of that SAME normalization, for the accepted lift. -/
def endpointStep (s : ℝ) (k : ℕ) :
    RefStep (parentEndpoint (p := p) (r := r) s) (childEndpoint (q := q) s)
      r b k (w.sample k) := (endpointBody w s).step k

variable {B₂ k : ℕ} {s h₂ ε₂ : ℝ}

/-- Reinterpret a child chart at its own literal endpoint, retaining all
of its data and its original true floor. -/
def endpointChart (Q : ChartW q B₂ s s h₂ ε₂ true k) :
    ChartW (childEndpoint (q := q) s) B₂ (L (childEndpoint (q := q) s))
      (L (childEndpoint (q := q) s)) h₂ ε₂ true k :=
  ⟨Q.T, Q.n, Q.γ, Q.j, Q.A, Q.C, Q.u, Q.v, Q.J, Q.P, Q.Λ, Q.hcd⟩

/-- An actual intermediate TRUE chart lifts to the original problem with
the accepted explicit geometry, full assignments, masks and original lists.
The full-prior saturation is the only calibration input. -/
theorem lift_chartData (hp : Exact p) (hq : Exact q)
    (Q : ChartW q B₂ s s h₂ ε₂ true k)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (hr : 0 ≤ r) (hbs : b ≤ r + s) (hloss₁ : w.loss k ≤ 1)
    (hε₂ : 0 ≤ ε₂) {δ ε₃ : ℝ} (hσ : σ k ≤ δ)
    (hδ : 0 ≤ δ) (hε₃ : w.loss k + ε₂ + δ ≤ ε₃)
    (hε₃' : 4 * N p (w.sample k) ^ (w.loss k + ε₂) ≤ N p (w.sample k) ^ ε₃) :
    let S := endpointStep w s k
    let Q' := endpointChart Q
    ChartData p (2 * B₂ + 2 * w.exponent + 9) (r + s) (r + s)
      (h + w.loss k + h₂) ε₃ true (w.sample k) (w.T k + Q.T) Q.n
        (S.γ₃ Q') (S.j₃ Q') (S.A₃ Q') (S.C₃ Q')
        (S.u₃ Q') (S.v₃ Q') (S.J₃ Q') (S.P₃ Q') (S.Λ₃ Q') := by
  let S := endpointStep w s k
  let Q' := endpointChart Q
  have hgood : ∀ d, ENNReal.ofReal
      (N (parentEndpoint (p := p) (r := r) s) (w.sample k) ^
        (f (childEndpoint (q := q) s) (L (childEndpoint (q := q) s)) -
          f (parentEndpoint (p := p) (r := r) s) (L (parentEndpoint (p := p) (r := r) s)) - δ) *
            S.J₁ (Q'.γ d)) ≤
      ν (parentEndpoint (p := p) (r := r) s) (w.sample k)
        (S.γ₁ (Q'.γ d)) (S.A₁ (Q'.γ d)) := by
    intro d
    have hfloor := w.intermediate_floor_of_saturation hp hq σ hsat hrelative k hσ (Q.γ d)
    rw [(w.charts k).1] at hfloor
    exact hfloor
  exact S.lift_chartData Q' (hp.1.1 (w.sample k)) (hp.2.1 (w.sample k)).2.1
    (fun a => ((hp.2.1 (w.sample k)).2.2.2.1 a).1) hr
    (show s = (r + s) - r by ring) hbs hloss₁ hε₂ hgood hε₃ hδ (w.loss_pos k).le hε₃'

/-- The actual lifted witness, preserving the accepted composition data. -/
def liftChartW (hp : Exact p) (hq : Exact q)
    (Q : ChartW q B₂ s s h₂ ε₂ true k)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (hr : 0 ≤ r) (hbs : b ≤ r + s) (hloss₁ : w.loss k ≤ 1)
    (hε₂ : 0 ≤ ε₂) {δ ε₃ : ℝ} (hσ : σ k ≤ δ)
    (hδ : 0 ≤ δ) (hε₃ : w.loss k + ε₂ + δ ≤ ε₃)
    (hε₃' : 4 * N p (w.sample k) ^ (w.loss k + ε₂) ≤ N p (w.sample k) ^ ε₃) :
    ChartW p (2 * B₂ + 2 * w.exponent + 9) (r + s) (r + s)
      (h + w.loss k + h₂) ε₃ true (w.sample k) :=
  let S := endpointStep w s k
  let Q' := endpointChart Q
  ⟨w.T k + Q.T, Q.n, S.γ₃ Q', S.j₃ Q', S.A₃ Q', S.C₃ Q',
    S.u₃ Q', S.v₃ Q', S.J₃ Q', S.P₃ Q', S.Λ₃ Q',
    lift_chartData w hp hq Q σ hsat hrelative hr hbs hloss₁ hε₂ hσ hδ hε₃ hε₃'⟩

/-- The finite TRUE lift, with its fixed complexity and actual time budget. -/
theorem lift_chart (hp : Exact p) (hq : Exact q)
    (Q : ChartW q B₂ s s h₂ ε₂ true k)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (hr : 0 ≤ r) (hbs : b ≤ r + s) (hloss₁ : w.loss k ≤ 1)
    (hε₂ : 0 ≤ ε₂) {δ ε₃ : ℝ} (hσ : σ k ≤ δ)
    (hδ : 0 ≤ δ) (hε₃ : w.loss k + ε₂ + δ ≤ ε₃)
    (hε₃' : 4 * N p (w.sample k) ^ (w.loss k + ε₂) ≤ N p (w.sample k) ^ ε₃) :
    Chart p (2 * B₂ + 2 * w.exponent + 9) (r + s) (r + s)
      (h + w.loss k + h₂) ε₃ true (w.sample k) := by
  apply (chart_iff_nonempty ..).mpr
  exact ⟨liftChartW w hp hq Q σ hsat hrelative hr hbs hloss₁ hε₂ hσ hδ hε₃ hε₃'⟩

/-- A frequent intermediate TRUE cost lifts through a saturated actual
refinement, with the SAME asymptotic sum of time costs. -/
theorem trueKnown_lift (hp : Exact p) (hq : Exact q)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    (hσ : Tendsto σ atTop (nhds 0))
    (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (hr : 0 ≤ r) (hbs : b ≤ r + s) (hh : 0 ≤ h)
    {h₂ : ℝ} (htrue : TrueKnown q s s h₂) :
    TrueKnown p (r + s) (r + s) (h + h₂) := by
  classical
  obtain ⟨hh₂, B₂, hB₂, hcharts⟩ := htrue
  refine ⟨add_nonneg hh hh₂, 2 * B₂ + 2 * w.exponent + 9, by omega, ?_⟩
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  have hloss₁ := w.loss_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlossε := w.loss_tendsto.eventually (gt_mem_nhds hquarter)
  have hsigma := hσ.eventually (gt_mem_nhds hquarter)
  have hfour : ∀ᶠ k in atTop, 4 ≤ N p (w.sample k) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).comp
      (hp.1.2.1.comp w.sample_strictMono.tendsto_atTop)).eventually_ge_atTop 4
  have hfreq : ∃ᶠ k in atTop,
      Chart p (2 * B₂ + 2 * w.exponent + 9) (r + s) (r + s)
        (h + h₂ + ε) ε true (w.sample k) := by
    apply ((hcharts (ε / 4) hquarter).and_eventually
      (hloss₁.and (hlossε.and (hsigma.and hfour)))).mono
    rintro k ⟨hc, hl1, hlε, hσε, h4⟩
    obtain ⟨Q⟩ := (chart_iff_nonempty q B₂ s s (h₂ + ε / 4) (ε / 4) true k).mp hc
    have hN : 0 < N p (w.sample k) := by linarith [hp.1.1 (w.sample k)]
    have hN₁ : 1 ≤ N p (w.sample k) := by linarith [hp.1.1 (w.sample k)]
    have hfactor : 4 * N p (w.sample k) ^ (w.loss k + ε / 4) ≤
        N p (w.sample k) ^ ε := by
      calc
        _ ≤ N p (w.sample k) ^ (ε / 2) * N p (w.sample k) ^ (ε / 2) :=
          mul_le_mul h4 (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith))
            (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
        _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
    have hlift := lift_chart w hp hq Q σ hsat hrelative hr hbs hl1.le hquarter.le
      hσε.le hquarter.le (show w.loss k + ε / 4 + ε / 4 ≤ ε by linarith) hfactor
    exact Submission.Obl.k4_scalar_true_terminal_lifting.chart_mono hlift hN₁ le_rfl
      (by linarith : h + w.loss k + (h₂ + ε / 4) ≤ h + h₂ + ε) le_rfl
  rw [Filter.frequently_atTop] at hfreq ⊢
  intro K
  obtain ⟨k, hk, hc⟩ := hfreq K
  exact ⟨w.sample k, hk.trans (w.sample_strictMono.id_le k), hc⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.IntermediateTrueLift
