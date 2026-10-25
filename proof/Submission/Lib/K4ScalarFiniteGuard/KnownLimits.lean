/-
Adapted from: here:o093
Original proofs by session x0535 in this LOT workspace. The scalar atlas
interface was written in the same o093 tree by x0364; this package retains
its literal fields while requiring only the sampling hypotheses used here.
-/

import Submission.Lib.K4ScalarFiniteGuard.ChartTransport

/-!
Limits of the thickness and knowledge exponents of actual chart outputs.
Finite compatibility lists absorb their power-grid mismatch into a
vanishing original-resolution loss.
-/

set_option autoImplicit false

namespace Submission.Lib.K4ScalarFiniteGuard

open Filter
open scoped Topology

/-- Every actual chart has a nonnegative horizon budget at a resolution
strictly greater than one. -/
theorem chart_horizon_nonneg (p : Code) (B k : ℕ) (r b h ε : ℝ) (isTrue : Bool)
    (hN : 1 < N p k) (hc : Chart p B r b h ε isTrue k) : 0 ≤ h := by
  rcases hc with ⟨T, n, γ, j, A, C, u, v, J, P, Λ, ht, _⟩
  by_contra hneg
  have hsmall := Real.rpow_lt_one_of_one_lt_of_neg hN (lt_of_not_ge hneg)
  have hone : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  linarith

/-- On any actual sample subsequence, convergent exponents and vanishing
losses can be replaced by their limits at any prescribed positive loss. -/
theorem eventually_transport_chart_exponents (p : Code) (hp : Sampling p) (B : ℕ)
    (sample : ℕ → ℕ) (hsample : Tendsto sample atTop atTop)
    (r b : ℝ) (rseq bseq horizon loss : ℕ → ℝ)
    (hr : Tendsto rseq atTop (𝓝 r)) (hb : Tendsto bseq atTop (𝓝 b))
    (hloss : Tendsto loss atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      Chart p B (rseq k) (bseq k) (horizon k) (loss k) false (sample k) →
      Chart p B r b (horizon k) ε false (sample k) := by
  have hNt : Tendsto (fun k => N p (sample k)) atTop atTop := hp.2.comp hsample
  have hfour : ∀ᶠ k in atTop, (4 : ℝ) ≤ N p (sample k) ^ (ε / 4) :=
    ((tendsto_rpow_atTop (show 0 < ε / 4 by positivity)).comp hNt).eventually_ge_atTop 4
  have hl : ∀ᶠ k in atTop, loss k < ε / 4 :=
    hloss.eventually_lt tendsto_const_nhds (by positivity)
  have hrd : ∀ᶠ k in atTop, |rseq k - r| < ε / 4 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.1 hr (ε / 4) (by positivity)
  have hbd : ∀ᶠ k in atTop, |bseq k - b| < ε / 4 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.1 hb (ε / 4) (by positivity)
  filter_upwards [hfour, hl, hrd, hbd] with k h4 hl hr hb hc
  have hN : 1 ≤ N p (sample k) := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1 _)
  have hNpos : 0 < N p (sample k) := lt_of_lt_of_le zero_lt_one hN
  have hthick := chart_changeThickness p B (sample k) (rseq k) r (bseq k) (horizon k)
    (loss k) (ε / 2) hN (by linarith) (by
      have := (abs_lt.1 hr).1
      linarith) hc
  apply chart_changeKnowledge p B (sample k) r (bseq k) b (horizon k)
    (ε / 2) ε false hN (by linarith) ?_ hthick
  calc
    _ ≤ N p (sample k) ^ (ε / 4) * N p (sample k) ^ (ε / 2 + |bseq k - b|) :=
      mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hNpos.le _)
    _ = N p (sample k) ^ (ε / 4 + (ε / 2 + |bseq k - b|)) :=
      (Real.rpow_add hNpos _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- Infinitely many actual uniformly tempered charts with converging
thickness/knowledge exponents produce a genuine known atlas at the
limiting exponents. The horizon needs only an eventual upper envelope. -/
theorem known_of_varying_charts (p : Code) (hp : Sampling p) (B : ℕ) (hB : 1 ≤ B)
    (sample : ℕ → ℕ) (hsample : Tendsto sample atTop atTop)
    (r b h : ℝ) (hh : 0 ≤ h) (rseq bseq horizon loss : ℕ → ℝ)
    (hr : Tendsto rseq atTop (𝓝 r)) (hb : Tendsto bseq atTop (𝓝 b))
    (hloss : Tendsto loss atTop (𝓝 0))
    (hhorizon : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, horizon k ≤ h + ε)
    (hcharts : ∃ᶠ k in atTop,
      Chart p B (rseq k) (bseq k) (horizon k) (loss k) false (sample k)) :
    Known p r b h := by
  refine ⟨hh, B, hB, ?_⟩
  intro ε hε
  have htransport := eventually_transport_chart_exponents p hp B sample hsample r b
    rseq bseq horizon loss hr hb hloss ε hε
  have hf : ∃ᶠ k in atTop, Chart p B r b (h + ε) ε false (sample k) := by
    apply (hcharts.and_eventually (htransport.and (hhorizon ε hε))).mono
    intro k hk
    exact chart_mono p B (sample k) r b (horizon k) (h + ε) ε ε false
      ((by norm_num : (1 : ℝ) ≤ 2).trans (hp.1 _)) hk.2.2 le_rfl (hk.2.1 hk.1)
  apply Filter.frequently_atTop.2
  intro a
  obtain ⟨k, hk, hka⟩ := (hf.and_eventually (hsample.eventually_ge_atTop a)).exists
  exact ⟨sample k, hka, hk⟩

end Submission.Lib.K4ScalarFiniteGuard
