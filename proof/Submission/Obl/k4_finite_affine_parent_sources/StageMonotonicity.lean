-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.Stages

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory

/-- The endpoint range supplies every smaller tested pure/joint range,
using exactly the same incidence law and palette. -/
theorem EH2_mono {α : Type} [MeasurableSpace α]
    {d S R R' : ℝ} {st : EStage α} (hR : 0 < R) (hRR' : R ≤ R')
    (h : EH2 d S st R') : EH2 d S st R := by
  have hi : R'⁻¹ ≤ R⁻¹ := inv_anti₀ hR hRR'
  intro r s v hr hr' hs hs' hv hv'
  exact h r s v (hi.trans hr) (hr'.trans hRR') hs (hs'.trans hRR')
    (hi.trans hv) (hv'.trans hRR')

/-- True-label bounds restrict to smaller ranges. In particular the
per-label velocity cap keeps its original full prior and fixed palette. -/
theorem EH3_mono {α : Type} [MeasurableSpace α]
    {d κ ℓ U e₀ R R' : ℝ} {st : EStage α} (hR : 0 < R) (hRR' : R ≤ R')
    (h : EH3 d κ ℓ U e₀ st R') : EH3 d κ ℓ U e₀ st R := by
  have hi : R'⁻¹ ≤ R⁻¹ := inv_anti₀ hR hRR'
  intro s hs hsU
  obtain ⟨hT₀, hT₁, hmeas, hdisj, hlabels, hcover, hcap⟩ := h s (hi.trans hs) hsU
  refine ⟨hT₀, hT₁, hmeas, hdisj, hlabels, hcover, ?_⟩
  intro i v v₀ hv hv'
  exact hcap i v v₀ (hi.trans hv) (hv'.trans hRR')

theorem EH4_mono {α : Type} [MeasurableSpace α]
    {U R R' : ℝ} {st : EStage α} (hR : 0 < R) (hRR' : R ≤ R')
    (h : EH4 U st R') : EH4 U st R := by
  intro s t hs hst ht i
  exact h s t ((inv_anti₀ hR hRR').trans hs) hst ht i

/-- Model assembly only needs the three range predicates at the single
endpoint n; the frozen StageGood package then follows for all 1<R<=n. -/
theorem stageGood_of_max_range
    (d κ ℓ S : ℝ) (n : ℕ) (st : EStage Trajectory)
    (hN : (n : ℝ) + 2 ≤ st.N) (hK : 1 ≤ st.K)
    (hKmax : st.K ≤ st.N ^ (1 / ((n : ℝ) + 1))) (h1 : EH1 st)
    (h2 : EH2 d S st n) (h3 : EH3 d κ ℓ 1 1 st n) (h4 : EH4 1 st n) :
    StageGood d κ ℓ S n st := by
  refine ⟨hN, ⟨hK, hKmax⟩, h1, fun R hR hRn => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans hR
  exact ⟨EH2_mono hR0 hRn h2, EH3_mono hR0 hRn h3, EH4_mono hR0 hRn h4⟩

end Submission.Obl.k4_finite_affine_parent_sources
