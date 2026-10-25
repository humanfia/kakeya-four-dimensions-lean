/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file StripDuration.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.StripEntries
import Submission.Obl.k4_scalar_graph_residual_discovery.CountedDuration

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_initial_horizon_bound

/-- All short original strip entries are deleted for one global budget. This
uses the entry count on each trajectory and the unchanged original prior. -/
theorem short_strip_entry_mass_le
    (ν : Measure ScalarLine) [SFinite ν] (μ : Measure ScalarIncidence)
    {c : ℝ≥0∞} (hdom : μ ≤ c • (ν.prod volume))
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (row : (Fin 3 → ℤ) → Fin 2 → ℝ) {H b ρ p A D : ℝ}
    (hH : 1 ≤ H) (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ) (hp : 0 < p)
    (hcoeff : ∀ z ∈ E, ∀ e, |z.1.2 e| ≤ H)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hA : ∀ q, 1 + |row q 0| + |row q 1| ≤ A) (hD : 0 ≤ D)
    (hderiv : ∀ z ∈ E,
      |(normalPolynomial
        (row (cell ρ (leftCorner b (cell b (scalarPosition z))))) z.1).derivative.eval z.2| ≤ D)
    (a : ℝ≥0∞) :
    μ {z | z ∈ E ∧
      incidenceDuration (E ∩ stripRecord b ρ p row ⁻¹' {stripRecord b ρ p row z}) z.1 < a} ≤
        c * (a * ENNReal.ofReal (343 * (3 * H / ρ + 2) *
          (2 * (D * (ρ + 2 * b) + 2 * A * b) / p + 2)) * ν univ) := by
  classical
  let Q : ℝ := 343 * (3 * H / ρ + 2) *
    (2 * (D * (ρ + 2 * b) + 2 * A * b) / p + 2)
  have hH0 : 0 ≤ H := by linarith
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ 1 + |row 0 0| + |row 0 1|).trans (hA 0)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hlist (l : ScalarLine) : ∃ L : Finset ((Fin 3 → ℤ) × ℤ),
      (L.card : ℝ) ≤ Q ∧ ∀ t, (l, t) ∈ E → stripRecord b ρ p row (l, t) ∈ L := by
    by_cases hl : ∀ e, |l.2 e| ≤ H
    · obtain ⟨L, hcard, hmem⟩ := trajectory_strip_entry_list row l {t | (l, t) ∈ E}
        hH hb hρ hbρ hp hl (fun t ht => htime (l, t) ht) hA hD
        (fun t ht => hderiv (l, t) ht)
      exact ⟨L, hcard, fun t ht => hmem t ht⟩
    · refine ⟨∅, ?_, ?_⟩
      · simpa only [Finset.card_empty, Nat.cast_zero] using hQ
      · intro t ht
        exact False.elim (hl (hcoeff (l, t) ht))
  choose L hcard hmem using hlist
  apply record_short_incidence_deletion_le ν μ hdom hE (stripRecord b ρ p row)
    (measurable_stripRecord b ρ p row) L a (ENNReal.ofReal Q)
  · intro l
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hcard l)
  · intro z hz
    exact hmem z.1 z.2 hz

end Submission.Obl.k4_scalar_graph_residual_discovery
