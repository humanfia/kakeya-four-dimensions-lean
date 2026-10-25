/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/JointSource.lean.
   Existing source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.AsymptoticUpper
import Submission.Obl.k4_critical_switching_state_preparation.SourceMaps

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α]

/-- A joint witness on the original residual, before switching-state or
trajectory deletions. The original primitive mass is preserved exactly. -/
structure RegularPairSource (cfg : Data α) (k : ℕ) (s v ζ δ : ℝ)
    (depths : Finset ℝ) (ip : Fin (cfg.n k s)) (L : Fin 4 → ℝ) where
  source : Set (α × ℝ)
  measurable_source : MeasurableSet source
  source_subset : source ⊆ cfg.primitiveEvent k s ip L (cfg.N k ^ ζ * cfg.N k ^ (-s))
  source_mass : cfg.ρ k source =
    cfg.ρ k (cfg.primitiveEvent k s ip L (cfg.N k ^ ζ * cfg.N k ^ (-s)))
  coefficients : ∀ p ∈ source, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k
  horizontal_defect : ∀ p ∈ source, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)
  true_descendants : ∀ p ∈ source, ∀ t ∈ depths, ∃ i : Fin (cfg.n k t),
    p.1 ∈ cfg.B k t i ∧ p.2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
    cfg.A k t i ⊆ cfg.A k s ip ∧ I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip)
  pairs : Finset (ℤ × (Fin 3 → ℤ))
  pairs_exact : ∀ u, u ∈ pairs ↔ ∃ p ∈ source,
    cfg.sourcePair k s ip L (cfg.N k ^ (-s - v)) (cfg.N k ^ (-10 * s)) p = u
  pairs_card : (pairs.card : ℝ) * (cfg.N k ^ (-10 * s)) ^ 3 ≤ cfg.N k ^ (cfg.d * v + δ)

/-- All original pointwise data, a finite list of true depths, and the
quantitative actual pair table can be prepared simultaneously. -/
theorem Valid.eventually_regular_pair_source {cfg : Data α} (h : cfg.Valid) {s v ζ δ : ℝ}
    (hs : 0 < s) (hv : 0 < v) (hvs : v ≤ s) (hsU : s + v ≤ cfg.U)
    (hζ : 0 < ζ) (hζs : ζ ≤ s) (hgap : 0 < cfg.κ * s - v - ζ) (hδ : 0 < δ)
    (depths : Finset ℝ) (hupper : s + v ∈ depths)
    (hdepths : ∀ t ∈ depths, s < t ∧ t ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ (ip : Fin (cfg.n k s)) (L : Fin 4 → ℝ),
      L 0 = 0 → (∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) →
      Nonempty (cfg.RegularPairSource k s v ζ δ depths ip L) := by
  classical
  have hlevels : ∀ᶠ k in atTop, ∀ t ∈ depths, cfg.AssignmentLevel k t := by
    apply (Filter.eventually_all_finset depths).mpr
    intro t ht
    exact h.eventually_assignment_level (lt_trans hs (hdepths t ht).1) (hdepths t ht).2
  have hnests : ∀ᶠ k in atTop, ∀ t ∈ depths, ∀ i : Fin (cfg.n k t),
      ∃ ip : Fin (cfg.n k s), cfg.A k t i ⊆ cfg.A k s ip ∧
        I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) := by
    apply (Filter.eventually_all_finset depths).mpr
    intro t ht
    exact h.eventually_nesting hs (hdepths t ht).1 (hdepths t ht).2
  filter_upwards [h.eventually_assignment_level hs (by linarith),
    h.eventually_fitted_measurable hs (by linarith), hlevels, hnests,
    h.eventually_source_pair_upper_power hs hv hvs hsU hζ hζs hgap hδ]
    with k parent hB hl hn hup ip L hL₀ hL
  obtain ⟨source, hm, hsub, hmass, hpoint⟩ := parent.exists_regular_primitive_source h ip L
    (cfg.N k ^ ζ * cfg.N k ^ (-s)) (hB ip) depths hl hn
  have hcoeff : ∀ p ∈ source, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k :=
    fun p hp => (hpoint p hp).1
  have hdefect : ∀ p ∈ source, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) :=
    fun p hp => (hpoint p hp).2.1
  have hdesc := fun p hp => (hpoint p hp).2.2
  obtain ⟨F, hF, hcard⟩ := hup ip L source hL₀ hL hsub hcoeff
    (fun p hp => hdesc p hp (s + v) hupper)
  exact ⟨⟨source, hm, hsub, hmass, hcoeff, hdefect, hdesc, F, hF, hcard⟩⟩

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
