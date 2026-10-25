/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/ConcreteRates.lean.
-/

import Submission.Obl.k4_scalar_linear_critical_extremizers.ConcreteCritical

set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_linear_critical_extremizers.Split

open Set Filter
open scoped Topology

noncomputable section

def classDimension (S₀ η : ℝ) : ℝ := criticalDimension (AngularClass S₀ η) d Horizon
def classRate (S₀ η : ℝ) : ℝ → ℝ := extremalRate (AngularClass S₀ η) d L Horizon
def classCriticalRate (S₀ η : ℝ) : ℝ := criticalRate (classRate S₀ η) (classDimension S₀ η)

theorem class_horizon_bound (hinit : Initial) (S₀ η : ℝ) (p : Code)
    (hp : AngularClass S₀ η p) : 0 < L p ∧ Horizon p ≤ L p :=
  ⟨exact_length_pos hp.1, horizon_le_length_of_initial hinit hp.1⟩

theorem class_rate_nonempty (S₀ η : ℝ)
    (hne : (badDimensions (AngularClass S₀ η) d Horizon).Nonempty)
    {D' : ℝ} (hD : classDimension S₀ η < D') :
    (horizonRates (AngularClass S₀ η) d L Horizon D').Nonempty := by
  obtain ⟨p, hp, hdim, hH⟩ := exists_bad_below_cap _ _ _ hne hD
  exact ⟨Horizon p / L p, p, hp, hdim.le, rfl⟩

/-- The terminal-extension constant can be fixed on one neighborhood of
the critical density, and gives a uniform positive bound for all larger
density-cap rates by working in the smaller of the two classes. -/
theorem class_rates_uniformly_positive (hinit : Initial) (hcalc : WeakCalculus) (hext : Extension)
    (S₀ η : ℝ) (hS : 0 < S₀) (hη : 0 < η)
    (hne : (badDimensions (AngularClass S₀ η) d Horizon).Nonempty) :
    ∃ α : ℝ, 0 < α ∧ ∀ D' ∈ Ioo (classDimension S₀ η) 1, α ≤ classRate S₀ η D' := by
  let dstar := classDimension S₀ η
  have hstar₀ : 0 ≤ dstar := criticalDimension_nonneg _ _ _ hne
  have hstar₁ : dstar < 1 := criticalDimension_lt_one _ _ _ hne
  let dmax := (dstar + 1) / 2
  have hmax₀ : 0 ≤ dmax := by dsimp [dmax]; linarith
  have hmax₁ : dmax < 1 := by dsimp [dmax]; linarith
  have hstarmax : dstar < dmax := by dsimp [dmax]; linarith
  obtain ⟨C, c, hC, hc, hExtension⟩ := hext dmax S₀ η hmax₀ hmax₁ hS hη
  refine ⟨3 / (4 * C), by positivity, ?_⟩
  intro D' hD
  let cap := min D' dmax
  have hstarcap : dstar < cap := lt_min hD.1 hstarmax
  obtain ⟨p, hp, hpcap, hpH⟩ := exists_bad_below_cap _ _ _ hne hstarcap
  let Q := {q : Code // AngularClass S₀ η q ∧ d q ≤ cap}
  refine positive_rate_of_terminal_extension
    (P := Q) (costs := fun q => {h : ℝ | Cost q.1 h}) (length := fun q => L q.1)
    (C := C) (c := c) (k := classRate S₀ η D') hC hc
    (fun _ _ hh => hh.1) ?_ ?_ ⟨p, hp, hpcap.le⟩
    ⟨L p, hinit p hp.1⟩ hpH
  · intro q
    refine ⟨exact_length_pos q.2.1.1, ?_⟩
    exact horizon_le_extremalRate_mul _ _ _ _ (class_horizon_bound hinit S₀ η)
      q.2.1 (q.2.2.trans (min_le_left _ _))
  · intro q h e hh he heh hec
    have hqdmax : d q.1 ≤ dmax := q.2.2.trans (min_le_right _ _)
    obtain ⟨r, hr₀, hrL, hrem, hKnown⟩ :=
      hExtension q.1 q.2.1.1 hqdmax q.2.1.2.1 q.2.1.2.2 h e
        (he.trans heh) hh he heh hec
    obtain ⟨q', hq', hq'L, hq'd, hq'S, hq'U, hH, hprof, heq⟩ :=
      hcalc.2.2 q.1 r (L q.1) (h - e) (d q.1) q.2.1.1 hr₀.le hrL hrL.le le_rfl
        (exact_dimension_bounds q.2.1.1).1 (exact_dimension_bounds q.2.1.1).2
        (fun s hrs hsL => exact_terminal_cap q.2.1.1 s (hr₀.le.trans hrs) hsL) hKnown
    have hq'class : AngularClass S₀ η q' := by
      refine ⟨hq', hq'S.trans q.2.1.2.1, ?_⟩
      rw [hq'U, q.2.1.2.2, hq'L]
      field_simp [(exact_length_pos q.2.1.1).ne']
    refine ⟨⟨q', hq'class, hq'd ▸ q.2.2⟩, ?_, hH⟩
    simpa only [hq'L] using hrem

theorem class_critical_rate_bounds (hinit : Initial) (hcalc : WeakCalculus) (hext : Extension)
    (S₀ η : ℝ) (hS : 0 < S₀) (hη : 0 < η)
    (hne : (badDimensions (AngularClass S₀ η) d Horizon).Nonempty) :
    0 < classCriticalRate S₀ η ∧ classCriticalRate S₀ η ≤ 1 := by
  have hstar : classDimension S₀ η < 1 := criticalDimension_lt_one _ _ _ hne
  obtain ⟨α, hα, hlower⟩ := class_rates_uniformly_positive hinit hcalc hext S₀ η hS hη hne
  have hnonneg (D' : ℝ) (hD : D' ∈ Ioo (classDimension S₀ η) 1) :
      0 ≤ classRate S₀ η D' := hα.le.trans (hlower D' hD)
  refine ⟨criticalRate_pos hstar hα hlower, ?_⟩
  obtain ⟨D', hD⟩ := exists_between hstar
  apply (criticalRate_le hnonneg hD).trans
  exact extremalRate_le_one _ _ _ _ (class_horizon_bound hinit S₀ η)
    (class_rate_nonempty S₀ η hne hD.1)

end

end Submission.Obl.k4_scalar_linear_critical_extremizers.Split
