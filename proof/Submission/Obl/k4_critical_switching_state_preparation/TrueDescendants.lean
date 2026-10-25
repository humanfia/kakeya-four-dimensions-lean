/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/TrueDescendants.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/TrueDescendants.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.OriginalMass
import Submission.Obl.k4_critical_switching_state_preparation.DescendantCount

namespace Submission.Obl.k4_critical_switching_state_preparation

open MeasureTheory Set Finset
open scoped ENNReal BigOperators

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Inclusion of actual dyadic blocks forces the corresponding order of time depths. -/
theorem time_depth_le_of_block_subset {T Tp : ℕ}
    (j : Fin (2 ^ T)) (jp : Fin (2 ^ Tp)) (hsub : I T j ⊆ I Tp jp) : Tp ≤ T := by
  have hvol := measure_mono (μ := (volume : Measure ℝ)) hsub
  change volume (Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I T j) ≤
    volume (Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I Tp jp) at hvol
  rw [Submission.Obl.k4_scalar_angular_pair_agreement.volume_I,
    Submission.Obl.k4_scalar_angular_pair_agreement.volume_I] at hvol
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2 : ℝ) ^ T)⁻¹),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2 : ℝ) ^ Tp)⁻¹)] at hreal
  have hpow := (inv_le_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ T)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ Tp)).mp hreal
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow

/-- Frozen true-level floors imply the critical descendant count, with no
floor requirement on any later restriction of the incidence measure. -/
theorem AssignmentLevel.true_descendant_count (h : cfg.Valid) {k : ℕ} {s t : ℝ}
    (parent : cfg.AssignmentLevel k s) (child : cfg.AssignmentLevel k t)
    (ip : Fin (cfg.n k s)) (S : Finset (Fin (cfg.n k t)))
    (hsub : ∀ i ∈ S, cfg.A k t i ⊆ cfg.A k s ip)
    (htime : ∀ i ∈ S,
      I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip)) :
    (S.card : ℝ) ≤ cfg.K k ^ 4 *
      ((2 : ℝ) ^ cfg.T k t / (2 : ℝ) ^ cfg.T k s) ^ 4 *
      (cfg.N k ^ (-s) / cfg.N k ^ (-t)) ^ cfg.d := by
  classical
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  by_cases hS : S.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hS
    have hT := time_depth_le_of_block_subset _ _ (htime i₀ hi₀)
    let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
    have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
    have hbound := critical_descendant_count (cfg.ν k) S hT (cfg.j k s ip)
      (cfg.j k t) (cfg.A k t) (cfg.A k s ip) (fun i _ => child.measurable i)
      (fun i _ i' _ hne hj => child.disjoint i i' hne hj) hsub htime
      (cfg.N k ^ (-t)) (cfg.N k ^ (-s)) cfg.d (cfg.K k ^ 2)
      (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _) (by positivity)
      (parent.critical_prior_bounds h ip).2 (by
        intro i hi
        calc
          _ ≤ ENNReal.ofReal ((cfg.ν k).real (cfg.A k t i)) :=
            ENNReal.ofReal_le_ofReal (child.critical_prior_bounds h i).1
          _ = _ := ENNReal.ofReal_toReal (measure_ne_top (cfg.ν k) _))
    convert hbound using 1 <;> ring
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hzero]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
