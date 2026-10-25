-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.DensityPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/DensityPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- The uniform path budget and half-mass argument are adapted from this LOT
tree, o265, x0943 branch 3cd2e161,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/Preparation.lean.
That file credits o204/x0749 e4d9e4b8c9b3, Native/Preparation.lean, and
o116/x0389 e3859a9b, Preparation.lean. The finite density preparation itself
is imported from accepted o214, rather than copied. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Obl.k4_uncapped_native_capping.UWE.DensityPreparedLaw
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

namespace DensityPreparation

abbrev Problem := Submission.Obl.k4_uncapped_native_capping.UWE.Problem

/-- The existing exact-problem API has the same original-law predicate as
this obligation. -/
theorem valid_iff (p : Problem) (S η : ℝ) :
    p.Valid S η ↔ pb p.N p.K p.L p.d S η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G := Iff.rfl

/-- Power-small deletion is uniform over every subsequently supplied path
factor below one fixed small power. The exponent is fixed before the path. -/
theorem uniform_path_budget {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {bad : ℕ → ENNReal} (hbad : IsPowerSmall N bad) {D : ℝ} (hD : 0 < D) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ κ : ℝ,
      1 ≤ κ → κ ≤ N k ^ σ → bad k ≤ ENNReal.ofReal (κ⁻¹ / D) := by
  obtain ⟨c, hc, hbad⟩ := hbad
  refine ⟨c / 2, by positivity, ?_⟩
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show -c < -(c / 2) by linarith) D
  filter_upwards [hbad, hsmall, hN.eventually (eventually_gt_atTop (0 : ℝ))]
    with k hk hsmall hNk
  intro κ hκ hκN
  have hκpos : 0 < κ := by linarith
  have hinv : N k ^ (-(c / 2)) ≤ κ⁻¹ := by
    rw [Real.rpow_neg hNk.le]
    simpa only [one_div] using one_div_le_one_div_of_le hκpos hκN
  apply hk.trans
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hsmall.le.trans hinv)

/-- Half-mass pruning in the unchanged original world mixture. -/
theorem remove_half {Γ X : Type*} [Fintype Γ] [MeasurableSpace X]
    (μ : Γ → Measure X) (weight : Γ → ENNReal) (H bad : Γ → Set X)
    {a : ℝ} (ha : 0 ≤ a)
    (hH : ENNReal.ofReal a ≤ ∑ w, weight w * μ w (H w))
    (hbad : (∑ w, weight w * μ w (bad w)) ≤ ENNReal.ofReal (a / 2)) :
    ENNReal.ofReal (a / 2) ≤ ∑ w, weight w * μ w (H w \ bad w) := by
  have hcover (w : Γ) : H w ⊆ (H w \ bad w) ∪ bad w := by
    intro p hp
    by_cases hb : p ∈ bad w
    · exact Or.inr hb
    · exact Or.inl ⟨hp, hb⟩
  have hbound : ENNReal.ofReal a ≤
      (∑ w, weight w * μ w (H w \ bad w)) + ENNReal.ofReal (a / 2) := by
    calc
      _ ≤ ∑ w, weight w * μ w (H w) := hH
      _ ≤ ∑ w, weight w * (μ w (H w \ bad w) + μ w (bad w)) := by
        apply Finset.sum_le_sum
        intro w hw
        exact mul_le_mul_of_nonneg_left
          ((measure_mono (hcover w)).trans (measure_union_le _ _)) zero_le
      _ = (∑ w, weight w * μ w (H w \ bad w)) + ∑ w, weight w * μ w (bad w) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl hbad
  have hsplit : ENNReal.ofReal a = ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hsplit] at hbound
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hbound

/-- Simultaneous pure and angular density masks may be prepared before a
supplied path and before choosing the residual. Their pointwise bounds and
remaining mass use the original product measures. -/
theorem fixed_masks {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (R A : Finset ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L)
    (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L) {τ : ℝ} (hτ : 0 < τ) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ κ : ℝ,
      1 ≤ κ → κ ≤ p.N k ^ σ →
      ∀ H : Fin (p.W k) → Set Ev,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ p.E k w) →
      ENNReal.ofReal (κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (p.ω k w) * ((p.ν k w).prod volume) (H w) →
      ∃ F : Fin (p.W k) → Set Ev,
        (∀ w, MeasurableSet (F w) ∧ F w ⊆ H w) ∧
        (∀ w z, z ∈ F w → ∀ r ∈ insert p.L R,
          ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ≤ p.g k w r (obs (p.B k w) (δ (p.N k) r) z) ∧
          p.g k w r (obs (p.B k w) (δ (p.N k) r) z) ≤ ENNReal.ofReal (p.N k ^ (-p.f r + τ))) ∧
        (∀ w z, z ∈ F w → ∀ u ∈ A,
          p.G k w u (obs (p.B k w) (δ (p.N k) p.L) z, fun j => ⌊v z.1 j / δ (p.N k) u⌋) ≤
            ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ)) *
              p.g k w p.L (obs (p.B k w) (δ (p.N k) p.L) z)) ∧
        ENNReal.ofReal (κ⁻¹ / 4) ≤
          ∑ w, ENNReal.ofReal (p.ω k w) * ((p.ν k w).prod volume) (F w) := by
  classical
  let bad := Submission.Obl.k4_uncapped_native_capping.UWE.densityPreparationBad p S R A τ
  have hbad := hp.finite_density_preparation R A hR hA hτ
  obtain ⟨σ, hσ, hbudget⟩ := uniform_path_budget hp.2.1 hbad (by norm_num : (0 : ℝ) < 4)
  refine ⟨σ, hσ, hbudget.mono ?_⟩
  intro k hk κ hκ hκN H hH hmass
  let F : Fin (p.W k) → Set Ev := fun w => H w \ bad k w
  have hbadMeas w : MeasurableSet (bad k w) :=
    hp.measurableSet_densityPreparationBad R A hR hA τ k w
  have hF w : MeasurableSet (F w) ∧ F w ⊆ H w :=
    ⟨(hH w).1.diff (hbadMeas w), sdiff_subset⟩
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro w z hz r hr
    exact p.pure_density_band_of_not_bad S R A τ k w z hz.2 hr
  · intro w z hz u hu
    exact p.angular_ratio_of_not_bad S R A τ k w (by linarith [hp.1 k]) z hz.2 hu
  · have hHmeasure w : p.incidenceMeasure k w (H w) = ((p.ν k w).prod volume) (H w) := by
      rw [Submission.Obl.k4_uncapped_native_capping.UWE.Problem.incidenceMeasure,
        Measure.restrict_apply (hH w).1,
        inter_eq_left.mpr (hH w).2]
    have hFmeasure w : p.incidenceMeasure k w (F w) = ((p.ν k w).prod volume) (F w) := by
      rw [Submission.Obl.k4_uncapped_native_capping.UWE.Problem.incidenceMeasure,
        Measure.restrict_apply (hF w).1,
        inter_eq_left.mpr ((hF w).2.trans (hH w).2)]
    have hkeep := remove_half (fun w => p.incidenceMeasure k w)
      (fun w => ENNReal.ofReal (p.ω k w)) H (bad k) (a := κ⁻¹ / 2)
      (by positivity) (by simpa only [hHmeasure] using hmass)
      (by simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hk κ hκ hκN)
    simpa only [F, hFmeasure, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hkeep

end DensityPreparation

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
