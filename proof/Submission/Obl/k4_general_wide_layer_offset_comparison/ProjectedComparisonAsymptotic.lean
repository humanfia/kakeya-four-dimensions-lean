import Submission.Obl.k4_general_wide_layer_offset_comparison.WideProjectedComparison
import Submission.Obl.k4_general_wide_layer_offset_comparison.BoundedMeshTables
import Submission.Obl.k4_profile_density_bounds.Asymptotics

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedComparisonAsymptotic.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Uniformly over all actual raw comparison frames, matching excludes a
fixed power of original-source bad mass at the prescribed wide threshold.
The finite smoothing table is constructed from the actual bounded base. -/
theorem eventually_wide_comparison_bad_small (hp : p.Valid)
    (hM : Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Matching)
    {sc sf m u : ℝ} (hu : 0 < u) (hgap : sf - sc ≤ u)
    (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k) (hKH : ∀ k, p.K k ≤ H k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ h g b : ℝ, ∀ σ : Measure (α × ℝ),
      ∀ f : ProjectedComparisonFrame p k sc sf m (H k) h g b σ,
        σ (f.bad (4 * H k * p.N k ^ (-sc) * p.N k ^ (10 / (1 - p.d) * u))) ≤
          ENNReal.ofReal (p.N k ^ (-c)) := by
  have hd₀ : 0 ≤ (1 + p.d) / 2 := by linarith [hp.dimension_nonneg]
  have hd₁ : (1 + p.d) / 2 < 1 := by linarith [hp.dimension_lt_one]
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmb⟩ := matching_unnormalized hM _ hd₀ hd₁
  obtain ⟨J⟩ := nonempty_jetData
  let ε := ε₀ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεε₀ : ε ≤ ε₀ := by dsimp [ε]; linarith
  let a := 10 / (1 - p.d) * u
  have ha : 0 < a := mul_pos (div_pos (by norm_num) (sub_pos.mpr hp.dimension_lt_one)) hu
  have haε : 0 < a * ε := mul_pos ha hε
  let c := a * ε / 2
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.scale k]
  have hsmall := eventually_subpower_mul_rpow_lt hN1 hp.scale_limit hH hsub 1
    (show (0 : ℝ) < u from hu) (show (0 : ℝ) ≤ 4 by norm_num)
  have hRlarge := eventually_const_mul_rpow_lt hp.scale_limit ha R₀
  have hClarge := eventually_const_mul_rpow_lt hp.scale_limit haε (3 * J.C₂)
  have hdecay := eventually_subpower_mul_rpow_lt hN1 hp.scale_limit hH hsub 6
    (show -(a * ε) < -c by dsimp [c]; linarith)
    (comparisonJetConstant_nonneg J hε)
  filter_upwards [hsmall, hRlarge, hClarge, hdecay] with k hk hRk hCk hdk
  intro h g b σ f
  have hNp : 0 < p.N k := by linarith [hp.scale k]
  have hsmallk : 4 * H k ≤ p.N k ^ u := by
    simpa only [pow_one, Real.rpow_zero, mul_one] using hk.le
  have hRk' : R₀ ≤ p.N k ^ a := by simpa only [Real.rpow_zero, mul_one] using hRk.le
  have hCk' : 3 * J.C₂ ≤ (p.N k ^ a) ^ ε := by
    rw [← Real.rpow_mul hNp.le]
    simpa only [Real.rpow_zero, mul_one] using hCk.le
  obtain ⟨Q, hQ⟩ := exists_ae_mesh_table σ (p.normalizedDomainBase k h g b) f.mesh_pos
    (show (0 : ℝ) ≤ 1 / 8 by norm_num)
    (Eventually.of_forall (p.normalizedDomainBase_inner f.time_pos f.slope_pos f.width_pos f.domain_motion))
  have hb := f.wide_bad_mass_le hp (hKH k) hu hgap hsmallk (le_refl (p.N k ^ a))
    Q hQ J hmb hR₀ hε hεε₀ hRk' hCk'
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_mul hNp.le, show a * (-ε) = -(a * ε) by ring]
  exact hdk.le

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
