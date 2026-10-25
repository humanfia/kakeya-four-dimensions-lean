-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.AngularBinMenus
import Submission.Lib.K4AngularCharge.AngularCharge

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4AngularCharge

open scoped ENNReal

noncomputable section

/-- Original angular density and original label-share floors give the
palette numerator for a major axis in any orientation. The reference
mass remains the full original label mass. -/
theorem linear_native_palette_cap {Ω O : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace O] [MeasurableEq O]
    (μ : Measure Ω) [IsFiniteMeasure μ] (obs : Ω → O) (hobs : Measurable obs)
    (velocity : Ω → EuclideanSpace ℝ (Fin 2)) (fine : ℝ)
    (hcell : Measurable (fun z => fun e : Fin 2 => ⌊velocity z e / fine⌋))
    (lam : Measure O) [SigmaFinite lam] (g : O → ℝ≥0∞) (hg : Measurable g)
    (hmap : μ.map obs = lam.withDensity g)
    (G : O × (Fin 2 → ℤ) → ℝ≥0∞) (hG : Measurable G)
    (hmapG : μ.map (fun z => (obs z, fun e : Fin 2 => ⌊velocity z e / fine⌋)) =
      (lam.prod Measure.count).withDensity G)
    (F : Set Ω) (hF : MeasurableSet F) (θ α β : ℝ≥0∞) (hθ : θ ≠ 0) (hβ : β ≠ 0)
    (b : Ω → Fin 2 → ℝ) (offset : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (H a : ℝ) (hH : 0 ≤ H) (ha : 0 < a) (hf : 0 < fine) (haf : a ≤ fine)
    (hmajor : ∀ e, |M e 0| ≤ H) (hminor : ∀ e, |M e 1| ≤ a)
    (hcoord : ∀ z ∈ F, ∀ e, velocity z e = offset e + ∑ i, M e i * b z i)
    (hbound : ∀ z ∈ F, |b z 1| ≤ H) (j : ℤ) :
    μ (F ∩ {z | θ ≤ labelShare μ obs F z} ∩
        {z | G (obs z, fun e : Fin 2 => ⌊velocity z e / fine⌋) ≤ α ∧ β ≤ g (obs z)} ∩
        {z | ⌊b z 0 / a⌋ = j}) ≤
      ENNReal.ofReal ((6 * H + 2) ^ 2) * (((α / β) / θ) * μ F) := by
  classical
  let cell : Ω → Fin 2 → ℤ := fun z e => ⌊velocity z e / fine⌋
  let D := F ∩ {z | θ ≤ labelShare μ obs F z} ∩
    {z | G (obs z, cell z) ≤ α ∧ β ≤ g (obs z)}
  let U := D ∩ {z | ⌊b z 0 / a⌋ = j}
  obtain ⟨V, hV, hmem⟩ := linear_velocity_bin_menu velocity b U offset M H a fine j
    hH ha hf haf hmajor hminor
    (fun z hz e => hcoord z hz.1.1.1 e) (fun z hz => hz.2)
    (fun z hz => hbound z hz.1.1.1)
  have hsub : U ⊆ ⋃ c ∈ V, D ∩ {z | cell z = c} := by
    intro z hz
    simp only [mem_iUnion, exists_prop]
    exact ⟨cell z, hmem z hz, hz.1, rfl⟩
  calc
    _ ≤ ∑ c ∈ V, μ (D ∩ {z | cell z = c}) :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _c ∈ V, ((α / β) / θ) * μ F := by
      apply Finset.sum_le_sum
      intro c hc
      exact label_conditional_cap μ obs hobs cell hcell lam g hg hmap G hG hmapG hF θ α β hθ hβ c
    _ = (V.card : ℝ≥0∞) * (((α / β) / θ) * μ F) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hV

end
end Submission.Obl.k4_finite_affine_parent_sources
