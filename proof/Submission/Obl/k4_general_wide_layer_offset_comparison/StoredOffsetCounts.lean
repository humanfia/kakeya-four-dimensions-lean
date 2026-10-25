import Submission.Obl.k4_general_wide_layer_offset_comparison.OriginalListCounts

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/StoredOffsetCounts.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Local offset counts use the FULL original fine marginal witnesses.
The original palette and physical Jacobian cancel. No floor is needed on
any later pair restriction of those witnesses. -/
theorem stored_offset_local_count
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (U : Set Ω) (E : ι → Set Ω) (S : Finset ι)
    (value coarse : Ω → ℝ) (fine : ι → Ω → ℝ) (offset : ι → ℝ)
    {a d J K H L : ℝ} (ha : 0 < a) (hJ : 0 < J) (hK : 0 < K)
    (hH : 0 < H) (hL : 1 ≤ L)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hwtop : w ≠ ⊤)
    (hcap : ∀ x Δ : ℝ, a ≤ Δ →
      μ {ω | ω ∈ U ∧ |value ω - coarse ω - x| ≤ Δ} ≤ ENNReal.ofReal (K * J * Δ ^ d) * w)
    (hE : ∀ i ∈ S, MeasurableSet (E i) ∧ E i ⊆ U)
    (hdisj : (S : Set ι).PairwiseDisjoint E)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal (J * a ^ d / H) * w ≤ μ (E i))
    (hfit : ∀ i ∈ S, ∀ ω ∈ E i, |value ω - fine i ω| ≤ L * a)
    (hcompare : ∀ i ∈ S, ∀ ω ∈ E i, |fine i ω - coarse ω - offset i| ≤ L * a)
    (x δ : ℝ) (hδ : a ≤ δ) :
    (((S.filter (fun i => |offset i - x| ≤ δ)).card : ℝ)) ≤
      K * H * (2 * L + 1) ^ d * (δ / a) ^ d := by
  classical
  have hδp : 0 < δ := ha.trans_le hδ
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  let Δ := (2 * L + 1) * δ
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have haΔ : a ≤ Δ := by dsimp [Δ]; nlinarith
  let T := S.filter (fun i => |offset i - x| ≤ δ)
  let V : Set Ω := {ω | ω ∈ U ∧ |value ω - coarse ω - x| ≤ Δ}
  have hsubset (i : ι) (hi : i ∈ T) : E i ⊆ V := by
    obtain ⟨hiS, hoff⟩ := Finset.mem_filter.mp hi
    intro ω hω
    refine ⟨(hE i hiS).2 hω, ?_⟩
    calc
      _ = |(value ω - fine i ω) + (fine i ω - coarse ω - offset i) + (offset i - x)| := by
        congr 1
        ring
      _ ≤ |value ω - fine i ω| + |fine i ω - coarse ω - offset i| + |offset i - x| :=
        abs_add_three _ _ _
      _ ≤ L * a + L * a + δ := add_le_add (add_le_add (hfit i hiS ω hω)
        (hcompare i hiS ω hω)) hoff
      _ ≤ Δ := by dsimp [Δ]; nlinarith [mul_le_mul_of_nonneg_left hδ hL0]
  have hc := card_le_from_original_witnesses μ V E T
    (by positivity : 0 < J * a ^ d / H) (by positivity : 0 < K * J * Δ ^ d)
    w hw hwtop (hcap x Δ haΔ)
    (fun i hi => ⟨(hE i (Finset.mem_filter.mp hi).1).1, hsubset i hi⟩)
    (by
      intro i hi j hj hne
      exact hdisj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hne)
    (fun i hi => hfloor i (Finset.mem_filter.mp hi).1)
  apply hc.trans_eq
  calc
    _ = K * H * (Δ ^ d / a ^ d) := by field_simp
    _ = K * H * (2 * L + 1) ^ d * (δ / a) ^ d := by
      dsimp [Δ]
      rw [Real.mul_rpow (by positivity : 0 ≤ 2 * L + 1) hδp.le,
        Real.div_rpow hδp.le ha.le]
      ring

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
