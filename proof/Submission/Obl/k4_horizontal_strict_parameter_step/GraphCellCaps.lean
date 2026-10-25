/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/GraphCellCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.MeshJitter
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- Inside one fine base cell, a graph band meets at most seven scalar cells.
The original joint cap retains every auxiliary event, including the palette bin. -/
theorem graph_base_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (x : Ω → ℝ) (condition : Ω → Prop)
    {δ a C : ℝ} (ha : 0 < a) (g : (Fin 3 → ℤ) → ℝ)
    (hfit : ∀ᵐ p ∂μ, condition p → |x p - g (baseMesh δ (Z p))| ≤ 2 * a)
    (hcell : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh δ (Z p) = q ∧ ⌊x p / a⌋ = j ∧ condition p} ≤
        ENNReal.ofReal (C * δ ^ 3)) (q : Fin 3 → ℤ) :
    μ {p | baseMesh δ (Z p) = q ∧ condition p} ≤
      ENNReal.ofReal (7 * C * δ ^ 3) := by
  let F : Finset ℤ := Finset.Icc (-3) 3
  have hsub : {p | baseMesh δ (Z p) = q ∧ condition p} ≤ᵐ[μ]
      ⋃ j ∈ F, {p | baseMesh δ (Z p) = q ∧ ⌊x p / a⌋ = ⌊g q / a⌋ + j ∧ condition p} := by
    filter_upwards [hfit] with p hp he
    have hh := hp he.2
    rw [he.1] at hh
    have hoff := Submission.Obl.k4_fixed_budget_quadratic_recovery.floor_offset_mem ha hh
    exact mem_iUnion₂.mpr ⟨⌊x p / a⌋ - ⌊g q / a⌋, (by simpa [F] using hoff), he.1, by omega, he.2⟩
  calc
    _ ≤ μ (⋃ j ∈ F, {p | baseMesh δ (Z p) = q ∧
        ⌊x p / a⌋ = ⌊g q / a⌋ + j ∧ condition p}) := measure_mono_ae hsub
    _ ≤ ∑ j ∈ F, μ {p | baseMesh δ (Z p) = q ∧
        ⌊x p / a⌋ = ⌊g q / a⌋ + j ∧ condition p} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ F, ENNReal.ofReal (C * δ ^ 3) := Finset.sum_le_sum (fun j _ => hcell q _)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      norm_num [F]
      ring

/-- A tested jitter event is charged under its original pre-jitter event.
The cell mass is unchanged and all new points stay in the same cell. -/
theorem meshJitter_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (F : Finset (Fin 3 → ℤ))
    (A : Set Ω) (hA : MeasurableSet A) (B : Set (Fin 3 → ℝ)) (hB : MeasurableSet B)
    (htransport : ∀ᵐ p ∂μ, ∀ z, baseMesh δ z = baseMesh δ (Z p) → z ∈ B → p ∈ A) :
    meshJitter δ F (fun q => μ {p | baseMesh δ (Z p) = q}) B ≤ μ A := by
  rw [meshJitter_apply δ F _ hB]
  have hterm (q : Fin 3 → ℤ) :
      (μ {p | baseMesh δ (Z p) = q} / ENNReal.ofReal (δ ^ 3)) *
        volume (B ∩ meshBox δ q) ≤ μ ({p | baseMesh δ (Z p) = q} ∩ A) := by
    rcases (B ∩ meshBox δ q).eq_empty_or_nonempty with hempty | ⟨z, hzB, hzq⟩
    · simp only [hempty, measure_empty, mul_zero]
      exact zero_le
    · have hsame : μ {p | baseMesh δ (Z p) = q} =
          μ ({p | baseMesh δ (Z p) = q} ∩ A) := by
        apply measure_congr
        filter_upwards [htransport] with p hp
        apply propext
        constructor
        · intro hpq
          exact ⟨hpq, hp z (hzq.trans hpq.symm) hzB⟩
        · exact fun hpq => hpq.1
      calc
        _ ≤ (μ {p | baseMesh δ (Z p) = q} / ENNReal.ofReal (δ ^ 3)) *
            volume (meshBox δ q) := mul_le_mul_of_nonneg_left (measure_mono inter_subset_right) zero_le
        _ = μ {p | baseMesh δ (Z p) = q} := by
          rw [volume_meshBox hδ, ENNReal.div_mul_cancel]
          · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
          · exact ENNReal.ofReal_ne_top
        _ = _ := hsame
  calc
    _ ≤ ∑ q ∈ F, μ ({p | baseMesh δ (Z p) = q} ∩ A) :=
      Finset.sum_le_sum (fun q _ => hterm q)
    _ = μ (⋃ q ∈ F, {p | baseMesh δ (Z p) = q} ∩ A) := by
      symm
      apply measure_biUnion_finset
      · intro q hq q' hq' hne
        apply disjoint_left.mpr
        rintro p ⟨hp, _⟩ ⟨hp', _⟩
        exact hne (hp.symm.trans hp')
      · intro q hq
        exact ((measurable_baseMesh δ).comp hZ (measurableSet_singleton q)).inter hA
    _ ≤ μ A := measure_mono (by
      intro p hp
      obtain ⟨q, hq, hp⟩ := mem_iUnion₂.mp hp
      exact hp.2)

end

end Submission.Obl.k4_horizontal_strict_parameter_step
