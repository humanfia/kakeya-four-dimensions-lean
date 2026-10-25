/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/FiniteWidthGrid.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeAssignments

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- Only finitely many dyadic widths above the preparation floor are needed.
Every real requested width is comparable with one of these coarser widths. -/
theorem exists_finite_dyadic_width_grid {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ J : ℕ, ∀ w : ℝ, ζ ≤ w → w ≤ 1 →
      ∃ j : Fin (J + 1), ζ ≤ (1 / 2 : ℝ) ^ (j : ℕ) ∧
        w ≤ (1 / 2 : ℝ) ^ (j : ℕ) ∧ (1 / 2 : ℝ) ^ (j : ℕ) < 2 * w := by
  obtain ⟨J, hJ, -⟩ := exists_nat_pow_near_of_lt_one hζ hζ1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨J, ?_⟩
  intro w hw hw1
  obtain ⟨j, hj, hwj⟩ := exists_nat_pow_near_of_lt_one (hζ.trans_le hw) hw1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hjJ : j ≤ J := by
    by_contra hn
    have hpow : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ (J + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  refine ⟨⟨j, by omega⟩, hw.trans hwj, hwj, ?_⟩
  rw [pow_succ] at hj
  linarith

namespace NativeModel

open Submission.Obl.k4_critical_derivative_evaluation_lists

/-- At a fixed sample, finitely many native levels have a common measurable
full-measure coverage event, even if the finite grid was chosen from that sample. -/
theorem finite_assignment_cover {α : Type} [MeasurableSpace α] (cfg : NativeModel α)
    {k : ℕ} {J : ℕ} (s : Fin J → ℝ) (a : ∀ j, cfg.AssignmentLevel k (s j)) :
    ∃ G : Set (α × ℝ), MeasurableSet G ∧ (∀ᵐ p ∂cfg.μ k, p ∈ G) ∧
      ∀ p ∈ G, ∀ j : Fin J, ∃ i, p.1 ∈ cfg.B k (s j) i ∧
        p.2 ∈ Data.I (cfg.T k (s j)) (cfg.j k (s j) i) := by
  let G : Set (α × ℝ) := ⋂ j : Fin J,
    ⋃ i : Fin (cfg.n k (s j)), cfg.B k (s j) i ×ˢ Data.I (cfg.T k (s j)) (cfg.j k (s j) i)
  have hG : MeasurableSet G := MeasurableSet.iInter fun j =>
    MeasurableSet.iUnion fun i => ((a j).fitted_measurable i).prod measurableSet_Icc
  have hcover : ∀ᵐ p ∂cfg.μ k, ∀ j : Fin J, ∃ i, p.1 ∈ cfg.B k (s j) i ∧
      p.2 ∈ Data.I (cfg.T k (s j)) (cfg.j k (s j) i) :=
    ae_all_iff.mpr (fun j => (a j).covers)
  refine ⟨G, hG, ?_, ?_⟩
  · filter_upwards [hcover] with p hp
    exact mem_iInter.mpr (fun j => by
      obtain ⟨i, hi, hit⟩ := hp j
      exact mem_iUnion.mpr ⟨i, hi, hit⟩)
  · intro p hp j
    obtain ⟨i, hi, ht⟩ := mem_iUnion.mp (mem_iInter.mp hp j)
    exact ⟨i, hi, ht⟩

end NativeModel

end Submission.Obl.k4_horizontal_strict_parameter_step
