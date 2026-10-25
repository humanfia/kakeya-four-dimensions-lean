/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/MovingGraphCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Lib.K4MovingMeshBoxes.Geometry
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4MovingMeshBoxes

/-- A graph center that varies by at most one scalar width inside a base mesh cell
can be retained when integrating the original joint caps over a moving box. -/
theorem moving_graph_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 3 → ℝ) (x h : Ω → ℝ) (condition : Ω → Prop)
    {delta a radius L C : ℝ} (hd : 0 < delta) (ha : 0 < a)
    (hdr : delta ≤ radius) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, delta ≤ width i)
    (hmove : ∀ i, L * delta ≤ width i)
    (g : (Fin 3 → ℤ) → ℝ)
    (happrox : ∀ p, z p ∈ movingBox time radius center velocity width → condition p →
      |h p - g (baseMesh delta (z p))| ≤ a)
    (hcell : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh delta (z p) = q ∧ ⌊x p / a⌋ = j ∧ condition p} ≤
        ENNReal.ofReal (C * delta ^ 3)) :
    μ {p | z p ∈ movingBox time radius center velocity width ∧
      |x p - h p| ≤ a ∧ condition p} ≤
        ENNReal.ofReal (4200 * C * radius * width 0 * width 1) := by
  classical
  let box := movingBox time radius center velocity width
  let event : Ω → Prop := fun p => z p ∈ box ∧ |x p - h p| ≤ a ∧ condition p
  let F : Finset ℤ := Finset.Icc (-3) 3
  have hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh delta (z p) = q ∧ event p} ≤ ENNReal.ofReal ((7 * C) * delta ^ 3) := by
    intro q
    have hsub : {p | baseMesh delta (z p) = q ∧ event p} ⊆
        ⋃ j ∈ F, {p | baseMesh delta (z p) = q ∧
          ⌊x p / a⌋ = ⌊g q / a⌋ + j ∧ condition p} := by
      rintro p ⟨hpq, hpbox, hpfit, hpcond⟩
      have hfit : |x p - g q| ≤ 2 * a := by
        have hg := happrox p hpbox hpcond
        rw [hpq] at hg
        linarith [abs_sub_le (x p) (h p) (g q)]
      have hoff := Submission.Obl.k4_fixed_budget_quadratic_recovery.floor_offset_mem ha hfit
      have hoff' : ⌊x p / a⌋ - ⌊g q / a⌋ ∈ F := by simpa [F] using hoff
      exact mem_iUnion₂.mpr ⟨⌊x p / a⌋ - ⌊g q / a⌋, hoff', hpq, by omega, hpcond⟩
    calc
      _ ≤ μ (⋃ j ∈ F, {p | baseMesh delta (z p) = q ∧
          ⌊x p / a⌋ = ⌊g q / a⌋ + j ∧ condition p}) := measure_mono hsub
      _ ≤ ∑ j ∈ F, μ {p | baseMesh delta (z p) = q ∧
          ⌊x p / a⌋ = ⌊g q / a⌋ + j ∧ condition p} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ F, ENNReal.ofReal (C * delta ^ 3) :=
        Finset.sum_le_sum (fun j _ => hcell q (⌊g q / a⌋ + j))
      _ = ENNReal.ofReal ((7 * C) * delta ^ 3) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        norm_num [F]
        ring
  have hbound := measure_movingBox_of_cell_cap μ z event hd hdr hL
    (mul_nonneg (by norm_num) hC) time center velocity width hv hdw hmove hcap
  have hset : {p | z p ∈ box ∧ event p} =
      {p | z p ∈ box ∧ |x p - h p| ≤ a ∧ condition p} := by
    ext p
    simp only [mem_ofPred_eq, event, and_self_left]
  rw [hset] at hbound
  convert hbound using 1
  congr 1
  ring

end Submission.Obl.k4_horizontal_strict_parameter_step
