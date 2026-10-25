/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ParameterCellCount.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.HorizontalFlow

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

def parameterCode (D : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℤ := fun i => ⌊p i / D⌋
def parameterCell (D : ℝ) (q : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  {p | parameterCode D p = q}

theorem measurableSet_parameterCell (D : ℝ) (q : Fin 2 → ℤ) :
    MeasurableSet (parameterCell D q) := by
  have hm : Measurable (parameterCode D) := by unfold parameterCode; fun_prop
  exact hm (measurableSet_singleton q)

theorem parameterCell_disjoint (D : ℝ) :
    Pairwise (fun q q' : Fin 2 → ℤ => Disjoint (parameterCell D q) (parameterCell D q')) := by
  intro q q' hne
  apply disjoint_left.mpr
  intro p hp hp'
  exact hne (hp.symm.trans hp')

theorem volume_parameterCell {D : ℝ} (hD : 0 < D) (q : Fin 2 → ℤ) :
    volume (parameterCell D q) = ENNReal.ofReal (D ^ 2) := by
  have heq : parameterCell D q = Set.univ.pi
      (fun i => Ico ((q i : ℝ) * D) (((q i : ℝ) + 1) * D)) := by
    ext p
    simp only [parameterCell, parameterCode, Set.mem_ofPred_eq, funext_iff,
      Set.mem_pi, Set.mem_univ, forall_const]
    apply forall_congr'
    intro i
    rw [Int.floor_eq_iff, le_div_iff₀ hD, div_lt_iff₀ hD]
    rfl
  rw [heq, Real.volume_pi_Ico]
  have hlength (i : Fin 2) : ((q i : ℝ) + 1) * D - (q i : ℝ) * D = D := by ring
  simp_rw [hlength]
  rw [Fin.prod_univ_two, ← ENNReal.ofReal_mul hD.le]
  congr 1
  ring

theorem parameterCell_coordinate_gap {D : ℝ} (hD : 0 < D)
    {q : Fin 2 → ℤ} {p p' : Fin 2 → ℝ}
    (hp : p ∈ parameterCell D q) (hp' : p' ∈ parameterCell D q) (i : Fin 2) :
    |p i - p' i| ≤ D := by
  have h1 := Int.floor_eq_iff.mp (congrFun hp i)
  have h2 := Int.floor_eq_iff.mp (congrFun hp' i)
  rw [le_div_iff₀ hD, div_lt_iff₀ hD] at h1 h2
  exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- Count static parameter cells meeting a tilted rectangle by its true area.
This retains the transverse squared-time scale instead of using an axis-aligned box. -/
theorem parameter_cells_in_strip {D A B m u v : ℝ} (hD : 0 < D)
    (hDA : D ≤ A) (hDB : (1 + |m|) * D ≤ B)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ q ∈ S, ∃ p ∈ parameterCell D q,
      |p 0 - u| ≤ A ∧ |p 1 - m * p 0 - v| ≤ B) :
    (S.card : ℝ) * D ^ 2 ≤ 16 * A * B := by
  have hA : 0 < A := hD.trans_le hDA
  have hB : 0 < B := lt_of_lt_of_le (by positivity : 0 < (1 + |m|) * D) hDB
  let box : Set (Fin 2 → ℝ) := Icc ![u - 2 * A, v - 2 * B] ![u + 2 * A, v + 2 * B]
  have hsub : (⋃ q ∈ S, parameterCell D q) ⊆ horizontalFibre m 0 ⁻¹' box := by
    intro z hz
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp hz
    obtain ⟨p, hpq, hp0, hp1⟩ := hS q hq
    have hgap (i : Fin 2) := parameterCell_coordinate_gap hD hzq hpq i
    have hz0 : |z 0 - u| ≤ 2 * A := (abs_sub_le _ _ _).trans (by linarith [hgap 0])
    have hg : |(z 1 - m * z 0 - v) - (p 1 - m * p 0 - v)| ≤ (1 + |m|) * D := by
      calc
        _ = |(z 1 - p 1) - m * (z 0 - p 0)| := by congr 1; ring
        _ ≤ |z 1 - p 1| + |m * (z 0 - p 0)| := abs_sub _ _
        _ ≤ D + |m| * D := by
          rw [abs_mul]
          exact add_le_add (hgap 1) (mul_le_mul_of_nonneg_left (hgap 0) (abs_nonneg _))
        _ = _ := by ring
    have hz1 : |z 1 - m * z 0 - v| ≤ 2 * B := by
      calc
        _ = |((z 1 - m * z 0 - v) - (p 1 - m * p 0 - v)) +
          (p 1 - m * p 0 - v)| := by congr 1; ring
        _ ≤ |(z 1 - m * z 0 - v) - (p 1 - m * p 0 - v)| +
          |p 1 - m * p 0 - v| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hz0' := abs_le.mp hz0
    have hz1' := abs_le.mp hz1
    constructor <;> intro i <;> fin_cases i <;> simp [box, horizontalFibre] <;> linarith
  have hvol : volume (horizontalFibre m 0 ⁻¹' box) = ENNReal.ofReal (16 * A * B) := by
    have hm : Measurable (horizontalFibre m 0) := by unfold horizontalFibre; fun_prop
    rw [← Measure.map_apply hm measurableSet_Icc, horizontalFibre_map m 0, Real.volume_Icc_pi]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : u + 2 * A - (u - 2 * A) = 4 * A := by ring
    have h1 : v + 2 * B - (v - 2 * B) = 4 * B := by ring
    rw [h0, h1, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * A)]
    congr 1
    ring
  have hv := measure_mono (μ := (volume : Measure (Fin 2 → ℝ))) hsub
  rw [measure_biUnion_finset (fun q hq q' hq' hne => parameterCell_disjoint D hne)
    (fun q _ => measurableSet_parameterCell D q), hvol] at hv
  simp only [volume_parameterCell hD, Finset.sum_const, nsmul_eq_mul] at hv
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)] at hv
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hv

end

end Submission.Obl.k4_horizontal_strict_parameter_step
