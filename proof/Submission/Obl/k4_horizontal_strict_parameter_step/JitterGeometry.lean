/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/JitterGeometry.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.HorizontalFlow
import Submission.Obl.k4_horizontal_strict_parameter_step.ReconstructionMesh
import Submission.Lib.K4AffineMeshCaps.Saturation

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

def physicalBase (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4]

theorem reconstructBase_line (b : Fin 6 → ℝ) (v t : ℝ) :
    reconstructBase v (physicalBase b t) =
      ![t, b 0 + t * (b 3 - v), b 1 + t * (b 4 + b 0) + t ^ 2 * (b 3 - v)] := by
  ext i
  fin_cases i <;> simp [physicalBase, reconstructBase] <;> ring

/-- Both graphs can be evaluated at any shared jitter point, not merely at
one chosen representative of its physical base cell. -/
theorem reconstructBase_jitter {b : Fin 6 → ℝ} {v t δ χ K : ℝ} {z : Fin 3 → ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hvel : |b 3 - v| ≤ χ) (hdef : |b 4 + b 0| ≤ χ) (hχ1 : χ ≤ 1)
    (hb : |b 0| ≤ K) (hv : |v| ≤ K)
    (hcell : baseMesh δ z = baseMesh δ (physicalBase b t)) :
    |z 0 - t| ≤ δ ∧ |z 0| ≤ 2 ∧
      |reconstructBase v z 1 - b 0| ≤ χ + (K + 1) * δ ∧
      |reconstructBase v z 2 - b 1| ≤ 2 * χ + (3 * K + 4) * δ := by
  let w := physicalBase b t
  have hd (i : Fin 3) : |z i - w i| ≤ δ :=
    meshBox_coordinate_distance hδ hcell rfl i
  have hK : 0 ≤ K := (abs_nonneg _).trans hv
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hvel
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have htime : |z 0 - t| ≤ δ := hd 0
  have hz0 : |z 0| ≤ 2 := by
    have h := abs_sub_le (z 0) t 0
    simp only [sub_zero] at h
    linarith
  have hw1 : |reconstructBase v w 1 - b 0| ≤ χ := by
    rw [reconstructBase_line]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel_left, abs_mul]
    exact (mul_le_mul ht1 hvel (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hw2 : |reconstructBase v w 2 - b 1| ≤ 2 * χ := by
    rw [reconstructBase_line]
    change |(b 1 + t * (b 4 + b 0) + t ^ 2 * (b 3 - v)) - b 1| ≤ 2 * χ
    have ht2 : |t ^ 2| ≤ 1 := by
      simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht1 2
    calc
      _ = |t * (b 4 + b 0) + t ^ 2 * (b 3 - v)| := by congr 1; ring
      _ ≤ |t * (b 4 + b 0)| + |t ^ 2 * (b 3 - v)| := abs_add_le _ _
      _ ≤ 1 * χ + 1 * χ := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul ht1 hdef (abs_nonneg _) (by norm_num))
          (mul_le_mul ht2 hvel (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hw1b : |reconstructBase v w 1| ≤ K + 1 := by
    have h := abs_sub_le (reconstructBase v w 1) (b 0) 0
    simp only [sub_zero] at h
    linarith
  have hp : |reconstructBase v z 1 - reconstructBase v w 1| ≤ (K + 1) * δ := by
    change |(z 1 - z 0 * v) - (w 1 - w 0 * v)| ≤ _
    calc
      _ = |(z 1 - w 1) - (z 0 - w 0) * v| := by congr 1; ring
      _ ≤ |z 1 - w 1| + |(z 0 - w 0) * v| := abs_sub _ _
      _ ≤ δ + δ * K := by
        rw [abs_mul]
        exact add_le_add (hd 1) (mul_le_mul (hd 0) hv (abs_nonneg _) hδ.le)
      _ = _ := by ring
  have hq : |reconstructBase v z 2 - reconstructBase v w 2| ≤ (3 * K + 4) * δ := by
    have heq : reconstructBase v z 2 - reconstructBase v w 2 =
        (z 2 - w 2) + z 0 * (reconstructBase v z 1 - reconstructBase v w 1) +
          (z 0 - w 0) * reconstructBase v w 1 := by
      simp [reconstructBase]
      <;> ring
    rw [heq]
    calc
      _ ≤ |z 2 - w 2| + |z 0 * (reconstructBase v z 1 - reconstructBase v w 1)| +
          |(z 0 - w 0) * reconstructBase v w 1| := abs_add_three _ _ _
      _ ≤ δ + 2 * ((K + 1) * δ) + δ * (K + 1) := by
        rw [abs_mul, abs_mul]
        exact add_le_add (add_le_add (hd 2)
          (mul_le_mul hz0 hp (abs_nonneg _) (by norm_num)))
          (mul_le_mul (hd 0) hw1b (abs_nonneg _) hδ.le)
      _ = _ := by ring
  refine ⟨htime, hz0, ?_, ?_⟩
  · exact (abs_sub_le _ _ _).trans (by linarith [hp, hw1])
  · exact (abs_sub_le _ _ _).trans (by linarith [hq, hw2])

/-- One quantitative bound transfers each full-time predictor fit to the same
jittered physical base point used for its paired true affine entry. -/
theorem predictor_jitter_error {h b : Fin 6 → ℝ} {v t δ χ K Mt Mp : ℝ}
    {z : Fin 3 → ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hvel : |b 3 - v| ≤ χ) (hdef : |b 4 + b 0| ≤ χ) (hχ1 : χ ≤ 1)
    (hb : |b 0| ≤ K) (hv : |v| ≤ K) (hMt : 0 ≤ Mt) (hMp : 0 ≤ Mp)
    (hcell : baseMesh δ z = baseMesh δ (physicalBase b t))
    (hslope : |predictorTimeSlope h (b 0) (b 1)| ≤ Mt)
    (hgrad : |h 2 + h 3 * z 0| ≤ Mp ∧ |h 4 + h 5 * z 0| ≤ Mp) :
    |predictor h t (b 0) (b 1) -
      predictor h (z 0) (reconstructBase v z 1) (reconstructBase v z 2)| ≤
        Mt * δ + Mp * (3 * χ + (4 * K + 5) * δ) := by
  obtain ⟨htime, _, hp, hq⟩ := reconstructBase_jitter hδ hδ1 ht hvel hdef hχ1 hb hv hcell
  have heq : predictor h t (b 0) (b 1) -
      predictor h (z 0) (reconstructBase v z 1) (reconstructBase v z 2) =
    (t - z 0) * predictorTimeSlope h (b 0) (b 1) +
      (h 2 + h 3 * z 0) * (b 0 - reconstructBase v z 1) +
      (h 4 + h 5 * z 0) * (b 1 - reconstructBase v z 2) := by
    simp only [predictor, predictorTimeSlope]
    ring
  rw [heq]
  calc
    _ ≤ |(t - z 0) * predictorTimeSlope h (b 0) (b 1)| +
      |(h 2 + h 3 * z 0) * (b 0 - reconstructBase v z 1)| +
      |(h 4 + h 5 * z 0) * (b 1 - reconstructBase v z 2)| := abs_add_three _ _ _
    _ ≤ δ * Mt + Mp * (χ + (K + 1) * δ) + Mp * (2 * χ + (3 * K + 4) * δ) := by
      rw [abs_mul, abs_mul, abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul (by simpa only [abs_sub_comm] using htime) hslope (abs_nonneg _) hδ.le)
        (mul_le_mul hgrad.1 (by simpa only [abs_sub_comm] using hp) (abs_nonneg _) hMp))
        (mul_le_mul hgrad.2 (by simpa only [abs_sub_comm] using hq) (abs_nonneg _) hMp)
    _ = _ := by ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
