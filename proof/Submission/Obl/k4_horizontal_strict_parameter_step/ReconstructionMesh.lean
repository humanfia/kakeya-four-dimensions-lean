/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ReconstructionMesh.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.AffineUpgrade
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set

noncomputable section

/-- The lower endpoint of the mesh cell containing a real coordinate. -/
def floorPoint (δ t : ℝ) : ℝ := δ * (⌊t / δ⌋ : ℝ)

/-- Static parameters reconstructed from the physical base point at its lower mesh corner. -/
def meshParameters (b : Fin 6 → ℝ) (δ v t : ℝ) : Fin 3 → ℝ :=
  let τ := floorPoint δ t
  let p := floorPoint δ (b 0 + t * b 3) - τ * v
  ![τ, p, floorPoint δ (b 1 + t * b 4) + τ * p]

theorem floorPoint_error {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : |t - floorPoint δ t| ≤ δ :=
  Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hδ t

theorem floorPoint_time {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc (0 : ℝ) 1) :
    floorPoint δ t ∈ Icc (0 : ℝ) 1 := by
  have hf : 0 ≤ ⌊t / δ⌋ := Int.floor_nonneg.mpr (div_nonneg ht.1 hδ.le)
  have hnonneg : 0 ≤ floorPoint δ t := mul_nonneg hδ.le (by exact_mod_cast hf)
  have hlo := Int.sub_floor_div_mul_nonneg t hδ
  have hupper : floorPoint δ t ≤ t := by dsimp [floorPoint]; nlinarith
  exact ⟨hnonneg, hupper.trans ht.2⟩

/-- Contact and velocity-bin errors remain small after reconstructing the two static
parameters at the base mesh corner. -/
theorem meshParameters_error {b : Fin 6 → ℝ} {δ v t χ K : ℝ}
    (hδ : 0 < δ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hvel : |b 3 - v| ≤ χ) (hcontact : |b 4 + b 0| ≤ χ)
    (hpos : |b 0| ≤ K) (hv : |v| ≤ K) :
    meshParameters b δ v t 0 ∈ Icc (0 : ℝ) 1 ∧
    |meshParameters b δ v t 1 - b 0| ≤ χ + (K + 1) * δ ∧
    |meshParameters b δ v t 2 - b 1| ≤ 2 * (χ + (K + 1) * δ) := by
  let τ := floorPoint δ t
  let p := floorPoint δ (b 0 + t * b 3) - τ * v
  have hτ : τ ∈ Icc (0 : ℝ) 1 := floorPoint_time hδ ht
  have htime : |t - τ| ≤ δ := floorPoint_error hδ t
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hvel
  have hK : 0 ≤ K := (abs_nonneg _).trans hv
  have hx := floorPoint_error hδ (b 0 + t * b 3)
  have hy := floorPoint_error hδ (b 1 + t * b 4)
  have hp : |p - b 0| ≤ χ + (K + 1) * δ := by
    have heq : p - b 0 = (floorPoint δ (b 0 + t * b 3) - (b 0 + t * b 3)) +
        (t - τ) * v + t * (b 3 - v) := by dsimp [p]; ring
    rw [heq]
    calc
      _ ≤ |floorPoint δ (b 0 + t * b 3) - (b 0 + t * b 3)| +
        |(t - τ) * v| + |t * (b 3 - v)| := abs_add_three _ _ _
      _ ≤ δ + δ * K + 1 * χ := by
        rw [abs_mul, abs_mul]
        exact add_le_add (add_le_add (by simpa only [abs_sub_comm] using hx)
          (mul_le_mul htime hv (abs_nonneg _) hδ.le))
          (mul_le_mul (by simpa only [abs_of_nonneg ht.1] using ht.2) hvel
            (abs_nonneg _) (by norm_num))
      _ = χ + (K + 1) * δ := by ring
  have hq : |floorPoint δ (b 1 + t * b 4) + τ * p - b 1| ≤
      2 * (χ + (K + 1) * δ) := by
    have heq : floorPoint δ (b 1 + t * b 4) + τ * p - b 1 =
        (floorPoint δ (b 1 + t * b 4) - (b 1 + t * b 4)) +
        t * (b 4 + b 0) + (τ - t) * b 0 + τ * (p - b 0) := by ring
    rw [heq]
    calc
      _ ≤ |floorPoint δ (b 1 + t * b 4) - (b 1 + t * b 4)| +
        |t * (b 4 + b 0)| + |(τ - t) * b 0| + |τ * (p - b 0)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_three _ _ _) le_rfl)
      _ ≤ δ + 1 * χ + δ * K + 1 * (χ + (K + 1) * δ) := by
        rw [abs_mul, abs_mul, abs_mul]
        refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
        · simpa only [abs_sub_comm] using hy
        · exact mul_le_mul (by simpa only [abs_of_nonneg ht.1] using ht.2) hcontact
            (abs_nonneg _) (by norm_num)
        · exact mul_le_mul (by simpa only [abs_sub_comm] using htime) hpos (abs_nonneg _) hδ.le
        · exact mul_le_mul (by simpa only [abs_of_nonneg hτ.1] using hτ.2) hp (abs_nonneg _) (by norm_num)
      _ = 2 * (χ + (K + 1) * δ) := by ring
  exact ⟨hτ, hp, hq⟩

/-- The predictor's time derivative is independent of time. -/
def predictorTimeSlope (h : Fin 6 → ℝ) (p q : ℝ) : ℝ := h 1 + h 3 * p + h 5 * q

theorem predictor_reconstruction_error {h : Fin 6 → ℝ} {b : Fin 6 → ℝ}
    {δ v t χ K M D : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hvel : |b 3 - v| ≤ χ) (hcontact : |b 4 + b 0| ≤ χ)
    (hpos : |b 0| ≤ K) (hv : |v| ≤ K) (hM : 0 ≤ M) (hD : 0 < D)
    (hslope : |predictorTimeSlope h (b 0) (b 1)| ≤ 2 * M)
    (hgrad : ∀ τ ∈ Icc (0 : ℝ) 1,
      |h 2 + h 3 * τ| ≤ 2 * M / D ∧ |h 4 + h 5 * τ| ≤ 2 * M / D) :
    |predictor h t (b 0) (b 1) -
      predictor h (meshParameters b δ v t 0) (meshParameters b δ v t 1)
        (meshParameters b δ v t 2)| ≤
      2 * M * δ + (6 * M / D) * (χ + (K + 1) * δ) := by
  obtain ⟨hτ, hp, hq⟩ := meshParameters_error hδ ht hvel hcontact hpos hv
  let τ := meshParameters b δ v t 0
  let p := meshParameters b δ v t 1
  let q := meshParameters b δ v t 2
  have htime : |t - τ| ≤ δ := floorPoint_error hδ t
  have hg := hgrad τ hτ
  have heq : predictor h t (b 0) (b 1) - predictor h τ p q =
      (t - τ) * predictorTimeSlope h (b 0) (b 1) +
      (h 2 + h 3 * τ) * (b 0 - p) + (h 4 + h 5 * τ) * (b 1 - q) := by
    dsimp [predictor, predictorTimeSlope]
    ring
  rw [heq]
  calc
    _ ≤ |(t - τ) * predictorTimeSlope h (b 0) (b 1)| +
      |(h 2 + h 3 * τ) * (b 0 - p)| + |(h 4 + h 5 * τ) * (b 1 - q)| := abs_add_three _ _ _
    _ ≤ δ * (2 * M) + (2 * M / D) * (χ + (K + 1) * δ) +
        (2 * M / D) * (2 * (χ + (K + 1) * δ)) := by
      rw [abs_mul, abs_mul, abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul htime hslope (abs_nonneg _) hδ.le)
        (mul_le_mul hg.1 (by simpa only [abs_sub_comm] using hp) (abs_nonneg _) (by positivity)))
        (mul_le_mul hg.2 (by simpa only [abs_sub_comm] using hq) (abs_nonneg _) (by positivity))
    _ = 2 * M * δ + (6 * M / D) * (χ + (K + 1) * δ) := by ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
