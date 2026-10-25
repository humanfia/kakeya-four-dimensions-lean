/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeFrameSupport.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonFrames
import Submission.Obl.k4_horizontal_strict_parameter_step.JitterGeometry

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- A single common frame for every observed predictor in one unchanged
velocity/parameter cell and one native time block. -/
def nativeComparisonFrame (χ q D : ℝ) (g : Fin 3 → ℤ) (j : ℝ) : ComparisonFrame where
  velocity := χ * (g 0 : ℝ)
  timeCenter := j * q
  timeScale := 16 * q
  pCenter := D * (g 1 : ℝ)
  qCenter := D * (g 2 : ℝ)
  parameterScale := 16 * D

theorem nativeComparisonFrame_jacobian (χ q D : ℝ) (g : Fin 3 → ℤ) (j : ℝ) :
    (nativeComparisonFrame χ q D g j).timeScale *
      (nativeComparisonFrame χ q D g j).parameterScale ^ 2 = 4096 * q * D ^ 2 := by
  dsimp [nativeComparisonFrame]
  ring

/-- The entire old product domain lies in the matching half ball. Consequently
a successful comparison controls the whole domain on which its original floors live. -/
theorem nativeComparisonFrame_product {χ q D j t p r : ℝ} {g : Fin 3 → ℤ}
    (hq : 0 < q) (hD : 0 < D)
    (ht : t ∈ Icc (j * q) ((j + 1) * q))
    (hp : p ∈ Icc (D * (g 1 : ℝ)) (D * (g 1 : ℝ) + D))
    (hr : r ∈ Icc (D * (g 2 : ℝ)) (D * (g 2 : ℝ) + D)) :
    ‖(nativeComparisonFrame χ q D g j).parameterPoint t p r‖ ≤ 1 / 2 := by
  apply ComparisonFrame.parameterPoint_mem_half (nativeComparisonFrame χ q D g j)
      (by dsimp [nativeComparisonFrame]; positivity)
      (by dsimp [nativeComparisonFrame]; positivity)
  · change |t - j * q| ≤ 16 * q / 4
    rw [abs_of_nonneg (by linarith [ht.1])]
    nlinarith [ht.2]
  · change |p - D * (g 1 : ℝ)| ≤ 16 * D / 4
    rw [abs_of_nonneg (by linarith [hp.1])]
    linarith [hp.2]
  · change |r - D * (g 2 : ℝ)| ≤ 16 * D / 4
    rw [abs_of_nonneg (by linarith [hr.1])]
    linarith [hr.2]

/-- Every point of the same physical mesh cell stays in the matching half ball.
The conclusion holds for the common jitter, rather than for a chosen cell corner. -/
theorem nativeComparisonFrame_jitter {b : Fin 6 → ℝ} {g : Fin 3 → ℤ}
    {χ q D δ K t j : ℝ} {z : Fin 3 → ℝ}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hq : 0 < q) (hD : 0 < D)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδq : δ ≤ q)
    (hroom : 2 * χ + (3 * K + 4) * δ ≤ D)
    (ht : t ∈ Icc (0 : ℝ) 1) (hblock : t ∈ Icc (j * q) ((j + 1) * q))
    (hgrid : ⌊b 3 / χ⌋ = g 0 ∧ ⌊b 0 / D⌋ = g 1 ∧ ⌊b 1 / D⌋ = g 2)
    (hdef : |b 4 + b 0| ≤ χ) (hb : |b 0| ≤ K)
    (hv : |χ * (g 0 : ℝ)| ≤ K)
    (hcell : baseMesh δ z = baseMesh δ (physicalBase b t)) :
    ‖(nativeComparisonFrame χ q D g j).coordinates z‖ ≤ 1 / 2 := by
  have hvel : |b 3 - χ * (g 0 : ℝ)| ≤ χ := by
    simpa only [floorPoint, hgrid.1] using floorPoint_error hχ (b 3)
  have hp0 : |b 0 - D * (g 1 : ℝ)| ≤ D := by
    simpa only [floorPoint, hgrid.2.1] using floorPoint_error hD (b 0)
  have hq0 : |b 1 - D * (g 2 : ℝ)| ≤ D := by
    simpa only [floorPoint, hgrid.2.2] using floorPoint_error hD (b 1)
  have hK : 0 ≤ K := (abs_nonneg _).trans hv
  obtain ⟨htime, -, hp, hr⟩ :=
    reconstructBase_jitter hδ hδ1 ht hvel hdef hχ1 hb hv hcell
  apply comparisonCoordinates_mem_half
      (by change 0 < 16 * q; positivity) (by change 0 < 16 * D; positivity)
  · change |z 0 - j * q| ≤ 16 * q / 4
    have htc : |t - j * q| ≤ q := by
      rw [abs_of_nonneg (by linarith [hblock.1])]
      nlinarith [hblock.2]
    have htriangle := abs_sub_le (z 0) t (j * q)
    linarith
  · change |reconstructBase (χ * (g 0 : ℝ)) z 1 - D * (g 1 : ℝ)| ≤ 16 * D / 4
    have htriangle := abs_sub_le (reconstructBase (χ * (g 0 : ℝ)) z 1)
      (b 0) (D * (g 1 : ℝ))
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * K + 3) hδ.le]
  · change |reconstructBase (χ * (g 0 : ℝ)) z 2 - D * (g 2 : ℝ)| ≤ 16 * D / 4
    have htriangle := abs_sub_le (reconstructBase (χ * (g 0 : ℝ)) z 2)
      (b 1) (D * (g 2 : ℝ))
    linarith

end

end Submission.Obl.k4_horizontal_strict_parameter_step
