import Submission.Lib.K4ScalarCoreAssembly.NeighborhoodCellCeilings

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ScalarCoreAssembly

/-- The supplied fine base ceiling controls every coarser grid cell by its area.
The fine-cell count cancels its two powers of the fine mesh. -/
theorem grid_cell_ceiling {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (cell : Ω → I)
    (z : Ω → Fin 2 → ℝ) (center : I → Fin 2 → ℝ)
    (δ ω R K : ℝ) (hδ : 0 < δ) (hδω : δ ≤ ω) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hcap : ∀ q : Fin 2 → ℤ,
      μ {p | (fun j => ⌊z p j/δ⌋)=q} ≤ ENNReal.ofReal (K*δ^2))
    (hnear : ∀ p ∈ A, ∀ j, |z p j-center (cell p) j| ≤ R*ω) :
    ∀ i, μ (A ∩ {p | cell p=i}) ≤ ENNReal.ofReal ((4*R+11)^2*K*ω^2) := by
  have hω : 0 < ω := hδ.trans_le hδω
  have hnear' (p : Ω) (hp : p ∈ A) (j) :
      |z p j-center (cell p) j| ≤ (R*ω/δ)*δ := by
    simpa only [div_mul_cancel₀ _ hδ.ne'] using hnear p hp j
  have hbound := original_neighborhood_cell_ceiling μ 2 A cell z center δ (R*ω/δ)
    hδ (by positivity) (ENNReal.ofReal (K*δ^2))
    (fun q => (measure_mono inter_subset_right).trans (hcap q)) hnear'
  intro i
  apply (hbound i).trans
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hid : (4*(R*ω/δ)+11)^2*(K*δ^2) = K*(4*R*ω+11*δ)^2 := by
    field_simp <;> ring
  rw [hid]
  have hlin : 4*R*ω+11*δ ≤ (4*R+11)*ω := by nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 4*R*ω+11*δ) hlin 2
  calc
    _ ≤ K*((4*R+11)*ω)^2 := mul_le_mul_of_nonneg_left hsq hK
    _ = _ := by ring

end Submission.Obl.k4_conditional_common_affine_field
