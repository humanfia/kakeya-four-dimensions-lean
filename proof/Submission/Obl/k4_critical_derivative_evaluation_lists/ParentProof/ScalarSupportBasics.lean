/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, ScalarSupportBasics.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ContactBoxes
import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking

/-! Adapted from this LOT tree, obligation o107, session x0353,
`Submission/Obl/k4_finite_narrowness_path_improvement/AffineContactFit.lean`, `Submission/Obl/k4_finite_narrowness_path_improvement/InterceptBinCount.lean`
(commit 2d33b59a). -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Finset

def affineBaseEval (A : Fin 4 → ℝ) (q : Fin 3 → ℝ) : ℝ :=
  A 0 + A 1 * q 0 + A 2 * q 1 + A 3 * q 2

/-- Scalar projection of the accepted three-coordinate grid count. -/
theorem scalar_floor_image_card_of_diameter {ι : Type*} (S : Finset ι) (y : ι → ℝ)
    {δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, |y i - y j| ≤ L) :
    ((S.image (fun i => ⌊y i / δ⌋)).card : ℝ) ≤ 32 * L / δ + 64 := by
  classical
  let embed : ℤ → Fin 3 → ℤ := fun z => ![z, 0, 0]
  have hembed : Function.Injective embed := by
    intro z w h
    exact congrFun h 0
  have h := Submission.Obl.k4_plank_projected_multiplicity.card_grid_codes_of_coordinate_diameters
    S (fun i => ![y i, 0, 0]) hδ ![L, 0, 0]
    (by intro j; fin_cases j <;> dsimp <;> positivity)
    (by
      intro i hi j hj k
      fin_cases k <;> dsimp
      · exact hdiam i hi j hj
      · simp
      · simp)
  have hcode (i : ι) : (fun j : Fin 3 => ⌊(![y i, 0, 0] : Fin 3 → ℝ) j / δ⌋) =
      embed ⌊y i / δ⌋ := by
    ext j
    fin_cases j <;> simp [embed]
  have hfunction : (fun i j => ⌊(![y i, 0, 0] : Fin 3 → ℝ) j / δ⌋) =
      (fun i => embed ⌊y i / δ⌋) := funext hcode
  rw [hfunction] at h
  have himage : S.image (fun i => embed ⌊y i / δ⌋) =
      (S.image (fun i => ⌊y i / δ⌋)).image embed := by rw [Finset.image_image]; rfl
  rw [himage, Finset.card_image_of_injective _ hembed] at h
  convert h using 1
  simp only [Fin.prod_univ_three]
  dsimp
  ring

theorem affineBaseEval_mesh_gap (A : Fin 4 → ℝ) (q r : Fin 3 → ℝ) (M δ : ℝ)
    (hM : 0 ≤ M) (hA : ∀ i : Fin 3, |A i.succ| ≤ M)
    (hgap : ∀ i, |q i - r i| ≤ δ) :
    |affineBaseEval A q - affineBaseEval A r| ≤ 3 * M * δ := by
  calc
    _ = |A 1 * (q 0 - r 0) + A 2 * (q 1 - r 1) + A 3 * (q 2 - r 2)| := by
      unfold affineBaseEval
      congr 1
      ring
    _ ≤ |A 1 * (q 0 - r 0)| + |A 2 * (q 1 - r 1)| + |A 3 * (q 2 - r 2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M * δ + M * δ + M * δ := by
      apply add_le_add
      · apply add_le_add <;> rw [abs_mul]
        · exact mul_le_mul (hA 0) (hgap 0) (abs_nonneg _) hM
        · exact mul_le_mul (hA 1) (hgap 1) (abs_nonneg _) hM
      · rw [abs_mul]
        exact mul_le_mul (hA 2) (hgap 2) (abs_nonneg _) hM
    _ = _ := by ring


end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
