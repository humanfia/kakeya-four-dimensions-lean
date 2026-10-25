/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/HorizontalFlow.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Mathlib

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory

noncomputable section

/-- The determinant-one reference motion of a static horizontal parameter square. -/
def horizontalFibre (t v : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![z 0 + t * v, z 1 - t * z 0]

def horizontalFlow (v : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 0, z 1 + z 0 * v, z 2 - z 0 * z 1]

def reconstructBase (v : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 0, z 1 - z 0 * v, z 2 + z 0 * (z 1 - z 0 * v)]

theorem horizontalFibre_map (t v : ℝ) :
    Measure.map (horizontalFibre t v) (volume : Measure (Fin 2 → ℝ)) = volume := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![1, 0], ![-t, 1]]
  have hdet : M.det = 1 := by rw [Matrix.det_fin_two]; norm_num [M]
  have hfun : horizontalFibre t v =
      (fun z : Fin 2 → ℝ => z + ![t * v, 0]) ∘ Matrix.toLin' M := by
    funext z
    rw [Function.comp_apply, Matrix.toLin'_apply]
    ext i
    fin_cases i <;> simp [horizontalFibre, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    <;> ring
  have hlin : Measurable (Matrix.toLin' M) := (LinearMap.continuous_on_pi _).measurable
  rw [hfun, ← Measure.map_map (measurable_add_const _) hlin,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [hdet]; norm_num), hdet]
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul, map_add_right_eq_self]

theorem measurePreserving_horizontalFlow (v : ℝ) :
    MeasurePreserving (horizontalFlow v) (volume : Measure (Fin 3 → ℝ)) volume := by
  have hsplit := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have hshear : MeasurePreserving
      (fun p : ℝ × (Fin 2 → ℝ) => (id p.1, horizontalFibre p.1 v p.2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) := by
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun (t : ℝ) (z : Fin 2 → ℝ) => horizontalFibre t v z)
    · unfold horizontalFibre
      fun_prop
    · exact Filter.Eventually.of_forall fun t => horizontalFibre_map t v
  have hjoin := hsplit.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  convert hjoin.comp (hshear.comp hsplit) using 1
  funext z
  ext i
  fin_cases i <;> simp [horizontalFlow, horizontalFibre, Function.comp_apply,
    MeasurableEquiv.piFinSuccAbove_apply, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv_symm_apply, Fin.removeNth, Fin.tail]

def horizontalFlowEquiv (v : ℝ) : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) where
  toFun := horizontalFlow v
  invFun := reconstructBase v
  left_inv z := by ext i; fin_cases i <;> simp [horizontalFlow, reconstructBase] <;> ring
  right_inv z := by ext i; fin_cases i <;> simp [horizontalFlow, reconstructBase] <;> ring
  measurable_toFun := by change Measurable (horizontalFlow v); unfold horizontalFlow; fun_prop
  measurable_invFun := by change Measurable (reconstructBase v); unfold reconstructBase; fun_prop

theorem measurePreserving_reconstructBase (v : ℝ) :
    MeasurePreserving (reconstructBase v) (volume : Measure (Fin 3 → ℝ)) volume :=
  (measurePreserving_horizontalFlow v).symm (horizontalFlowEquiv v)

end

end Submission.Obl.k4_horizontal_strict_parameter_step
