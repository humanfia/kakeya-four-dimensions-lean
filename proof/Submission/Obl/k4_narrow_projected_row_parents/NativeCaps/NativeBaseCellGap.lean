/- Adapted from this LOT tree o222, session x0774, commit 9dbb47a74d2ab640ef4d8807465d86d7e9066adc,
   Submission/Obl/k4_projected_parent_contact_reduction/NativeBaseCellGap.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.ParentZoom
import Submission.Lib.K4AffineMeshCaps.Transport

/-! Physical source cells control the accepted parent's native base coordinates. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

theorem native_base_gap_of_mesh_cell
    (Z : Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom) {delta sigma : ℝ} (hd : 0 < delta)
    (hresolve : ∀ i, (∑ j, |Z.baseMatrix i j| * delta) ≤ sigma)
    (p p' : NativePoint)
    (hcell : baseMesh delta (rootBaseCoordinates p) = baseMesh delta (rootBaseCoordinates p')) :
    ‖nativeBase (Z.nativePoint p) - nativeBase (Z.nativePoint p')‖ ≤ 3 * sigma := by
  have hp : rootBaseCoordinates p ∈ meshBox delta (baseMesh delta (rootBaseCoordinates p)) := rfl
  have hp' : rootBaseCoordinates p' ∈ meshBox delta (baseMesh delta (rootBaseCoordinates p)) := hcell.symm
  have hclose : ∀ j, |rootBaseCoordinates p j - rootBaseCoordinates p' j| ≤ delta :=
    fun j => meshBox_coordinate_distance hd hp hp' j
  have hcoord (i : Fin 3) :
      |nativeBase (Z.nativePoint p) i - nativeBase (Z.nativePoint p') i| ≤ sigma := by
    change |rootBaseCoordinates (Z.nativePoint p) i - rootBaseCoordinates (Z.nativePoint p') i| ≤ sigma
    rw [Z.nativePoint_base, Z.nativePoint_base]
    exact (affineBase_coordinate_variation Z.baseMatrix Z.baseShift hclose i).trans (hresolve i)
  have hn := Submission.Obl.k4_scalar_coefficient_clustering.coeff_norm_le_abs_add
    (nativeBase (Z.nativePoint p) - nativeBase (Z.nativePoint p'))
  change ‖nativeBase (Z.nativePoint p) - nativeBase (Z.nativePoint p')‖ ≤
    |nativeBase (Z.nativePoint p) 0 - nativeBase (Z.nativePoint p') 0| +
      |nativeBase (Z.nativePoint p) 1 - nativeBase (Z.nativePoint p') 1| +
      |nativeBase (Z.nativePoint p) 2 - nativeBase (Z.nativePoint p') 2| at hn
  linarith [hcoord 0, hcoord 1, hcoord 2]

end

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
