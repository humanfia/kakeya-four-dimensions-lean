/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/Inherited/ContactVolume.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/ContactVolume.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ContactVolume.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_critical_switching_state_preparation.Inherited.ContactBoxes

/-! The common contact box has the fourth-power volume scale. -/

namespace Submission.Obl.k4_critical_switching_state_preparation.Inherited

noncomputable section

open MeasureTheory Set
open scoped ENNReal

def contactCoordinates (m : ℝ) (p q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![q 0, q 1 - referenceZ p (q 0), contactTransverse m p q]

def contactShearMatrix (m : ℝ) (p : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; -p 2, 1, 0; p 0 + m * p 2, -m, 1]

theorem contactShearMatrix_det (m : ℝ) (p : Fin 3 → ℝ) : (contactShearMatrix m p).det = 1 := by
  simp [contactShearMatrix, Matrix.det_fin_three]

theorem contactCoordinates_affine (m : ℝ) (p : Fin 3 → ℝ) :
    contactCoordinates m p = fun q => Matrix.toLin' (contactShearMatrix m p) q +
      ![0, -p 0, -p 1 + m * p 0] := by
  ext q i
  fin_cases i <;>
    simp [contactCoordinates, contactTransverse, referenceY, referenceZ,
      contactShearMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem measurePreserving_contactCoordinates (m : ℝ) (p : Fin 3 → ℝ) :
    MeasurePreserving (contactCoordinates m p) (volume : Measure (Fin 3 → ℝ)) volume := by
  have hlin : MeasurePreserving (Matrix.toLin' (contactShearMatrix m p))
      (volume : Measure (Fin 3 → ℝ)) volume := by
    refine ⟨(Matrix.toLin' (contactShearMatrix m p)).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi
      (by rw [contactShearMatrix_det]; norm_num), contactShearMatrix_det]
    simp
  rw [contactCoordinates_affine]
  exact (measurePreserving_add_right volume ![0, -p 0, -p 1 + m * p 0]).comp hlin

def contactOuterBox (m : ℝ) (p : Fin 3 → ℝ) (H A B : ℝ) : Set (Fin 3 → ℝ) :=
  contactCoordinates m p ⁻¹' Set.Icc ![m - H / 2, -A, -B] ![m + H / 2, A, B]

theorem volume_contactOuterBox (m : ℝ) (p : Fin 3 → ℝ) (H A B : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    volume (contactOuterBox m p H A B) = ENNReal.ofReal (4 * H * A * B) := by
  rw [contactOuterBox, (measurePreserving_contactCoordinates m p).measure_preimage
      measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi, Fin.prod_univ_three]
  change ENNReal.ofReal (m + H / 2 - (m - H / 2)) * ENNReal.ofReal (A - -A) *
    ENNReal.ofReal (B - -B) = _
  rw [show m + H / 2 - (m - H / 2) = H by ring,
    show A - -A = 2 * A by ring, show B - -B = 2 * B by ring]
  rw [← ENNReal.ofReal_mul hH, ← ENNReal.ofReal_mul (by positivity : 0 ≤ H * (2 * A))]
  congr 1
  ring

/-- The full true box meeting a reference is paid for by a common base set
of volume at most 1024*K^3*H^4, retaining the transverse H-squared scale. -/
theorem horizontalTrueBox_common_volume_bound
    (c : Fin 5 → ℝ) (p q₀ : Fin 3 → ℝ) (m H K D : ℝ)
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hD : D ≤ H ^ 2)
    (hm : |m| ≤ 1) (hc : |c 1| ≤ K) (hv : |p 2| ≤ K)
    (hcenter : |c 3 + c 0 + m * c 1| ≤ K * H) (htilt : |c 4 - m| ≤ K * H)
    (hq₀ : q₀ ∈ horizontalTrueBox c m H K)
    (hcontactZ : |q₀ 1 - referenceZ p (q₀ 0)| ≤ K * D)
    (hcontactY : |q₀ 2 - referenceY p (q₀ 0)| ≤ K * D) :
    volume (horizontalTrueBox c m H K) ≤ ENNReal.ofReal (1024 * K ^ 3 * H ^ 4) := by
  have hK0 : 0 ≤ K := by linarith
  have hsub : horizontalTrueBox c m H K ⊆
      contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2) := by
    intro q hq
    have hbounds := horizontalTrueBox_common_contact c p q₀ m H K D hH hH1 hK hD hm hc hv
      hcenter htilt hq₀ hcontactZ hcontactY q hq
    have ht := abs_le.mp hq.1
    have hZ := abs_le.mp hbounds.1
    have hY := abs_le.mp hbounds.2
    change ![m - H / 2, -(8 * K * H), -(32 * K ^ 2 * H ^ 2)] ≤
      ![q 0, q 1 - referenceZ p (q 0), contactTransverse m p q] ∧
      ![q 0, q 1 - referenceZ p (q 0), contactTransverse m p q] ≤
      ![m + H / 2, 8 * K * H, 32 * K ^ 2 * H ^ 2]
    constructor <;> intro i <;> fin_cases i <;> dsimp <;> linarith
  refine (measure_mono hsub).trans_eq ?_
  rw [volume_contactOuterBox m p H _ _ hH.le (by positivity) (by positivity)]
  congr 1
  ring

end

end Submission.Obl.k4_critical_switching_state_preparation.Inherited
