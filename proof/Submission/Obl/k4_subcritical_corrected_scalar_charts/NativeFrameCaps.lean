/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeFrameCaps.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeFrame
import Submission.Lib.K4AffineMeshCaps.Transport

/-! The accepted affine mesh transport gives normalized native caps with the
exact fourth-power Jacobian. Shears only affect the required source mesh. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set Matrix
open scoped ENNReal
open Submission.Lib.K4AffineMeshCaps

noncomputable section

def nativeFrameMatrix (h v w τ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![h⁻¹, 0, 0], ![-v / h, h⁻¹, 0], ![(w + τ * v) / h ^ 2, -τ / h ^ 2, (h ^ 2)⁻¹]]

def nativeFrameShift (h t₀ p r τ : ℝ) : Fin 3 → ℝ :=
  ![-t₀ / h, -p / h, (-r + τ * p) / h ^ 2]

theorem nativeFrame_eq_affine (h t₀ p r v w τ : ℝ) (z : Fin 3 → ℝ) :
    nativeFrame h t₀ p r v w τ z =
      affineBase (nativeFrameMatrix h v w τ) (nativeFrameShift h t₀ p r τ) z := by
  ext i
  fin_cases i <;>
    simp [nativeFrame, nativeFrameMatrix, nativeFrameShift, affineBase,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, div_eq_mul_inv] <;> ring

theorem nativeFrameMatrix_det (h v w τ : ℝ) :
    (nativeFrameMatrix h v w τ).det = (h ^ 4)⁻¹ := by
  rw [Matrix.det_fin_three]
  simp [nativeFrameMatrix, ← inv_pow]
  ring

theorem nativeFrameMatrix_det_ne_zero {h : ℝ} (hh : h ≠ 0) (v w τ : ℝ) :
    (nativeFrameMatrix h v w τ).det ≠ 0 := by
  rw [nativeFrameMatrix_det]
  exact inv_ne_zero (pow_ne_zero _ hh)

theorem nativeFrameMatrix_jacobian (h v w τ : ℝ) :
    |(nativeFrameMatrix h v w τ).det|⁻¹ = h ^ 4 := by
  rw [nativeFrameMatrix_det, abs_inv, inv_inv, abs_of_nonneg (by positivity)]

/-- Normalized base cells inherit the exact original masked-cell cap. The
common hidden-width or reference factor can be included in `C`. -/
theorem native_frame_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {h δ σ C : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hσ : 0 < σ) (hC : 0 ≤ C)
    (t₀ p r v w τ : ℝ)
    (hresolve : ∀ i, (∑ j, |nativeFrameMatrix h v w τ i j| * δ) ≤ σ)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {z | baseMesh δ (x z) = q ∧ condition z} ≤ ENNReal.ofReal (C * δ ^ 3))
    (q : Fin 3 → ℤ) :
    μ {z | baseMesh σ (nativeFrame h t₀ p r v w τ (x z)) = q ∧ condition z} ≤
      ENNReal.ofReal (27 * C * h ^ 4 * σ ^ 3) := by
  have hc := affine_mesh_cell_cap μ x condition (nativeFrameMatrix h v w τ)
    (nativeFrameShift h t₀ p r τ) (nativeFrameMatrix_det_ne_zero hh.ne' v w τ)
    hδ hσ hC hresolve hcap q
  simpa only [nativeFrame_eq_affine, nativeFrameMatrix_jacobian] using hc

/-- The same cap in the original witness's restricted law, ready for raw
coefficient calibration. No normalized posterior replaces the witness mass. -/
theorem native_frame_restrict_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (hx : Measurable x) (E : Set Ω)
    {h δ σ C : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hσ : 0 < σ) (hC : 0 ≤ C)
    (t₀ p r v w τ : ℝ)
    (hresolve : ∀ i, (∑ j, |nativeFrameMatrix h v w τ i j| * δ) ≤ σ)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {z | baseMesh δ (x z) = q ∧ z ∈ E} ≤ ENNReal.ofReal (C * δ ^ 3))
    (q : Fin 3 → ℤ) :
    (μ.restrict E) {z | baseMesh σ (nativeFrame h t₀ p r v w τ (x z)) = q} ≤
      ENNReal.ofReal (27 * C * h ^ 4 * σ ^ 3) := by
  have hm : Measurable (fun z => baseMesh σ (nativeFrame h t₀ p r v w τ (x z))) :=
    (measurable_baseMesh σ).comp ((measurable_nativeFrame h t₀ p r v w τ).comp hx)
  have hset : MeasurableSet
      {z | baseMesh σ (nativeFrame h t₀ p r v w τ (x z)) = q} :=
    measurableSet_eq_fun hm measurable_const
  rw [Measure.restrict_apply hset]
  exact native_frame_cell_cap μ x (fun z => z ∈ E) hh hδ hσ hC
    t₀ p r v w τ hresolve hcap q

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
