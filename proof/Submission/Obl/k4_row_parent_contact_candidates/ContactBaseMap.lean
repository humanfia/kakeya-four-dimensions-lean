/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactBaseMap.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ZoomLabel
import Submission.Obl.k4_row_parent_contact_candidates.ZoomLaw
import Submission.Lib.K4AffineMeshCaps

/-!
# The zoomed base chart as an affine map

The base coordinates `(t', x₁', x₂'')` of the zoomed and row-normalized chart are
an affine function of the original base coordinates `(t, x₁, x₂)`:
`baseMat` is lower triangular with diagonal `(1/q, 1/q, 1/(q g λ))`, so its
determinant is `1/(q³ g λ)`. This puts the zoomed caps within reach of the
affine mesh-cap transport `Submission.Lib.K4AffineMeshCaps.affine_mesh_cell_cap`.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open Submission.Lib.K4ContactNormalization (point skewCoeff)
open Submission.Lib.K4AffineMeshCaps (affineBase)

noncomputable section

namespace Zoom

variable (Z : Zoom) (B : Fin 2 → ℝ) (lam : ℝ)

/-- Linear part of the zoomed base chart. -/
def baseMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Z.q⁻¹, 0, 0;
     0, Z.q⁻¹, 0;
     -(Z.c₃ / Z.w + B 0 / Z.q) / lam, -(Z.c₄ / Z.w + B 1 / Z.q) / lam, (Z.w * lam)⁻¹]

/-- Translation part of the zoomed base chart. -/
def baseVec : Fin 3 → ℝ :=
  ![-Z.t₀ / Z.q, -Z.z₀ / Z.q, (-Z.c₂ / Z.w + B 0 * Z.t₀ / Z.q + B 1 * Z.z₀ / Z.q) / lam]

/-- Original base coordinates of a trajectory point. -/
def baseOf (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ := ![t, b 0 + t * b 3, b 1 + t * b 4]

variable {Z B lam}

/-- The zoomed base coordinates are the affine image of the original ones. -/
theorem baseOf_nCoeff (hZ : Z.Ok) (hlam : lam ≠ 0) (b : Fin 6 → ℝ) (t : ℝ) :
    baseOf (nCoeff Z B lam b) (Z.time t) = affineBase (baseMat Z B lam) (baseVec Z B lam)
      (baseOf b t) := by
  have hq := hZ.q_ne
  have hw := hZ.w_ne
  funext i
  fin_cases i <;>
    simp [baseOf, nCoeff, skewCoeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time, affineBase, baseMat, baseVec,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp <;> ring

theorem det_baseMat : (baseMat Z B lam).det = Z.q⁻¹ * Z.q⁻¹ * (Z.w * lam)⁻¹ := by
  simp [baseMat, Matrix.det_fin_three]

theorem det_baseMat_ne (hZ : Z.Ok) (hlam : lam ≠ 0) : (baseMat Z B lam).det ≠ 0 := by
  rw [det_baseMat]
  have := hZ.q_ne
  have := hZ.w_ne
  positivity

end Zoom

end

end Submission.Obl.k4_row_parent_contact_candidates

namespace Submission.Obl.k4_row_parent_contact_candidates

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ContactNormalization (point skewCoeff)
open Submission.Lib.K4AffineMeshCaps (affineBase affine_mesh_cell_cap)
open Submission.Lib.K4MovingMeshBoxes (baseMesh)

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- **Zoomed cell caps.** Finite-mesh caps of the original law at a fine scale
`δ` (with any extra incidence condition) give caps of the zoomed law at scale
`σ`, through the affine base chart. -/
theorem zoom_cell_cap (μ₀ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) {Z : Zoom} (hZ : Z.Ok)
    {B : Fin 2 → ℝ} {lam : ℝ} (hlam : lam ≠ 0) {S : Set (α × ℝ)} (hS : MeasurableSet S)
    (W : ℝ≥0∞) (cond : α × ℝ → Prop) (cond' : α × ℝ → Prop)
    (hcond : ∀ z, cond' (zoomTime Z.t₀ Z.q z) ↔ cond z)
    {δ σ C : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hC : 0 ≤ C)
    (hres : ∀ i, (∑ j, |Zoom.baseMat Z B lam i j| * δ) ≤ σ)
    (horig : ∀ q : Fin 3 → ℤ, μ₀ {z | baseMesh δ (Zoom.baseOf (b z.1) z.2) = q ∧
      (z ∈ S ∧ cond z)} ≤ ENNReal.ofReal (C * δ ^ 3))
    (q' : Fin 3 → ℤ)
    (hmeas : MeasurableSet {z : α × ℝ |
      baseMesh σ (Zoom.baseOf (Zoom.nCoeff Z B lam (b z.1)) z.2) = q' ∧ cond' z}) :
    zoomLaw μ₀ S Z.t₀ Z.q W {z | baseMesh σ (Zoom.baseOf (Zoom.nCoeff Z B lam (b z.1)) z.2) = q' ∧
        cond' z} ≤
      W⁻¹ * ENNReal.ofReal (27 * C * |(Zoom.baseMat Z B lam).det|⁻¹ * σ ^ 3) := by
  rw [zoomLaw_apply μ₀ hS _ _ W hmeas]
  gcongr
  have h := affine_mesh_cell_cap μ₀ (fun z => Zoom.baseOf (b z.1) z.2) (fun z => z ∈ S ∧ cond z)
    (Zoom.baseMat Z B lam) (Zoom.baseVec Z B lam) (Zoom.det_baseMat_ne hZ hlam) hδ hσ hC hres
    horig q'
  refine le_trans (measure_mono ?_) h
  rintro z ⟨hzS, hz1, hz2⟩
  refine ⟨?_, hzS, (hcond z).mp hz2⟩
  have := Zoom.baseOf_nCoeff (B := B) hZ hlam (b z.1) z.2
  simp only [zoomTime] at hz1
  rw [← this]
  exact hz1

end

end Submission.Obl.k4_row_parent_contact_candidates
