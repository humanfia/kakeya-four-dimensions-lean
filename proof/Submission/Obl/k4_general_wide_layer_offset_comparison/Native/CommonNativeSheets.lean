-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/CommonNativeSheets.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/CommonNativeSheets.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ParentFrameBounds
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ParentNativeSheets
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetAffine

/-!
# True native sheets in a common comparison domain

A native sheet of a true parent lives in the parent's support zoom (`parent_native_sheets`).
A comparison domain has its own coordinates `CommonDomain.coords q χ g m code`, with explicit
inverse `physicalBase = affineBase (physicalMatrix) (physicalOffset)` (x0934). Composing the
zoom `x ↦ A x + bZ` with that inverse gives the real affine map
`commonMatrix = A * physicalMatrix`, `commonOffset = A (physicalOffset) + bZ`.

`common_sheet_of_sheetOn`: if this map sends the complex ball of radius `4` into the stable
ball of a frame sheet, the composed function is an `IsSheet 4`, bounded by the frame bound,
`4V`-Lipschitz on the real ball of radius `1/2`, and at the common coordinates of EVERY
physical point it equals the frame sheet at that point's zoomed base (`affC_common_coords`), so
every stored witness inherits its native fit.

`parent_common_sheet` instantiates this for an actual true parent of accepted o253's prepared
model, with x0934's `actual_parent_sheet_ball` (on origin/x0934, fa925ae3) for the containment.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set MvPolynomial
open Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel

noncomputable section

/-- The offset of a native frame `x ↦ A x + bZ` composed with the common-domain inverse. -/
def commonOffset (A : Matrix (Fin 3) (Fin 3) ℝ) (bZ : Fin 3 → ℝ) (q χ m : ℝ) (code : Code) :
    Fin 3 → ℝ :=
  A.mulVec (physicalOffset q χ m code) + bZ

/-- The linear part of that composition. -/
def commonMatrix (A : Matrix (Fin 3) (Fin 3) ℝ) (q χ g m : ℝ) (code : Code) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  A * physicalMatrix q χ g m code

theorem affR_eq_affineBase (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    affR b M (WithLp.toLp 2 v) =
      WithLp.toLp 2 (Submission.Lib.K4AffineMeshCaps.affineBase M b v) := by
  ext i
  simp [affR, Submission.Lib.K4AffineMeshCaps.affineBase, Matrix.mulVec, dotProduct, add_comm]

/-- **Exact pullback.** At the common coordinates of any physical point, the composed map is
the native frame point of that physical point. -/
theorem affC_common_coords (A : Matrix (Fin 3) (Fin 3) ℝ) (bZ : Fin 3 → ℝ) {q χ g m : ℝ}
    (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m) (code : Code) (x : Fin 3 → ℝ) :
    affC (commonOffset A bZ q χ m code) (commonMatrix A q χ g m code)
        (emb (WithLp.toLp 2 (coords q χ g m code x))) =
      emb (WithLp.toLp 2 (Submission.Lib.K4AffineMeshCaps.affineBase A bZ x)) := by
  rw [affC_emb, affR_eq_affineBase]
  congr 2
  unfold commonOffset commonMatrix
  rw [← affineBase_common_comp, physicalBase_coords hq.ne' hχ.ne' hm.ne']

/-- **A frame sheet in common coordinates.** -/
theorem common_sheet_of_sheetOn {Rel : MvPolynomial (Fin 4) ℂ}
    {g : EuclideanSpace ℂ (Fin 3) → ℂ} {c : EuclideanSpace ℝ (Fin 3)} {r V : ℝ}
    (hS : SheetOn Rel g c r V) (hRel : Rel ≠ 0) (hRd : Rel.totalDegree ≤ 4) (hV : 0 ≤ V)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (bZ : Fin 3 → ℝ) (hA : A.det ≠ 0)
    {q χ g' m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m) (code : Code)
    (hball : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      affC (commonOffset A bZ q χ m code) (commonMatrix A q χ g' m code) z ∈ ball (emb c) r) :
    IsSheet 4 (fun z => g (affC (commonOffset A bZ q χ m code) (commonMatrix A q χ g' m code) z)) ∧
    (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      ‖g (affC (commonOffset A bZ q χ m code) (commonMatrix A q χ g' m code) z)‖ ≤ V) ∧
    LipschitzOnWith ⟨4 * V, by positivity⟩
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        g (affC (commonOffset A bZ q χ m code) (commonMatrix A q χ g' m code) (emb x)))
      (closedBall 0 (1 / 2)) ∧
    ∀ x : Fin 3 → ℝ,
      g (affC (commonOffset A bZ q χ m code) (commonMatrix A q χ g' m code)
          (emb (WithLp.toLp 2 (coords q χ g' m code x)))) =
        g (emb (WithLp.toLp 2 (Submission.Lib.K4AffineMeshCaps.affineBase A bZ x))) := by
  have hdet : IsUnit (commonMatrix A q χ g' m code).det :=
    isUnit_iff_ne_zero.mpr (common_comp_det_ne_zero A hA hq hχ hm code)
  obtain ⟨hsheet, hbound⟩ := hS.isSheet_affine hRel hRd (commonOffset A bZ q χ m code)
    (commonMatrix A q χ g' m code) hdet hball
  have hdiff : DifferentiableOn ℂ
      (fun z => g (affC (commonOffset A bZ q χ m code) (commonMatrix A q χ g' m code) z))
      (ball 0 4) := by
    obtain ⟨_, _, _, hd, _⟩ := hsheet
    exact hd
  refine ⟨hsheet, hbound, lipschitz_of_bounded hV hdiff hbound, fun x => ?_⟩
  rw [affC_common_coords A bZ hq hχ hm code x]

/-! ### Actual true parents -/

theorem parentSupportZoom_baseMatrix {α : Type} [MeasurableSpace α] (p : Parameters)
    (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) :
    (a.parentSupportZoom p k s i).baseMatrix =
      parentMatrix (p.K k) (a.q k s) (narrow p k s) (a.c k s i) := by
  ext e f
  fin_cases e <;> fin_cases f <;>
    simp [PreparedModel.parentSupportZoom, supportZoom, Zoom.baseMatrix, parentMatrix] <;>
    ring

theorem parentZoomPoint_base {α : Type} [MeasurableSpace α] (p : Parameters)
    (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) (z : α × ℝ) :
    rootBaseCoordinates (parentZoomPoint p a k s i z) =
      Submission.Lib.K4AffineMeshCaps.affineBase
        (parentMatrix (p.K k) (a.q k s) (narrow p k s) (a.c k s i))
        (a.parentSupportZoom p k s i).baseShift (point (a.b k z.1) z.2) := by
  unfold parentZoomPoint
  rw [Zoom.nativePoint_base, a.nativePoint_base k z, parentSupportZoom_baseMatrix]
  rfl

/-- **The common-domain true sheet of an actual parent.** From the native sheet at the zoomed
base of one retained incidence `z₀` of the parent (`parent_native_sheets`) and the small-domain
hypotheses of `actual_parent_sheet_ball` at `z₀`: the composed sheet on the comparison domain
of `z₀` is an `IsSheet 4`, bounded, Lipschitz, and at every physical point it is the parent's
native sheet at that point's zoomed base. -/
theorem parent_common_sheet {α : Type} [MeasurableSpace α] (p : Parameters)
    (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s))
    {Rel : MvPolynomial (Fin 4) ℂ} {g : EuclideanSpace ℂ (Fin 3) → ℂ} {ρ V : ℝ}
    (z₀ : α × ℝ)
    (hS : SheetOn Rel g (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z₀))) (4 * ρ) V)
    (hRel : Rel ≠ 0) (hRd : Rel.totalDegree ≤ 4) (hV : 0 ≤ V)
    {q χ g' m : ℝ} (hK : 1 ≤ p.K k) (hQ : 0 < a.q k s) (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hgg : g' = narrow p k s) (hg : 0 < g') (hg1 : g' ≤ 1) (hχg : χ ≤ g') (hm : 0 < m)
    (hqg : q * g' ≤ m) (hρ : 0 < ρ) (ht : z₀.2 ∈ Icc (0 : ℝ) 1)
    (hqsmall : q ≤ ρ * a.q k s / 10000) (hχsmall : χ ≤ ρ * (a.q k s * g') / 10000)
    (hmsmall : m ≤ ρ * (a.q k s * g') / 10000)
    (hc : |a.c k s i 4| ≤ p.K k) (hb : |a.b k z₀.1 3| ≤ p.K k)
    (hslope : |a.b k z₀.1 4 - a.c k s i 3 - a.c k s i 4 * a.b k z₀.1 3| ≤ p.K k * g') :
    let A := parentMatrix (p.K k) (a.q k s) (narrow p k s) (a.c k s i)
    let bZ := (a.parentSupportZoom p k s i).baseShift
    let code₀ := code q χ g' m (a.b k z₀.1) z₀.2
    IsSheet 4 (fun z => g (affC (commonOffset A bZ q χ m code₀) (commonMatrix A q χ g' m code₀) z)) ∧
    (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      ‖g (affC (commonOffset A bZ q χ m code₀) (commonMatrix A q χ g' m code₀) z)‖ ≤ V) ∧
    LipschitzOnWith ⟨4 * V, by positivity⟩
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        g (affC (commonOffset A bZ q χ m code₀) (commonMatrix A q χ g' m code₀) (emb x)))
      (closedBall 0 (1 / 2)) ∧
    ∀ x : Fin 3 → ℝ,
      g (affC (commonOffset A bZ q χ m code₀) (commonMatrix A q χ g' m code₀)
          (emb (WithLp.toLp 2 (coords q χ g' m code₀ x)))) =
        g (emb (WithLp.toLp 2 (Submission.Lib.K4AffineMeshCaps.affineBase A bZ x))) := by
  intro A bZ code₀
  subst hgg
  have hA : A.det ≠ 0 :=
    parentMatrix_det_ne_zero (by linarith) hQ hg (a.c k s i)
  have hcont := actual_parent_sheet_ball hK hQ hq hχ hχ1 hg hg1 hχg hm hqg hρ ht hqsmall
    hχsmall hmsmall (a.b k z₀.1) (a.c k s i) bZ hc hb hslope
  have hcenter : toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z₀)) =
      WithLp.toLp 2 (Submission.Lib.K4AffineMeshCaps.affineBase A bZ
        (point (a.b k z₀.1) z₀.2)) := by
    rw [parentZoomPoint_base]
  have hball : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      affC (commonOffset A bZ q χ m code₀) (commonMatrix A q χ (narrow p k s) m code₀) z ∈
        ball (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z₀)))) (4 * ρ) := by
    intro z hz
    have h1 := hcont z hz
    rw [hcenter]
    exact ball_subset_ball (by linarith) h1
  exact common_sheet_of_sheetOn hS hRel hRd hV A bZ hA hq hχ hm code₀ hball

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
