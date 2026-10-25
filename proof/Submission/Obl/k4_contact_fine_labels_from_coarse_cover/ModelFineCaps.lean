-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ModelFineCaps.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.FrozenCellCaps
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ShiftCalibration
import Submission.Lib.K4AffineMeshCaps

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Lib.K4AffineMeshCaps (baseMesh)

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Fine ceilings for a regular true quadratic, in the original incidence
law. Calibrating only its shifted base parts retains the original native
bin ceiling and any numerator included in that ceiling. -/
theorem original_shifted_fine_cell_cap (hp : p.Valid) {k : ℕ}
    (C : Set (α × ℝ)) (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
    (hF : F.totalDegree ≤ 2) {a A δ H : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H)
    (hFγ : ∀ e, |(restrictBase (translatedTest L F)).coeff e| ≤ A)
    (hFβ : ∀ e, |(restrictBase (pderiv 3 (translatedTest L F))).coeff e| ≤ A)
    (hPγ : ∀ e, |(restrictBase (translatedTest L (p.P k))).coeff e| ≤ A)
    (hPβ : ∀ e, |(restrictBase (pderiv 3 (translatedTest L (p.P k)))).coeff e| ≤ A)
    (hmesh : 216 * A * (2 * p.K k) ^ 2 * (1 + H) * δ ≤ a ∧
      216 * A * (2 * p.K k) ^ 2 * (1 + H) * δ ≤ (2 * p.K k)⁻¹)
    (hgood : ∀ u ∈ C, p.GoodPoint k u)
    (hclose : ∀ u ∈ C,
      |p.x k u.1 u.2 3 - eval (p.x k u.1 u.2) (Submission.Lib.K4ContactNormalization.affineBase L)| ≤ H)
    (hfit : ∀ u ∈ C, |eval (p.x k u.1 u.2) F| ≤ p.K k * a ∧
      (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 F)|)
    (cap : (Fin 3 → ℤ) → ENNReal)
    (hcap : ∀ (r : Fin 3 → ℤ) (j : ℤ), p.μ k {u |
      baseMesh δ (p.base k u) = r ∧ ⌊eval (p.x k u.1 u.2) (p.P k) / a⌋ = j} ≤ cap r)
    (r : Fin 3 → ℤ) :
    p.μ k {u | baseMesh δ (p.base k u) = r ∧ u ∈ C} ≤
      ENNReal.ofReal (320 * p.K k ^ 3) * cap r := by
  let hidden := fun u : α × ℝ => p.x k u.1 u.2 3 -
    eval (p.x k u.1 u.2) (Submission.Lib.K4ContactNormalization.affineBase L)
  let native := fun u : α × ℝ => eval (p.x k u.1 u.2) (p.P k)
  let S : Set (α × ℝ) := {u | baseMesh δ (p.base k u) = r ∧ u ∈ C}
  let T : Set (α × ℝ) := {u | baseMesh δ (p.base k u) = r}
  have hid (u : α × ℝ) : Fin.snoc (p.base k u) (hidden u) =
      point (residualCoeff L 1 (p.b k u.1)) u.2 := by
    have hb : Fin.init (point (p.b k u.1) u.2) = p.base k u := init_point_eq_base p k u
    simpa only [hb, hidden, x] using (point_residualCoeff_one L (p.b k u.1) u.2).symm
  have hev (Q : MvPolynomial (Fin 4) ℝ) (u : α × ℝ) :
      eval (Fin.snoc (p.base k u) (hidden u)) (translatedTest L Q) =
        eval (p.x k u.1 u.2) Q := by
    rw [hid, eval_translatedTest_residual]
    rfl
  have hpd (Q : MvPolynomial (Fin 4) ℝ) (u : α × ℝ) :
      eval (Fin.snoc (p.base k u) (hidden u)) (pderiv 3 (translatedTest L Q)) =
        eval (p.x k u.1 u.2) (pderiv 3 Q) := by
    rw [pderiv_translatedTest, hev]
  apply original_frozen_cell_cap (p.μ k) S T (fun _ hu => hu.1)
    (p.base k) hidden native (translatedTest L F) (translatedTest L (p.P k))
    ((translatedTest_degree L F).trans hF)
    ((translatedTest_degree L (p.P k)).trans (hp.basic k).2.2.2.2.2.2.2.1)
    (hp.K_ge k) ha ha1 hA (by linarith [hp.K_ge k]) hδ.le hδ1 hH
    hFγ hFβ hPγ hPβ hmesh
  · intro u hu
    exact GoodPoint.base_bounded p hp (hgood u hu.2)
  · intro u hu u' hu' i
    exact Submission.Lib.K4AffineMeshCaps.meshBox_coordinate_distance hδ hu'.1 hu.1 i
  · intro u hu
    exact hclose u hu.2
  · intro u hu
    rw [hev, hpd]
    exact hfit u hu.2
  · intro u hu
    rw [hev, hpd]
    exact ⟨rfl, ((hgood u hu.2).fit u.2 (hgood u hu.2).time).2.1⟩
  · rw [curvature_translatedTest L (p.P k) (hp.basic k).2.2.2.2.2.2.2.1]
    exact Valid.native_curvature_bound p hp k
  · intro j
    exact hcap r j

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
