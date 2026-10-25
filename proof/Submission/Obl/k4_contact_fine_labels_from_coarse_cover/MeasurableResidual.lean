-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/MeasurableResidual.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelBase
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.HeavyLabelPiece
import Submission.Lib.K4ContactNormalization.HomogeneousCorrection

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem Valid.measurable_current_point (hp : p.Valid) (k : ℕ) :
    Measurable (fun u : α × ℝ => p.x k u.1 u.2) := by
  have hb : Measurable (fun u : α × ℝ => p.b k u.1) :=
    (hp.basic k).1.comp measurable_fst
  have hc (i : Fin 6) : Measurable (fun u : α × ℝ => p.b k u.1 i) :=
    (measurable_pi_apply i).comp hb
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_snd
  · exact (hc 0).add (measurable_snd.mul (hc 3))
  · exact (hc 1).add (measurable_snd.mul (hc 4))
  · exact (hc 2).add (measurable_snd.mul (hc 5))

/-- Only the observed affine residual is restricted during calibration.
The original coarse palette supplies this cover from its full-time fits. -/
def residualEvent (k : ℕ) (L : Fin 4 → ℝ) (H : ℝ) : Set (α × ℝ) :=
  {u | |p.x k u.1 u.2 3 - eval (p.x k u.1 u.2) (affineBase L)| ≤ H}

theorem Valid.measurableSet_residualEvent (hp : p.Valid) (k : ℕ)
    (L : Fin 4 → ℝ) (H : ℝ) : MeasurableSet (p.residualEvent k L H) := by
  have hx := Valid.measurable_current_point p hp k
  have hres : Measurable (fun u : α × ℝ => p.x k u.1 u.2 3 -
      eval (p.x k u.1 u.2) (affineBase L)) :=
    ((measurable_pi_apply 3).comp hx).sub ((affineBase L).continuous_eval.measurable.comp hx)
  exact measurableSet_le (continuous_abs.measurable.comp hres) measurable_const

/-- A full-time original coarse cover yields a measurable heavy state in
EVERY true label, without trimming or changing its original reference. -/
theorem exists_heavy_measurable_label_state (hp : p.Valid) {k : ℕ} {s H : ℝ}
    {i : Fin (p.n k s)} (hi : p.Label k s i) {M : ℕ}
    (hH : 0 < H) (hM : (M : ℝ) ≤ H) (L : Fin M → Fin 4 → ℝ)
    (hcover : ∀ᵐ u ∂p.μ k, ∃ a : Fin M, ∀ t ∈ Icc (0 : ℝ) 1,
      |p.x k u.1 t 3 - (L a 0 + L a 1 * t + L a 2 * p.x k u.1 t 1 +
        L a 3 * p.x k u.1 t 2)| ≤ H)
    (hB : MeasurableSet (p.B k s i)) (G : Set (α × ℝ)) (hG : MeasurableSet G)
    (hGae : ∀ᵐ u ∂p.μ k, u ∈ G) :
    ∃ a : Fin M, MeasurableSet (((p.B k s i ×ˢ p.I k s i) ∩ G) ∩
      p.residualEvent k (L a) H) ∧
      ENNReal.ofReal (1 / (2 * p.K k * H)) *
        (ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i)) ≤
        p.μ k (((p.B k s i ×ˢ p.I k s i) ∩ G) ∩ p.residualEvent k (L a) H) := by
  have hD : ∀ᵐ u ∂p.μ k, ∃ a, u ∈ p.residualEvent k (L a) H := by
    filter_upwards [hcover, Valid.ae_good p hp k] with u hu hgood
    obtain ⟨a, ha⟩ := hu
    refine ⟨a, ?_⟩
    have h := ha u.2 hgood.time
    simpa [residualEvent, affineBase, x, point] using h
  obtain ⟨a, ha⟩ := exists_heavy_label_piece p hp hi hH hM
    (fun a => p.residualEvent k (L a) H) hD G hGae
  refine ⟨a, ?_, ha⟩
  exact ((hB.prod (by exact measurableSet_Icc)).inter hG).inter
    (Valid.measurableSet_residualEvent p hp k (L a) H)

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
