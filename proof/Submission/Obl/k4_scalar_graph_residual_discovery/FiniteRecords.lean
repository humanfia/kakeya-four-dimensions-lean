/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file FiniteRecords.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalRows
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts

noncomputable section

/-- The actual bounded point set has finitely many floor records at ANY
positive width. No preparation-mesh or positive-mass assumption is needed. -/
theorem finite_cell_image_of_abs_bound {X : Type*} {n : ℕ}
    (E : Set X) (Z : X → Fin n → ℝ) {δ H : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H)
    (hbound : ∀ z ∈ E, ∀ e, |Z z e| ≤ H) :
    (cell δ ∘ Z '' E).Finite ∧
      ((cell δ ∘ Z '' E).ncard : ℝ) ≤ (4 * H / δ + 2) ^ n := by
  have hdiam (e : Fin n) (z : X) (hz : z ∈ E) (z' : X) (hz' : z' ∈ E) :
      |Z z e - Z z' e| ≤ 2 * H :=
    (abs_sub _ _).trans (by linarith [hbound z hz e, hbound z' hz' e])
  have hh := Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts.records_finite_card
    E Z (fun _ => δ) (fun _ => 2 * H)
    (fun _ => hδ) (fun _ => by positivity) hdiam
  change (cell δ ∘ Z '' E).Finite ∧
    ((cell δ ∘ Z '' E).ncard : ℝ) ≤ ∏ _e : Fin n, (2 * (2 * H) / δ + 2) at hh
  simpa only [show (2 : ℝ) * (2 * H) = 4 * H by ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh

theorem scalarPosition_abs_le_three {H : ℝ} (hH : 1 ≤ H)
    (l : ScalarLine) (hcoeff : ∀ e, |l.2 e| ≤ H) {t : ℝ} (ht : |t| ≤ 1) :
    ∀ e, |scalarPosition (l, t) e| ≤ 3 * H := by
  have hH₀ : 0 ≤ H := by linarith
  have ht₂ : |t ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hprod (u : ℝ) (hu : |u| ≤ 1) (e : Fin 5) : |u * l.2 e| ≤ H := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hu (hcoeff e) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  intro e
  fin_cases e
  · change |t| ≤ 3 * H
    linarith
  · change |l.2 0 + t * l.2 1| ≤ 3 * H
    exact (abs_add_le _ _).trans (by linarith [hcoeff 0, hprod t ht 1])
  · change |l.2 2 + t * l.2 3 + t ^ 2 * l.2 4| ≤ 3 * H
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (by linarith [hcoeff 2, hprod t ht 3, hprod (t ^ 2) ht₂ 4])

/-- In particular the actual original fine-state image is finite, even
when the graph precision exponent is not on the preparation mesh. -/
theorem finite_original_physical_records
    (E : Set ScalarIncidence) {H b : ℝ} (hH : 1 ≤ H) (hb : 0 < b)
    (hcoeff : ∀ z ∈ E, ∀ e, |z.1.2 e| ≤ H)
    (htime : ∀ z ∈ E, |z.2| ≤ 1) :
    ((fun z => cell b (scalarPosition z)) '' E).Finite := by
  have hh := finite_cell_image_of_abs_bound E scalarPosition hb (by positivity : 0 ≤ 3 * H)
    (fun z hz => scalarPosition_abs_le_three hH z.1 (hcoeff z hz) (htime z hz))
  exact hh.1

/-- Every original coefficient grid has a finite actual record image
under the pointwise coefficient bounds inherited from preparation. -/
theorem finite_original_coefficient_records
    (E : Set ScalarIncidence) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 < β)
    (hcoeff : ∀ z ∈ E, ∀ e, |z.1.2 e| ≤ H) :
    ((fun z => cell β z.1.2) '' E).Finite :=
  (finite_cell_image_of_abs_bound E (fun z => z.1.2) hβ hH hcoeff).1

end

end Submission.Obl.k4_scalar_graph_residual_discovery
