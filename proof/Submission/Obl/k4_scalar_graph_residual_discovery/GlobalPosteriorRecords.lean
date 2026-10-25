/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file GlobalPosteriorRecords.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalPosteriorLists
import Submission.Obl.k4_scalar_graph_residual_discovery.FiniteRecords
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomParameterCount

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

/-- Finite base records and finite incidence lists give a finite ACTUAL
product record image. Its ambient cardinality is not a loss budget. -/
theorem finite_listed_product_record_image {X A B : Type*}
    (E : Set X) (record : X → A × B) (lists : B → Finset A)
    (hbase : ((fun p => (record p).2) '' E).Finite)
    (hlisted : ∀ p ∈ E, (record p).1 ∈ lists (record p).2) :
    (record '' E).Finite := by
  classical
  let base := hbase.toFinset
  let F := base.biUnion (fun b => (lists b).image (fun a => (a, b)))
  apply F.finite_toSet.subset
  rintro _ ⟨p, hp, rfl⟩
  exact Finset.mem_biUnion.mpr ⟨(record p).2, hbase.mem_toFinset.mpr ⟨p, hp, rfl⟩,
    Finset.mem_image.mpr ⟨(record p).1, hlisted p hp, rfl⟩⟩

namespace Zoom

/-- The posterior record is defined globally before selecting a
coefficient world. The zoom code uses each trajectory's OWN coarse-bin
normalized coefficients and retains the original fine state and palette. -/
def posteriorEntryRecord (ρ b r : ℝ) (p : ScalarIncidence) :
    ((Fin 5 → ℤ) × (Fin 3 → ℤ)) × ((Fin 3 → ℤ) × ℤ) :=
  ((cell ρ p.1.2, quadraticCoordinateCode r (normalizedCoeff ρ p.1) p.2),
    (cell b (scalarPosition p), cell ρ p.1.2 1))

theorem measurable_posteriorEntryRecord (ρ b r : ℝ) : Measurable (posteriorEntryRecord ρ b r) := by
  have hc : Measurable (fun p : ScalarIncidence => cell ρ p.1.2) :=
    measurable_cell ρ (measurable_snd.comp measurable_fst)
  have hz : Measurable (fun p : ScalarIncidence =>
      quadraticCoordinateCode r (normalizedCoeff ρ p.1) p.2) := by
    have hm := measurable_normalizedCoeff ρ
    unfold quadraticCoordinateCode quadraticCoordinates
    fun_prop
  exact (hc.prodMk hz).prodMk
    ((measurable_cell b measurable_scalarPosition).prodMk ((measurable_pi_apply 1).comp hc))

theorem posteriorEntryRecord_eq {ρ : ℝ} (hρ : 0 < ρ) (b r : ℝ) (p : ScalarIncidence) :
    posteriorEntryRecord ρ b r p =
      ((cell ρ p.1.2, cell r (position ρ (cell ρ p.1.2) p)),
        (cell b (scalarPosition p), cell ρ p.1.2 1)) := by
  unfold posteriorEntryRecord
  rw [quadraticCoordinateCode_normalizedCoeff hρ rfl]

/-- The actual bounded original labels and original posterior incidence
lists construct the finite record image used in global reference pruning. -/
theorem posteriorEntryRecord_finite (E : Set ScalarIncidence) {ρ b H : ℝ}
    (hρ : 0 < ρ) (hb : 0 < b) (hH : 1 ≤ H) (r : ℝ)
    (hcoeff : ∀ p ∈ E, ∀ e, |p.1.2 e| ≤ H) (htime : ∀ p ∈ E, |p.2| ≤ 1)
    (lists : ((Fin 3 → ℤ) × ℤ) → Finset ((Fin 5 → ℤ) × (Fin 3 → ℤ)))
    (hlisted : ∀ p ∈ E, (posteriorEntryRecord ρ b r p).1 ∈ lists (posteriorEntryRecord ρ b r p).2) :
    (posteriorEntryRecord ρ b r '' E).Finite := by
  have hW := finite_original_physical_records E hH hb hcoeff htime
  have hC := finite_original_coefficient_records E (by linarith : 0 ≤ H) hρ hcoeff
  have hbase : ((fun p => (posteriorEntryRecord ρ b r p).2) '' E).Finite := by
    apply (hW.prod (hC.image (fun q : Fin 5 → ℤ => q 1))).subset
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, ⟨cell ρ p.1.2, ⟨p, hp, rfl⟩, rfl⟩⟩
  exact finite_listed_product_record_image E (posteriorEntryRecord ρ b r) lists hbase hlisted

end Zoom

end

end Submission.Obl.k4_scalar_graph_residual_discovery
