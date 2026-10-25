/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PosteriorFinalCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.EntryReferences

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal

/-- A finite family of posterior-entry thresholds has the same globally
summed OLD reference budget as the countable complete family. -/
theorem finite_product_entry_reference_budget {A Q V : Type*} [DecidableEq A]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (old : Q → ENNReal) (π : Measure V) (L : Q × V → Finset A) (D η : ENNReal)
    (hD : ∀ b, ((L b).card : ENNReal) ≤ D) (F : Finset (A × (Q × V))) :
    (∑ e ∈ F, η * productEntryReference old π L e) ≤
      η * D * ((∑' q, old q) * π univ) := by
  rw [← Finset.mul_sum]
  exact (mul_le_mul_right ((ENNReal.sum_le_tsum F).trans
    (sum_productEntryReference_le old π L D hD)) η).trans_eq (by ring)

/-- The posterior palette cap uses an arbitrary final submeasure whose
entry floors have been restored simultaneously. No one-pass pruning
identity is required. -/
theorem posterior_palette_cap_of_final_floors {X A J : Type*} [MeasurableSpace X]
    (μ κ : Measure X) (hκ : κ ≤ μ) (entry : X → A) (fine : X → J)
    (old coarseWeight : A → ℝ≥0∞) (fineWeight : J → ℝ≥0∞) (C η : ℝ≥0∞)
    (hη₀ : η ≠ 0) (hηt : η ≠ ∞)
    (hcap : ∀ a j, μ {p | entry p = a ∧ fine p = j} ≤ C * old a * fineWeight j)
    (hfloor : ∀ a, κ (entry ⁻¹' {a}) = 0 ∨ η * old a * coarseWeight a ≤ κ (entry ⁻¹' {a}))
    (a : A) (hP₀ : coarseWeight a ≠ 0) (hPt : coarseWeight a ≠ ∞) (j : J) :
    κ {p | entry p = a ∧ fine p = j} ≤
      ((C * fineWeight j) / (η * coarseWeight a)) * κ (entry ⁻¹' {a}) := by
  rcases hfloor a with hzero | hfloor
  · calc
      _ ≤ κ (entry ⁻¹' {a}) := measure_mono (fun _ hp => hp.1)
      _ = 0 := hzero
      _ ≤ _ := zero_le
  · have hnum : κ {p | entry p = a ∧ fine p = j} ≤ (C * fineWeight j) * old a :=
      ((hκ _).trans (hcap a j)).trans_eq (by ring)
    have hden : (η * coarseWeight a) * old a ≤ κ (entry ⁻¹' {a}) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hfloor
    exact Zoom.cap_of_palette_floor (mul_ne_zero hη₀ hP₀)
      (ENNReal.mul_ne_top hηt hPt) hnum hden

end Submission.Obl.k4_scalar_graph_residual_discovery
