-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/HeavyPiece.lean
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Basic.ENNReal.BigOperators

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Set MeasureTheory

/-- One original piece of an almost-everywhere finite cover carries the
prescribed mass floor whenever the total light-piece budget is too small. -/
theorem exists_heavy_cover_piece {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (E : Set Ω) (D : ι → Set Ω) (δ : ENNReal)
    (hcover : ∀ᵐ u ∂μ, u ∈ E → ∃ i, u ∈ D i)
    (hmass : (Fintype.card ι : ENNReal) * δ < μ E) :
    ∃ i, δ ≤ μ (E ∩ D i) := by
  classical
  by_contra hex
  have hlight (i : ι) : μ (E ∩ D i) ≤ δ :=
    (lt_of_not_ge (fun h => hex ⟨i, h⟩)).le
  have hsub : E ≤ᵐ[μ] ⋃ i, E ∩ D i := by
    filter_upwards [hcover] with u hu hE
    obtain ⟨i, hi⟩ := hu hE
    exact mem_iUnion.mpr ⟨i, hE, hi⟩
  have hle : μ E ≤ (Fintype.card ι : ENNReal) * δ := by
    calc
      _ ≤ μ (⋃ i, E ∩ D i) := measure_mono_ae hsub
      _ ≤ ∑ i, μ (E ∩ D i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum (fun i _ => hlight i)
      _ = _ := by simp
  exact (not_lt_of_ge hle) hmass

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
