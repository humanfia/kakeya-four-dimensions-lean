import Submission.Obl.k4_terminal_time_extension.SplitInterfaces
import Submission.Obl.k4_local_algebraic_graph_matching
import Submission.Obl.k4_quadratic_sheet_continuation
import Submission.Obl.k4_terminal_representative_atlas
import Submission.Obl.k4_quadratic_atlas_normalization

namespace Submission.Obl.k4_terminal_time_extension

/-- The analytic comparisons construct representatives; normalization supplies
exact chart bounds on a slightly coarser fitting depth. -/
theorem terminal_extension_from_children : MatchingInput → TerminalExtension := by
  intro hMatch
  have hGraph : GraphMatching := Submission.k4_local_algebraic_graph_matching hMatch
  have hPath : Continuation := Submission.k4_quadratic_sheet_continuation
  have hPreliminary : PreliminaryExtension :=
    Submission.k4_terminal_representative_atlas hGraph hPath
  have hNormalize : AtlasNormalization := Submission.k4_quadratic_atlas_normalization
  intro d₀ S η hd₀ hS hη
  obtain ⟨Cr, cr, hCr, hcr, hPreliminary⟩ := hPreliminary d₀ S η hd₀ hS hη
  have hC : 0 < 20 * Cr := mul_pos (by norm_num) hCr
  refine ⟨20 * Cr, min cr ((20 * Cr)⁻¹), hC,
    lt_min hcr (inv_pos.mpr hC), ?_⟩
  intro N K L d W ω ν E P B f g G hprob hd h e he heh heL htrue
  have hdata := hprob
  rcases hdata with ⟨hN, hNt, hK, hL, hdpos, hdlt, hS', hη', htemp, hrest⟩
  obtain ⟨Mp, Dp, htemp⟩ := htemp
  have hω : ∀ k γ, 0 ≤ ω k γ := fun k => (htemp k).2.1
  have hωsum : ∀ k, (∑ γ, ω k γ) = 1 := fun k => (htemp k).2.2.1
  have hν : ∀ k γ, MeasureTheory.IsProbabilityMeasure (ν k γ) :=
    fun k γ => ((htemp k).2.2.2.1 γ).1
  have hB : ∃ Mb : ℕ, ∀ k γ,
      0 < B k γ ∧ B k γ ≤ N k ^ Mb ∧ (B k γ)⁻¹ ≤ N k ^ Mb := by
    refine ⟨Mp, ?_⟩
    intro k γ
    have hw := (htemp k).2.2.2.1 γ
    exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2.1⟩
  have hecr : e < cr * L :=
    lt_of_lt_of_le heL (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le)
  have hesmall : e < (20 * Cr)⁻¹ * L :=
    lt_of_lt_of_le heL (mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le)
  have haL : 20 * (Cr * e) < L := by
    have hh := (lt_inv_mul_iff₀ hC).mp hesmall
    nlinarith
  have hrough := hPreliminary N K L d W ω ν E P B f g G hprob hd h e he heh hecr htrue
  obtain ⟨r, hr, hrL, hloss, hknown⟩ :=
    hNormalize N W ω ν E B L (Cr * e) (h - e) hN hNt hL
      (mul_pos hCr he) haL hω hωsum hν hB hrough
  refine ⟨r, hr, hrL, ?_, hknown⟩
  nlinarith

end Submission.Obl.k4_terminal_time_extension
