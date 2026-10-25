import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepStruct

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepData

open MeasureTheory Set

variable (D : PrepData)

/-- Witness-only copies preserve each original list-membership event. -/
theorem copied_list_format {N L : ℝ} {M D₀ : ℕ}
    (hfmt : ∀ γ b, MeasurableSet {p | b ∈ D.lst γ (obs (D.B γ) (δ N L) p)} ∧
      ∀ i, fmt 7 (N ^ M) D₀ {r : Fin 7 → ℝ |
        b ∈ D.lst γ (obs (D.B γ) (δ N L)
          ((i, fun z : Fin 6 => r z.castSucc), r 6))}) :
    ∀ γ s, MeasurableSet {p | s ∈ D.lst' γ (obs (D.B γ) (δ N L) p)} ∧
      ∀ i, fmt 7 (N ^ M) D₀ {r : Fin 7 → ℝ |
        s ∈ D.lst' γ (obs (D.B γ) (δ N L)
          ((i, fun z : Fin 6 => r z.castSucc), r 6))} := by
  intro γ s
  simpa only [D.mem_lst'] using hfmt γ (D.chartOf s)

/-- There are at most as many used frames as old labels. -/
theorem frames_card_le : D.J ≤ D.C := frameKeys_card_le _ _ _ _ _ _ _ _

/-- The finite source/witness family has polynomial size. -/
theorem entries_card_le : D.m ≤ D.C ^ 2 := by
  have hm : D.m ≤ D.C * D.J := by
    have hc := Finset.card_le_univ D.valid
    simpa only [m, Fintype.card_prod, Fintype.card_fin] using hc
  calc
    D.m ≤ D.C * D.J := hm
    _ ≤ D.C * D.C := Nat.mul_le_mul_left _ D.frames_card_le
    _ = D.C ^ 2 := by ring

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepData
