-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.TotalCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.Covering
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.Covering

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

/-- A single cover at the bottom scale supplies every zero-dimensional AD bound. -/
lemma intervalAD_zero_of_cover {δ C : ℝ} {A : Set ℝ}
    (h : ∃ (m : ℕ) (c : Fin m → ℝ), A ⊆ ⋃ j, closedBall (c j) δ ∧ (m : ℝ) ≤ C) :
    IntervalAD δ 0 C A := by
  obtain ⟨m, c, hc, hm⟩ := h
  intro r R a hδr _
  refine ⟨m, c, ?_, by simpa only [Real.rpow_zero, mul_one] using hm⟩
  rintro x ⟨hx, _⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
  exact mem_iUnion.mpr ⟨j, closedBall_subset_closedBall hδr hj⟩

/-- A bounded scalar AD set has a uniform cover at its bottom scale. -/
lemma IntervalAD.cover_bounded {δ α C a R : ℝ} {A : Set ℝ}
    (h : IntervalAD δ α C A) (hR : δ ≤ R) (hA : A ⊆ Icc a (a + R)) :
    ∃ (m : ℕ) (c : Fin m → ℝ), A ⊆ ⋃ j, closedBall (c j) δ ∧
      (m : ℝ) ≤ C * (R / δ) ^ α := by
  obtain ⟨m, c, hc, hm⟩ := h δ R a le_rfl hR
  exact ⟨m, c, fun x hx => hc ⟨hx, hA hx⟩, hm⟩

/-- The uniform-cover form is compatible with the cell argument's AD convention. -/
lemma assouad_zero_of_cover {δ C : ℝ} {A : Set ℝ}
    (h : ∃ (m : ℕ) (c : Fin m → ℝ), A ⊆ ⋃ j, closedBall (c j) δ ∧ (m : ℝ) ≤ C) :
    CellProofs.Assouad δ 0 C A := intervalAD_zero_of_cover h

end WangZahlLot.Obl.wz_slab_local_linearity
