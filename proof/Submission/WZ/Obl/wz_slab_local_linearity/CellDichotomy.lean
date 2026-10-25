-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.Dichotomy
import Submission.WZ.Obl.wz_slab_local_linearity.NormalLine
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityApply

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

/-- Closed localization bounds imply the open localization bounds in the frozen theorem. -/
lemma CellProofs.ADset.planeAD {δ C : ℝ} {F : Set Plane}
    (h : CellProofs.ADset δ 1 C F) : PlaneAD δ C F := by
  intro x ρ r hδρ hρr
  obtain ⟨m, c, hc, hm⟩ := h x ρ r hδρ hρr
  refine ⟨m, c, (fun _ hx => hc ⟨hx.1, ball_subset_closedBall hx.2⟩), ?_⟩
  simpa only [Real.rpow_one] using hm

/-- The finite scalar-normal conclusion supplies the line form used by the cell proof. -/
theorem FiniteDichotomy.linearityDichotomy {σ : ℝ} (h : FiniteDichotomy σ) :
    CellProofs.LinearityDichotomy σ := by
  classical
  intro ε hε
  obtain ⟨η, δ₀, hη, hδ₀, hδ⟩ := h ε hε
  refine ⟨η, δ₀, hη, hδ₀, ?_⟩
  intro δ hδpos hδsmall Ks Js a b T D ha hb N hN hma hmb hADa hADb hT hcard hD hdot
  obtain ⟨e, c, he, hc⟩ := hδ δ hδpos hδsmall Ks Js a b T D ha hb N hN hma hmb
    hADa.planeAD hADb.planeAD hT hcard hD hdot
  refine ⟨c • e, perpendicular e, perpendicular_ne_zero he, hc.trans ?_⟩
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkK, hks⟩ := Finset.mem_filter.mp hk
  refine Finset.mem_filter.mpr ⟨hkK, ?_⟩
  have hl := mem_line_thickening_of_abs_inner he hks
  have hline : range (fun t : ℝ => c • e + t • perpendicular e) =
      CellProofs.lineThrough (c • e) (perpendicular e) := by
    ext q
    simp only [mem_range, CellProofs.lineThrough, mem_ofPred_eq]
    exact exists_congr (fun _ => eq_comm)
  rwa [hline] at hl

end WangZahlLot.Obl.wz_slab_local_linearity
