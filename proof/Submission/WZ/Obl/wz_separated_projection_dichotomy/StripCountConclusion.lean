-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripCountConclusion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripSlices

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- The counting version of the orthogonal-strip alternative. -/
def StripCountConclusion (δ ε : ℝ) (F G : Set Plane) : Prop :=
  ∃ e e' : Plane, ‖e‖ = 1 ∧ ‖e'‖ = 1 ∧ inner ℝ e e' = 0 ∧
    ∃ c c' : ℝ, δ ^ (ε - 1) ≤ ({a ∈ F | |inner ℝ a e - c| < δ}.ncard : ℝ) ∧
      δ ^ (ε - 1) ≤ ({b ∈ G | |inner ℝ b e' - c'| < δ}.ncard : ℝ)

theorem stripCountConclusion_of_containing_strips {F G : Finset Plane}
    {δ ε W c : ℝ} {e : Plane}
    (hFne : F.Nonempty) (hGne : G.Nonempty) (hδ : 0 < δ) (hδW : δ ≤ W) (he : ‖e‖ = 1)
    (hFstrip : ∀ a ∈ F, |inner ℝ a e| ≤ W)
    (hGstrip : ∀ b ∈ G, |inner ℝ b (perp e) - c| ≤ W)
    (hFcard : δ ^ (ε - 1) ≤ δ / (150 * W) * (F.card : ℝ))
    (hGcard : δ ^ (ε - 1) ≤ δ / (150 * W) * (G.card : ℝ)) :
    StripCountConclusion δ ε (↑F : Set Plane) (↑G : Set Plane) := by
  classical
  obtain ⟨c₁, F', hF', hF'strip, hF'card⟩ := exists_dense_strip_slice hFne hδ hδW
    (c := 0) (by simpa only [sub_zero] using hFstrip)
  obtain ⟨c₂, G', hG', hG'strip, hG'card⟩ := exists_dense_strip_slice hGne hδ hδW hGstrip
  have hW : 0 < W := hδ.trans_le hδW
  have hcF : δ ^ (ε - 1) ≤ (F'.card : ℝ) := by
    apply le_trans hFcard
    apply le_trans _ hF'card
    gcongr
    norm_num
  have hcG : δ ^ (ε - 1) ≤ (G'.card : ℝ) := by
    apply le_trans hGcard
    apply le_trans _ hG'card
    gcongr
    norm_num
  refine ⟨e, perp e, he, (perp_norm e).trans he, perp_inner e, c₁, c₂, ?_, ?_⟩
  · apply hcF.trans
    exact_mod_cast Set.ncard_le_ncard (s := (↑F' : Set Plane))
      (t := {a ∈ (↑F : Set Plane) | |inner ℝ a e - c₁| < δ})
      (by intro x hx; exact ⟨hF' hx, hF'strip x hx⟩)
      (F.finite_toSet.subset (by intro x hx; exact hx.1))
  · apply hcG.trans
    exact_mod_cast Set.ncard_le_ncard (s := (↑G' : Set Plane))
      (t := {b ∈ (↑G : Set Plane) | |inner ℝ b (perp e) - c₂| < δ})
      (by intro x hx; exact ⟨hG' hx, hG'strip x hx⟩)
      (G.finite_toSet.subset (by intro x hx; exact hx.1))

theorem StripCountConclusion.mono_set {δ ε : ℝ} {F G F' G' : Set Plane}
    (h : StripCountConclusion δ ε F G) (hF : F ⊆ F') (hG : G ⊆ G')
    (hF' : F'.Finite) (hG' : G'.Finite) : StripCountConclusion δ ε F' G' := by
  obtain ⟨e, e', he, he', hee', c, c', hFc, hGc⟩ := h
  refine ⟨e, e', he, he', hee', c, c', hFc.trans ?_, hGc.trans ?_⟩
  · exact_mod_cast Set.ncard_le_ncard (by intro x hx; exact ⟨hF hx.1, hx.2⟩)
      (hF'.subset (by intro x hx; exact hx.1))
  · exact_mod_cast Set.ncard_le_ncard (by intro x hx; exact ⟨hG hx.1, hx.2⟩)
      (hG'.subset (by intro x hx; exact hx.1))

end WangZahlLot.Obl.wz_separated_projection_dichotomy
