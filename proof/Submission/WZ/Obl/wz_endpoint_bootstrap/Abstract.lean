-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_endpoint_bootstrap.Abstract.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_endpoint_bootstrap

/-- The endpoint argument only needs one-sided exponent comparisons and closure
in the error exponent. Strict improvement is used once, at an infimum. -/
theorem endpoint_of_shift
    (D : ℝ → ℝ → Prop)
    (hseed : D (1 / 2) 0)
    (hmono : ∀ s w w', w ≤ w' → D s w → D s w')
    (hshift : ∀ s t w, t ≤ s → D s w → D t (w + 2 * (s - t)))
    (hclosed : ∀ s w, (∀ e > 0, D s (w + e)) → D s w)
    (himprove : ∀ s w, 0 < s → s ≤ 1 / 2 → 0 < w → w ≤ 1 →
      D s w → ∃ g, 0 < g ∧ g ≤ w ∧ D s (w - g)) :
    D 0 0 := by
  have hpos : ∀ w, 0 < w → w ≤ 1 → D 0 w := by
    intro w hw hw1
    let S : Set ℝ := {s | 0 ≤ s ∧ s ≤ 1 / 2 ∧ D s w}
    have hhalf : (1 / 2 : ℝ) ∈ S :=
      ⟨by norm_num, le_rfl, hmono _ _ _ hw.le hseed⟩
    have hne : S.Nonempty := ⟨_, hhalf⟩
    have hbdd : BddBelow S := ⟨0, fun _ hs => hs.1⟩
    let s := sInf S
    have hs0 : 0 ≤ s := le_csInf hne (fun _ hs => hs.1)
    have hs1 : s ≤ 1 / 2 := csInf_le hbdd hhalf
    have hsD : D s w := by
      apply hclosed
      intro e he
      obtain ⟨t, ht, hte⟩ := exists_lt_of_csInf_lt hne
        (show sInf S < s + e / 2 by dsimp [s]; linarith)
      have hst : s ≤ t := csInf_le hbdd ht
      apply hmono s (w + 2 * (t - s)) (w + e) (by linarith)
      exact hshift t s w hst ht.2.2
    have hs_eq : s = 0 := by
      by_contra hn
      have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hn)
      obtain ⟨g, hg, hgw, hD⟩ := himprove s w hspos hs1 hw hw1 hsD
      let t := min (s / 2) (g / 4)
      have ht : 0 < t := lt_min (by linarith) (by linarith)
      have hts : t ≤ s / 2 := min_le_left _ _
      have htg : t ≤ g / 4 := min_le_right _ _
      have hmem : s - t ∈ S := by
        refine ⟨by linarith, by linarith, ?_⟩
        apply hmono (s - t) ((w - g) + 2 * (s - (s - t))) w (by linarith)
        exact hshift s (s - t) (w - g) (by linarith) hD
      have := csInf_le hbdd hmem
      change s ≤ s - t at this
      linarith
    simpa only [hs_eq] using hsD
  apply hclosed
  intro e he
  have hmin : 0 < min e 1 := lt_min he zero_lt_one
  exact hmono 0 (min e 1) (0 + e) (by simp) (hpos _ hmin (min_le_right _ _))

end WangZahlLot.Obl.wz_endpoint_bootstrap
