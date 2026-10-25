-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.RichStripSet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.RichStrip

/-!
# The rich-strip count in Set/ncard form

The statement of the rich-strip child of the split of o141 (session x0397),
proved from `rich_strip_count_finset` with `A = 16000`.
-/

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

open scoped Classical

theorem frostman_rich_strip_count : ∃ A : ℝ, 0 < A ∧ ∀ r C l : ℝ, 0 < r → r ≤ 1 → 1 ≤ C → 0 < l → ∀ (Y : Set (EuclideanSpace ℝ (Fin 2))) (J : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Y.Finite → Y.Nonempty → (∀ y ∈ Y, ‖y‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((Y ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * Y.ncard) → J.Finite → (∀ q ∈ J, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 ∧ l * Y.ncard ≤ ({y ∈ Y | |inner ℝ (y - q.1) q.2| < r}.ncard : ℝ)) → (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) → l ^ 2 * J.ncard ≤ A * C * (1 + Real.log (1 / r)) := by
  refine ⟨16000, by norm_num, ?_⟩
  intro r C l hr hr1 hC hl Y J hY hYne hY4 hFr hJ hJmem hJsep
  set Ys := hY.toFinset with hYs
  set Js := hJ.toFinset with hJs
  have hYcard : Y.ncard = Ys.card := Set.ncard_eq_toFinset_card Y hY
  have hJcard : J.ncard = Js.card := Set.ncard_eq_toFinset_card J hJ
  have hfilter : ∀ p : E2 → Prop, ({y ∈ Y | p y}.ncard : ℝ) = ((Ys.filter p).card : ℝ) := by
    intro p
    have : ({y ∈ Y | p y} : Set E2) = ↑(Ys.filter p) := by
      ext y; simp [hYs]
    rw [this, Set.ncard_coe_finset]
  have hYne' : Ys.Nonempty := by
    obtain ⟨y, hy⟩ := hYne; exact ⟨y, by simp [hYs, hy]⟩
  have hY4' : ∀ y ∈ Ys, ‖y‖ ≤ 4 := fun y hy => hY4 y (by simpa [hYs] using hy)
  have hFr' : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((Ys.filter (fun z => z ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Ys.card := by
    intro x ρ hρ
    have h := hFr x ρ hρ
    rw [← Set.sep_mem_eq, hfilter, hYcard] at h
    exact h
  have hJ' : ∀ j ∈ Js, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1 := by
    intro j hj
    have hj' : j ∈ J := by simpa [hJs] using hj
    exact ⟨(hJmem j hj').1, (hJmem j hj').2.1⟩
  have hsep' : (Js : Set (E2 × E2)).Pairwise (StripSep r) := by
    intro q hq q' hq' hne
    have hq1 : q ∈ J := by simpa [hJs] using hq
    have hq2 : q' ∈ J := by simpa [hJs] using hq'
    exact hJsep q hq1 q' hq2 hne
  have hrich' : ∀ j ∈ Js, l * Ys.card ≤
      ((Ys.filter (fun y => |inner ℝ (y - j.1) j.2| < r)).card : ℝ) := by
    intro j hj
    have hj' : j ∈ J := by simpa [hJs] using hj
    have h := (hJmem j hj').2.2
    rw [hfilter, hYcard] at h
    exact h
  have := rich_strip_count_finset hr hr1 (by linarith) hl.le Ys hYne' hY4' hFr' Js hJ' hsep' hrich'
  rw [hJcard]
  exact this

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
