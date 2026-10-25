-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseLocalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoverWeights

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric Finset

/-- A unit tube is contained in the ball of radius `ρ + 1/2` about its midpoint. -/
theorem tube_subset_midpoint_ball {ρ : ℝ} {x v : Space} (hv : ‖v‖ = 1) :
    Tube ρ x v ⊆ ball (x + (1 / 2 : ℝ) • v) (ρ + 1 / 2) := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hseg : dist (x + s • v) (x + (1 / 2 : ℝ) • v) ≤ 1 / 2 := by
    rw [dist_eq_norm, show x + s • v - (x + (1 / 2 : ℝ) • v) =
      (s - 1 / 2) • v by module, norm_smul, Real.norm_eq_abs, hv, mul_one]
    exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  exact (dist_triangle p (x + s • v) _).trans_lt (add_lt_add_of_lt_of_le hpq hseg)

/-- A thin unit tube meeting the unit ball has bounded midpoint. -/
theorem tube_midpoint_norm_le_two {ρ : ℝ} (hρ : ρ ≤ 1 / 4) {x v : Space}
    (hv : ‖v‖ = 1) (hmeet : (Tube ρ x v ∩ ball 0 1).Nonempty) :
    ‖x + (1 / 2 : ℝ) • v‖ ≤ 2 := by
  obtain ⟨p, hpT, hpB⟩ := hmeet
  have hd := tube_subset_midpoint_ball hv hpT
  have hn : ‖p‖ < 1 := by simpa using hpB
  have ht := norm_le_norm_add_norm_sub p (x + (1 / 2 : ℝ) • v)
  rw [norm_sub_rev, ← dist_eq_norm] at ht
  rw [dist_comm (x + (1 / 2 : ℝ) • v)] at ht
  change dist p (x + (1 / 2 : ℝ) • v) < ρ + 1 / 2 at hd
  linarith

/-- A fixed finite localization places a mass-retaining coarse subfamily in one translated
unit ball. Its loss is independent of the scale and the number of tubes. -/
theorem weighted_unit_ball_localization :
    ∃ K : ℕ, 0 < K ∧ ∀ (ρ : ℝ), ρ ≤ 1 / 4 →
      ∀ (N : ℕ) (y w : Fin N → Space), (∀ k, ‖w k‖ = 1) →
      (∀ k, (Tube ρ (y k) (w k) ∩ ball 0 1).Nonempty) →
      ∀ a : Fin N → ℝ, 0 < ∑ k, a k →
      ∃ (Q : Finset (Fin N)) (z : Space), Q.Nonempty ∧
        (∑ k, a k) ≤ K * ∑ k ∈ Q, a k ∧
        ∀ k ∈ Q, Tube ρ (y k) (w k) ⊆ ball z 1 := by
  classical
  obtain ⟨F, hF, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : Space) 2).totallyBounded (1 / 4) (by norm_num)
  let := hF.fintype
  have hFne : Nonempty F := by
    obtain ⟨c, hc, _⟩ := mem_iUnion₂.mp (hcover (show (0 : Space) ∈ closedBall 0 2 by simp))
    exact ⟨⟨c, hc⟩⟩
  let := hFne
  refine ⟨Fintype.card F, Fintype.card_pos, ?_⟩
  intro ρ hρ N y w hw hmeet a hmass
  have hex (k : Fin N) : ∃ c : F, dist (y k + (1 / 2 : ℝ) • w k) c < 1 / 4 := by
    have hk : y k + (1 / 2 : ℝ) • w k ∈ closedBall (0 : Space) 2 := by
      simpa only [mem_closedBall, dist_zero_right] using
        tube_midpoint_norm_le_two hρ (hw k) (hmeet k)
    obtain ⟨c, hc, hkc⟩ := mem_iUnion₂.mp (hcover hk)
    exact ⟨⟨c, hc⟩, hkc⟩
  choose color hcolor using hex
  obtain ⟨c, hmassc⟩ := wz_concentrated_convex_factorization.weight_class univ color a
  let Q := univ.filter fun k => color k = c
  have hQmass : (∑ k, a k) ≤ Fintype.card F * ∑ k ∈ Q, a k := by
    convert hmassc using 1
    congr 1
    apply Finset.sum_congr
    · ext k
      simp only [Q, mem_filter]
    · intro k hk
      rfl
  have hQ : Q.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, sum_empty, mul_zero] at hQmass
    exact (hmass.trans_le hQmass).false
  refine ⟨Q, c, hQ, hQmass, ?_⟩
  intro k hk p hp
  have hk' : color k = c := (mem_filter.mp hk).2
  have hkc := hcolor k
  rw [hk'] at hkc
  have hp' := tube_subset_midpoint_ball (hw k) hp
  change dist p (y k + (1 / 2 : ℝ) • w k) < ρ + 1 / 2 at hp'
  exact (dist_triangle p (y k + (1 / 2 : ℝ) • w k) c).trans_lt (by linarith)

namespace Interfaces

/-- Every coarse tube in a balanced retained cover meets the original unit ball. -/
theorem c_coarse_meets_unit_ball {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (k : Fin N) : (T ρ (y k) (w k) ∩ ball 0 1).Nonempty := by
  obtain ⟨i, hi, hfi⟩ := c_fibers_nonempty hδ hA hC k
  have hxi : x i ∈ T δ (x i) (v i) :=
    self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
  refine ⟨x i, ?_, (hA.2.1 i).2.1 hxi⟩
  have ht := hC.2.2.2.1 i hi hxi
  simpa only [hfi] using ht

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
