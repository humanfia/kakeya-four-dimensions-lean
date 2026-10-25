-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.LocalToGlobal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Basic

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

/-- A separated net converts a lower bound in every small ball into a global
bound, using an upper bound for the anchor mass in the covering balls. -/
theorem local_mass_to_global {A E : Set Space} {r : ℝ} {m q : ℝ≥0∞}
    (hr : 0 < r) (hA : TotallyBounded A) (hE : MeasurableSet E)
    (hupper : ∀ x ∈ A, volume (A ∩ closedBall x (4 * r)) ≤ m)
    (hlower : ∀ x ∈ A, q ≤ volume (E ∩ ball x (2 * r))) :
    q * volume A ≤ m * volume E := by
  classical
  obtain ⟨F, hFA, hsep, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover
      hA (by positivity : 0 < 4 * r)
  have hmass : volume A ≤ (F.card : ℝ≥0∞) * m := by
    calc
      volume A ≤ volume (⋃ x ∈ F, A ∩ closedBall x (4 * r)) := by
        apply measure_mono
        intro p hp
        obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp (hcover hp)
        exact mem_iUnion₂.mpr ⟨x, hx, hp, hpx⟩
      _ ≤ ∑ x ∈ F, volume (A ∩ closedBall x (4 * r)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _x ∈ F, m := Finset.sum_le_sum fun x hx => hupper x (hFA hx)
      _ = _ := by simp [nsmul_eq_mul]
  have hdisj : (↑F : Set Space).PairwiseDisjoint (fun x => E ∩ ball x (2 * r)) := by
    intro x hx y hy hxy
    have hh := hsep x hx y hy hxy
    exact (ball_disjoint_ball (by linarith : 2 * r + 2 * r ≤ dist x y)).mono
      inter_subset_right inter_subset_right
  have hfill : (F.card : ℝ≥0∞) * q ≤ volume E := by
    calc
      _ = ∑ _x ∈ F, q := by simp [nsmul_eq_mul]
      _ ≤ ∑ x ∈ F, volume (E ∩ ball x (2 * r)) :=
        Finset.sum_le_sum fun x hx => hlower x (hFA hx)
      _ = volume (⋃ x ∈ F, E ∩ ball x (2 * r)) :=
        (measure_biUnion_finset hdisj (fun _ _ => hE.inter measurableSet_ball)).symm
      _ ≤ volume E := measure_mono (iUnion₂_subset fun _ _ => inter_subset_left)
  calc
    q * volume A ≤ q * ((F.card : ℝ≥0∞) * m) := mul_le_mul' (le_refl q) hmass
    _ = m * ((F.card : ℝ≥0∞) * q) := by ac_rfl
    _ ≤ m * volume E := mul_le_mul' (le_refl m) hfill

theorem prism_totallyBounded (a b : ℝ) (c : Space) {u : Fin 3 → Space}
    (hu : Orthonormal ℝ u) : TotallyBounded (prism a b c u) := by
  apply (isCompact_closedBall c (a + b + 1 / 1000)).totallyBounded.subset
  intro p hp
  rw [mem_closedBall, dist_eq_norm, eq_sum_frame hu (p - c)]
  calc
    _ ≤ ‖inner ℝ (u 0) (p - c) • u 0‖ + ‖inner ℝ (u 1) (p - c) • u 1‖ +
        ‖inner ℝ (u 2) (p - c) • u 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = |inner ℝ (u 0) (p - c)| + |inner ℝ (u 1) (p - c)| +
        |inner ℝ (u 2) (p - c)| := by
      simp [norm_smul, Real.norm_eq_abs, hu.1]
    _ ≤ _ := by linarith [hp.1, hp.2.1, hp.2.2]

/-- Only the anchor's short coordinate is used in this local volume bound. -/
theorem prism_ball_volume_upper (a b s : ℝ) (c x : Space) {u : Fin 3 → Space}
    (hu : Orthonormal ℝ u) :
    volume (prism a b c u ∩ closedBall x s) ≤ ENNReal.ofReal (8 * a * s ^ 2) := by
  have hh := volume_le_of_coords hu ![c, x, x] ![a, s, s]
    (prism a b c u ∩ closedBall x s) (by
      intro p hp i
      have hb (j : Fin 3) : |inner ℝ (u j) (p - x)| ≤ s := by
        calc
          _ ≤ ‖u j‖ * ‖p - x‖ := abs_real_inner_le_norm _ _
          _ = ‖p - x‖ := by rw [hu.1 j, one_mul]
          _ ≤ s := by simpa only [mem_closedBall, dist_eq_norm] using hp.2
      fin_cases i
      · exact hp.1.1
      · exact hb 1
      · exact hb 2)
  change volume (prism a b c u ∩ closedBall x s) ≤ ENNReal.ofReal (8 * (a * s * s)) at hh
  convert hh using 1
  congr 1
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
