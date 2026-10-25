-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.TranslationAverage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_translation_model.Geometry

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nsp_translation_model

noncomputable section

/-- A separated finite list has the expected three-dimensional local packing bound. -/
lemma separated_point_ball_count {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    {m : ℕ} (t : Fin m → Space)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (t i) (t j)) (q₀ : Space) :
    (Set.ncard {i | t i ∈ ball q₀ r} : ℝ) * δ ^ 3 ≤ 432 * r ^ 3 := by
  classical
  let I := Finset.univ.filter fun i => t i ∈ ball q₀ r
  have hdisj : Pairwise (fun i j : I =>
      Disjoint (ball (t i) (δ / 2)) (ball (t j) (δ / 2))) := by
    intro i j hij
    apply ball_disjoint_ball
    have hh := hsep i j (fun h => hij (Subtype.ext h))
    linarith
  have hsub : (⋃ i : I, ball (t i) (δ / 2)) ⊆ ball q₀ (3 * r / 2) := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    have hit : dist (t i) q₀ < r := (Finset.mem_filter.mp i.property).2
    have hpt : dist p (t i) < δ / 2 := hi
    exact (dist_triangle p (t i) q₀).trans_lt (by linarith)
  have hsum : (I.card : ℝ) * (δ / 2) ^ 3 ≤ 54 * r ^ 3 := by
    calc
      _ = ∑ _i : I, (δ / 2) ^ 3 := by simp
      _ ≤ ∑ i : I, volume.real (ball (t i) (δ / 2)) :=
        Finset.sum_le_sum fun _ _ => ball_volume_lower (by positivity) _
      _ = volume.real (⋃ i : I, ball (t i) (δ / 2)) :=
        (measureReal_iUnion_fintype hdisj (fun _ => measurableSet_ball)
          (fun _ => measure_ball_lt_top.ne)).symm
      _ ≤ volume.real (ball q₀ (3 * r / 2)) := measureReal_mono hsub measure_ball_lt_top.ne
      _ ≤ 16 * (3 * r / 2) ^ 3 := ball_volume_upper (by linarith) _
      _ = 54 * r ^ 3 := by ring
  have hcard : I.card = Set.ncard {i | t i ∈ ball q₀ r} := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext i
    simp [I]
  rw [hcard] at hsum
  nlinarith

/-- A finite list of bounded translations has a uniform cubic average for every point and ball. -/
theorem point_translation_average {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (t : Fin m → Space), 0 < m ∧ (∀ s, ‖t s‖ ≤ 1) ∧
      ∀ (q q₀ : Space) (r : ℝ), δ ≤ r →
        (Set.ncard {s | q + t s ∈ ball q₀ r} : ℝ) ≤ 65536 * (m : ℝ) * r ^ 3 := by
  obtain ⟨m, t, hm, ht, hsep, hcover⟩ := finite_net hδ (by norm_num : (0 : ℝ) ≤ 1)
  have hnet : 1 ≤ 128 * (m : ℝ) * δ ^ 3 := by
    simpa using net_card_lower hδ (by norm_num : (0 : ℝ) ≤ 1) t hcover
  refine ⟨m, t, hm, ht, ?_⟩
  intro q q₀ r hδr
  have hpack := separated_point_ball_count hδ hδr (fun s => q + t s)
    (fun i j hij => by simpa using (hsep i j hij).le) q₀
  have hr : 0 ≤ r := hδ.le.trans hδr
  have hcn : 0 ≤ (Set.ncard {s | q + t s ∈ ball q₀ r} : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (Set.ncard {s | q + t s ∈ ball q₀ r} : ℝ) * (128 * (m : ℝ) * δ ^ 3) := by
      simpa using mul_le_mul_of_nonneg_left hnet hcn
    _ = (128 * (m : ℝ)) * ((Set.ncard {s | q + t s ∈ ball q₀ r} : ℝ) * δ ^ 3) := by ring
    _ ≤ (128 * (m : ℝ)) * (432 * r ^ 3) :=
      mul_le_mul_of_nonneg_left hpack (by positivity)
    _ ≤ 65536 * (m : ℝ) * r ^ 3 := by
      nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (pow_nonneg hr 3)]

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
