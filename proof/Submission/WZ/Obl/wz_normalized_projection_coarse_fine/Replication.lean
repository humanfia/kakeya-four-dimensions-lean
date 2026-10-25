-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.Replication.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.TranslationAverage
import Submission.WZ.Obl.wz_nsp_translation_model.Counting

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nsp_translation_model

noncomputable section

lemma dist_translate_center (q t a : Space) : dist (q + t) a = dist q (a - t) := by
  rw [dist_eq_norm, dist_eq_norm]
  congr 1
  module

lemma translated_parameters_dist (q q' t t' : Space) :
    dist t t' ≤ dist (q + t) (q' + t') + dist q q' := by
  have hh := norm_add_le ((q + t) - (q' + t')) (q' - q)
  have he : (q + t) - (q' + t') + (q' - q) = t - t' := by module
  rw [he] at hh
  simpa only [← dist_eq_norm, dist_comm q' q] using hh

/-- Separated translations of a small parameter class preserve its linear count at all radii. -/
theorem replicated_parameter_count {δ ρ L A : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρL : ρ ≤ L) (hLcube : L ^ 3 = ρ) (hA : 0 ≤ A)
    {m n : ℕ} (t : Fin m → Space) (q : Fin n → Space) (a : Space)
    (hsep : ∀ s s', s ≠ s' → 10 * L < dist (t s) (t s'))
    (hdiam : ∀ i, dist (q i) a ≤ ρ) (hn : (n : ℝ) ≤ A * (ρ / δ))
    (hc : ∀ (b : Space) (r : ℝ), δ ≤ r → r ≤ 1 →
      (ncard {i | q i ∈ ball b r} : ℝ) ≤ A * (r / δ))
    (b : Space) {r : ℝ} (hδr : δ ≤ r) (hr1 : r ≤ 1) :
    (ncard {p : Fin m × Fin n | q p.2 + t p.1 ∈ ball b r} : ℝ) ≤
      3456 * A * (r / δ) := by
  classical
  have hL : 0 < L := hρ.trans_le hρL
  have hr : 0 < r := hδ.trans_le hδr
  have hqq (i j : Fin n) : dist (q i) (q j) ≤ 2 * ρ := by
    have hh := dist_triangle (q i) a (q j)
    rw [dist_comm a (q j)] at hh
    linarith [hdiam i, hdiam j]
  have hcopy (s : Fin m) :
      (ncard {i | q i + t s ∈ ball b r} : ℝ) ≤ A * (r / δ) := by
    simpa only [mem_ball, dist_translate_center] using hc (b - t s) r hδr hr1
  rw [ncard_prod_sum (fun s i => q i + t s ∈ ball b r)]
  by_cases hrL : r < L
  · by_cases hex : ∃ s i, q i + t s ∈ ball b r
    · obtain ⟨s₀, i₀, hi₀⟩ := hex
      have hzero (s : Fin m) (hs : s ≠ s₀) : {i | q i + t s ∈ ball b r} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hdist : dist (q i + t s) (q i₀ + t s₀) < 2 * r := by
          have hh := dist_triangle (q i + t s) b (q i₀ + t s₀)
          rw [dist_comm b (q i₀ + t s₀)] at hh
          have h1 : dist (q i + t s) b < r := hi
          have h2 : dist (q i₀ + t s₀) b < r := hi₀
          linarith
        have hh := translated_parameters_dist (q i) (q i₀) (t s) (t s₀)
        linarith [hsep s s₀ hs, hqq i i₀]
      have hsum : (∑ s, (ncard {i | q i + t s ∈ ball b r} : ℝ)) =
          (ncard {i | q i + t s₀ ∈ ball b r} : ℝ) := by
        apply Finset.sum_eq_single s₀
        · intro s _ hs
          rw [hzero s hs, ncard_empty, Nat.cast_zero]
        · simp
      rw [hsum]
      exact (hcopy s₀).trans (by nlinarith [mul_nonneg hA (div_nonneg hr.le hδ.le)])
    · have hzero (s : Fin m) : {i | q i + t s ∈ ball b r} = ∅ := by
        exact Set.eq_empty_iff_forall_notMem.mpr (fun i hi => hex ⟨s, i, hi⟩)
      simp only [hzero, ncard_empty, Nat.cast_zero, Finset.sum_const_zero]
      positivity
  · have hLr : L ≤ r := le_of_not_gt hrL
    have hcent (s : Fin m) (i : Fin n) (hi : q i + t s ∈ ball b r) :
        t s ∈ ball (b - a) (2 * r) := by
      have hh := dist_triangle (a + t s) (q i + t s) b
      rw [dist_add_right, dist_comm a (q i)] at hh
      have hi' : dist (q i + t s) b < r := hi
      have he : dist (a + t s) b = dist (t s) (b - a) := by
        rw [add_comm a, dist_translate_center]
      change dist (t s) (b - a) < 2 * r
      rw [← he]
      linarith [hdiam i]
    have hbound : (∑ s, (ncard {i | q i + t s ∈ ball b r} : ℝ)) ≤
        (ncard {s | t s ∈ ball (b - a) (2 * r)} : ℝ) * n := by
      rw [ncard_eq_sum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : t s ∈ ball (b - a) (2 * r)
      · simp only [hs, ite_true, one_mul]
        have hh : ncard {i | q i + t s ∈ ball b r} ≤ n := by
          simpa using Set.ncard_le_card {i | q i + t s ∈ ball b r}
        exact_mod_cast hh
      · have hz : {i | q i + t s ∈ ball b r} = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr (fun i hi => hs (hcent s i hi))
        rw [hz, ncard_empty, Nat.cast_zero, ite_eq_right hs, zero_mul]
    have hpack := separated_point_ball_count hL (by linarith : L ≤ 2 * r) t
      (fun s s' hs => by linarith [hsep s s' hs]) (b - a)
    rw [hLcube] at hpack
    have hr3 : r ^ 3 ≤ r := by nlinarith [sq_nonneg (1 - r), sq_nonneg r]
    calc
      _ ≤ (ncard {s | t s ∈ ball (b - a) (2 * r)} : ℝ) * n := hbound
      _ ≤ (ncard {s | t s ∈ ball (b - a) (2 * r)} : ℝ) * (A * (ρ / δ)) := by
        gcongr
      _ = (A / δ) * ((ncard {s | t s ∈ ball (b - a) (2 * r)} : ℝ) * ρ) := by ring
      _ ≤ (A / δ) * (432 * (2 * r) ^ 3) :=
        mul_le_mul_of_nonneg_left hpack (div_nonneg hA hδ.le)
      _ = 3456 * A * (r ^ 3 / δ) := by ring
      _ ≤ 3456 * A * (r / δ) := by gcongr

/-- A small parameter class admits at least a constant times `rho^-1` disjoint translates.
Their norms stay bounded and their union satisfies a one-dimensional Katz--Tao count. -/
theorem exists_parameter_replication {δ ρ A : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρ1 : ρ ≤ 1) (hA : 0 ≤ A) {n : ℕ} (q : Fin n → Space) (a : Space)
    (hdiam : ∀ i, dist (q i) a ≤ ρ) (hnorm : ∀ i, ‖q i‖ ≤ 5)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j))
    (hn : (n : ℝ) ≤ A * (ρ / δ))
    (hc : ∀ (b : Space) (r : ℝ), δ ≤ r → r ≤ 1 →
      (ncard {i | q i ∈ ball b r} : ℝ) ≤ A * (r / δ)) :
    ∃ (m : ℕ) (t : Fin m → Space), 0 < m ∧
      1 ≤ 128000 * (m : ℝ) * ρ ∧ (∀ s, ‖t s‖ ≤ 1) ∧
      (∀ p : Fin m × Fin n, ‖q p.2 + t p.1‖ ≤ 10) ∧
      (∀ p p' : Fin m × Fin n, p ≠ p' →
        δ ≤ dist (q p.2 + t p.1) (q p'.2 + t p'.1)) ∧
      (∀ (b : Space) (r : ℝ), δ ≤ r → r ≤ 1 →
        (ncard {p : Fin m × Fin n | q p.2 + t p.1 ∈ ball b r} : ℝ) ≤
          3456 * A * (r / δ)) := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  let L := ρ ^ (1 / 3 : ℝ)
  have hL : 0 < L := Real.rpow_pos_of_pos hρ _
  have hρL : ρ ≤ L := by
    simpa [L] using Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hLcube : L ^ 3 = ρ := by
    dsimp [L]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  obtain ⟨m, t, hm, ht, hts, hcover⟩ := finite_net (by positivity : 0 < 10 * L)
    (by norm_num : (0 : ℝ) ≤ 1)
  have hnet := net_card_lower (by positivity : 0 < 10 * L) (by norm_num : (0 : ℝ) ≤ 1) t hcover
  have hcard : 1 ≤ 128000 * (m : ℝ) * ρ := by
    simp only [one_pow, mul_pow, hLcube] at hnet
    nlinarith
  refine ⟨m, t, hm, hcard, ht, ?_, ?_, fun b r hδr hr1 =>
    replicated_parameter_count hδ hρ hρL hLcube hA t q a hts hdiam hn hc b hδr hr1⟩
  · intro p
    exact (norm_add_le _ _).trans (by linarith [hnorm p.2, ht p.1])
  · intro p p' hpp
    by_cases hs : p.1 = p'.1
    · have hi : p.2 ≠ p'.2 := fun hi => hpp (Prod.ext hs hi)
      simpa only [hs, dist_add_right] using hsep p.2 p'.2 hi
    · have hh := translated_parameters_dist (q p.2) (q p'.2) (t p.1) (t p'.1)
      have hqq := dist_triangle (q p.2) a (q p'.2)
      rw [dist_comm a (q p'.2)] at hqq
      linarith [hts p.1 p'.1 hs, hdiam p.2, hdiam p'.2]

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
