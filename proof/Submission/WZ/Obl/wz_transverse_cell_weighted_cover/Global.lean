-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.Global.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Local
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Net
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing

/-!
# Filling the output tube of a prism

`global_filling`: take a maximal `4 b`-separated set `X` of points of the shading `H k`
(`exists_finset_separated_cover`); since `H k ⊆ ⋃_{x ∈ X} B̄(x, 4 b)` and
`|P k ∩ B̄(x, 4b)| ≤ 128 a b²`, there are `≥ h / (16000 b)` of them. The balls `B(x, 2 b)` are
disjoint, lie in `cTube b (c k) (u k)`, and each is filled by `local_filling`.

`cell_density`: if `a / b ≥ h / 2` the shading `H k` alone suffices; otherwise the transversality
of the cell gives, at every point of `H k`, a prism at projective angle `≥ h / 4` from `P k`, and
`global_filling` applies with `θ = h / 4`.
-/

namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- A prism of small dimensions lies in the closed unit ball around its centre. -/
private theorem glob_prism_subset_closedBall {a b : ℝ} (ha1 : a ≤ 1 / 2) (hb1 : b ≤ 1 / 2)
    {c : Space} {u : Fin 3 → Space} (hu : Orthonormal ℝ u) :
    prism a b c u ⊆ closedBall c 1 := by
  intro q hq
  obtain ⟨h0, h1, h2⟩ := hq
  rw [mem_closedBall, dist_eq_norm]
  have hn := norm_sq_frame hu (q - c)
  have e0 := abs_le.mp h0
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  have hsq : ‖q - c‖ ^ 2 ≤ 1 := by
    rw [hn]
    nlinarith
  nlinarith [norm_nonneg (q - c)]

/-- The part of a prism in a closed ball of radius `4 b` around a point. -/
private theorem glob_volume_prism_inter_closedBall {a b : ℝ} {c : Space} {u : Fin 3 → Space}
    (hu : Orthonormal ℝ u) (x : Space) :
    volume (prism a b c u ∩ closedBall x (4 * b)) ≤
      ENNReal.ofReal (8 * (a * (4 * b) * (4 * b))) := by
  have hcoord : ∀ q ∈ prism a b c u ∩ closedBall x (4 * b), ∀ j : Fin 3,
      |inner ℝ (u j) (q - (![c, x, x] : Fin 3 → Space) j)| ≤
        (![a, 4 * b, 4 * b] : Fin 3 → ℝ) j := by
    intro q hq j
    have hball : ∀ j : Fin 3, |inner ℝ (u j) (q - x)| ≤ 4 * b := by
      intro j
      calc |inner ℝ (u j) (q - x)| ≤ ‖u j‖ * ‖q - x‖ := abs_real_inner_le_norm _ _
        _ = ‖q - x‖ := by rw [hu.1 j, one_mul]
        _ ≤ 4 * b := by rw [← dist_eq_norm]; exact hq.2
    fin_cases j
    · simpa using hq.1.1
    · simpa using hball 1
    · simpa using hball 2
  calc volume (prism a b c u ∩ closedBall x (4 * b))
      ≤ ENNReal.ofReal (8 * ((![a, 4 * b, 4 * b] : Fin 3 → ℝ) 0 *
          (![a, 4 * b, 4 * b] : Fin 3 → ℝ) 1 * (![a, 4 * b, 4 * b] : Fin 3 → ℝ) 2)) :=
        volume_le_of_coords hu _ _ _ hcoord
    _ = ENNReal.ofReal (8 * (a * (4 * b) * (4 * b))) := by simp

theorem global_filling : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (K : Finset (Fin n)) (a b h θ : ℝ)
    (c : Fin n → Space) (u : Fin n → Fin 3 → Space) (H : Fin n → Set Space) (k : Fin n),
    0 < a → a ≤ b → b ≤ 1 / 1000000 → 0 < h → h ≤ 1 → 0 < θ → θ ≤ 1 →
    (∀ i ∈ K, Orthonormal ℝ (u i)) → (∀ i ∈ K, MeasurableSet (H i)) →
    (∀ i ∈ K, H i ⊆ prism a b (c i) (u i)) →
    (∀ i ∈ K, ∀ p ∈ H i, ENNReal.ofReal h * volume (prism a b (c i) (u i) ∩ ball p b) ≤
      volume (H i ∩ ball p b)) →
    k ∈ K → ENNReal.ofReal h * volume (prism a b (c k) (u k)) ≤ volume (H k) →
    (∀ y ∈ H k, ∃ i ∈ K, y ∈ H i ∧ θ ≤ pd (u i 0) (u k 0)) →
    ENNReal.ofReal (C * h ^ 4 * θ ^ 4 * b ^ 2 / (1 + Real.log (b / a))) ≤
      volume (cTube b (c k) (u k) ∩ ⋃ i ∈ K, H i) := by
  obtain ⟨C₀, hC₀, hloc⟩ := local_filling
  refine ⟨C₀ / 16000, by positivity, ?_⟩
  intro n K a b h θ c u H k ha hab hb1 hh hh1 hθ hθ1 hu hmeas hsub hreg hk hdens htrans
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have huk : Orthonormal ℝ (u k) := hu k hk
  set E : Set Space := ⋃ i ∈ K, H i with hE_def
  have hE : MeasurableSet E := Finset.measurableSet_biUnion K hmeas
  set L : ℝ := 1 + Real.log (b / a) with hL_def
  have hL0 : 0 < L := by
    have : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).mpr hab)
    rw [hL_def]
    linarith
  -- Step 1: a maximal `4 b`-separated subset of `H k`.
  have hTB : TotallyBounded (H k) :=
    (isCompact_closedBall (c k) 1).totallyBounded.subset
      ((hsub k hk).trans (glob_prism_subset_closedBall (by linarith) (by linarith) huk))
  obtain ⟨X, hXH, hXsep, hXcov⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover hTB
      (show (0 : ℝ) < 4 * b by positivity)
  -- Step 2: there are many points in `X`.
  have hvol : ENNReal.ofReal (h * (8 * (a * b * (1 / 1000)))) ≤
      ENNReal.ofReal ((X.card : ℝ) * (8 * (a * (4 * b) * (4 * b)))) := by
    calc ENNReal.ofReal (h * (8 * (a * b * (1 / 1000))))
        = ENNReal.ofReal h * volume (prism a b (c k) (u k)) := by
          rw [volume_prism ha.le hb0.le (c k) huk, ENNReal.ofReal_mul hh.le]
      _ ≤ volume (H k) := hdens
      _ ≤ volume (⋃ x ∈ X, prism a b (c k) (u k) ∩ closedBall x (4 * b)) := by
          apply measure_mono
          intro q hq
          have hq' := hXcov hq
          rw [mem_iUnion₂] at hq' ⊢
          obtain ⟨x, hx, hqx⟩ := hq'
          exact ⟨x, hx, hsub k hk hq, hqx⟩
      _ ≤ ∑ x ∈ X, volume (prism a b (c k) (u k) ∩ closedBall x (4 * b)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ X, ENNReal.ofReal (8 * (a * (4 * b) * (4 * b))) :=
          Finset.sum_le_sum fun x _ => glob_volume_prism_inter_closedBall huk x
      _ = ENNReal.ofReal ((X.card : ℝ) * (8 * (a * (4 * b) * (4 * b)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have hvol' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol
  have hN : h ≤ 16000 * b * (X.card : ℝ) := by
    have hab0 : 0 < a * b := mul_pos ha hb0
    have h2 : h * (a * b) ≤ (16000 * b * (X.card : ℝ)) * (a * b) := by linarith
    exact le_of_mul_le_mul_right h2 hab0
  -- Step 3: each ball `B(x, 2 b)` is filled.
  have hfill : ∀ x ∈ X, ENNReal.ofReal (C₀ * h ^ 3 * θ ^ 4 * b ^ 3 / L) ≤
      volume (ball x (2 * b) ∩ E) := by
    intro x hx
    have hxH : x ∈ H k := hXH hx
    exact hloc n K a b h θ c u H (c k) (u k) (H k) x ha hab hb1 hh hh1 hθ hθ1 hu hmeas hsub
      hreg huk (hsub k hk) hxH (hreg k hk x hxH) htrans
  -- Step 4: the balls are disjoint and lie in the tube.
  have hdisj : (↑X : Set Space).PairwiseDisjoint (fun x => ball x (2 * b) ∩ E) := by
    intro x hx y hy hxy
    have hsep := hXsep x hx y hy hxy
    have hd : Disjoint (ball x (2 * b)) (ball y (2 * b)) := ball_disjoint_ball (by linarith)
    exact hd.mono inter_subset_left inter_subset_left
  have hunion : ∑ x ∈ X, volume (ball x (2 * b) ∩ E) =
      volume (⋃ x ∈ X, ball x (2 * b) ∩ E) :=
    (measure_biUnion_finset hdisj (fun x _ => measurableSet_ball.inter hE)).symm
  have hsubT : (⋃ x ∈ X, ball x (2 * b) ∩ E) ⊆ cTube b (c k) (u k) ∩ E := by
    intro q hq
    rw [mem_iUnion₂] at hq
    obtain ⟨x, hx, hq1, hq2⟩ := hq
    exact ⟨ball_subset_cTube ha.le hab huk (hsub k hk (hXH hx)) hq1, hq2⟩
  -- Step 5: summing up.
  have key : C₀ / 16000 * h ^ 4 * θ ^ 4 * b ^ 2 ≤
      (X.card : ℝ) * (C₀ * h ^ 3 * θ ^ 4 * b ^ 3) := by
    have hpos : 0 ≤ C₀ * h ^ 3 * θ ^ 4 * b ^ 2 / 16000 := by positivity
    calc C₀ / 16000 * h ^ 4 * θ ^ 4 * b ^ 2 = C₀ * h ^ 3 * θ ^ 4 * b ^ 2 / 16000 * h := by ring
      _ ≤ C₀ * h ^ 3 * θ ^ 4 * b ^ 2 / 16000 * (16000 * b * (X.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hN hpos
      _ = (X.card : ℝ) * (C₀ * h ^ 3 * θ ^ 4 * b ^ 3) := by ring
  calc ENNReal.ofReal (C₀ / 16000 * h ^ 4 * θ ^ 4 * b ^ 2 / L)
      ≤ ENNReal.ofReal ((X.card : ℝ) * (C₀ * h ^ 3 * θ ^ 4 * b ^ 3 / L)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right key hL0.le
    _ = ∑ x ∈ X, ENNReal.ofReal (C₀ * h ^ 3 * θ ^ 4 * b ^ 3 / L) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ x ∈ X, volume (ball x (2 * b) ∩ E) := Finset.sum_le_sum hfill
    _ = volume (⋃ x ∈ X, ball x (2 * b) ∩ E) := hunion
    _ ≤ volume (cTube b (c k) (u k) ∩ E) := measure_mono hsubT

theorem cell_density : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (K : Finset (Fin n)) (a b h : ℝ)
    (c : Fin n → Space) (u : Fin n → Fin 3 → Space) (H : Fin n → Set Space) (k : Fin n),
    0 < a → a ≤ b → b ≤ 1 / 1000000 → 0 < h → h ≤ 1 →
    (∀ i ∈ K, Orthonormal ℝ (u i)) → (∀ i ∈ K, MeasurableSet (H i)) →
    (∀ i ∈ K, H i ⊆ prism a b (c i) (u i)) →
    (∀ i ∈ K, ∀ p ∈ H i, ENNReal.ofReal h * volume (prism a b (c i) (u i) ∩ ball p b) ≤
      volume (H i ∩ ball p b)) →
    k ∈ K → ENNReal.ofReal h * volume (prism a b (c k) (u k)) ≤ volume (H k) →
    (∀ p : Space, (∃ i : Fin n, i ∈ K ∧ p ∈ H i) → ∃ i i' : Fin n, i ∈ K ∧ i' ∈ K ∧
      p ∈ H i ∧ p ∈ H i' ∧ h ≤ a / b + pd (u i 0) (u i' 0)) →
    ENNReal.ofReal (C * h ^ 8 * b ^ 2 / (1 + Real.log (b / a))) ≤
      volume (cTube b (c k) (u k) ∩ ⋃ i ∈ K, H i) := by
  obtain ⟨Cg, hCg, hglob⟩ := global_filling
  refine ⟨min (4 / 1000) (Cg / 256), lt_min (by norm_num) (by positivity), ?_⟩
  intro n K a b h c u H k ha hab hb1 hh hh1 hu hmeas hsub hreg hk hdens htrans
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hL1 : 1 ≤ 1 + Real.log (b / a) := by
    have : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).mpr hab)
    linarith
  have hL0 : 0 < 1 + Real.log (b / a) := by linarith
  by_cases hcase : h * b ≤ 2 * a
  · -- the shading `H k` alone suffices
    have hHk : H k ⊆ cTube b (c k) (u k) ∩ ⋃ i ∈ K, H i := by
      intro q hq
      refine ⟨prism_subset_cTube ha.le hab hb0 (hu k hk) (hsub k hk hq), ?_⟩
      rw [mem_iUnion₂]
      exact ⟨k, hk, hq⟩
    have hmin : min (4 / 1000) (Cg / 256) ≤ 4 / 1000 := min_le_left _ _
    have hmin0 : 0 ≤ min (4 / 1000) (Cg / 256) := le_min (by norm_num) (by positivity)
    have hh8 : h ^ 8 ≤ h ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
    have hreal : min (4 / 1000) (Cg / 256) * h ^ 8 * b ^ 2 / (1 + Real.log (b / a)) ≤
        h * (8 * (a * b * (1 / 1000))) := by
      calc min (4 / 1000) (Cg / 256) * h ^ 8 * b ^ 2 / (1 + Real.log (b / a))
          ≤ min (4 / 1000) (Cg / 256) * h ^ 8 * b ^ 2 := div_le_self (by positivity) hL1
        _ ≤ 4 / 1000 * h ^ 2 * b ^ 2 := by gcongr
        _ ≤ h * (8 * (a * b * (1 / 1000))) := by
            have := mul_le_mul_of_nonneg_left hcase (mul_pos hh hb0).le
            nlinarith
    calc ENNReal.ofReal (min (4 / 1000) (Cg / 256) * h ^ 8 * b ^ 2 / (1 + Real.log (b / a)))
        ≤ ENNReal.ofReal (h * (8 * (a * b * (1 / 1000)))) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal h * volume (prism a b (c k) (u k)) := by
          rw [volume_prism ha.le hb0.le (c k) (hu k hk), ENNReal.ofReal_mul hh.le]
      _ ≤ volume (H k) := hdens
      _ ≤ _ := measure_mono hHk
  · -- transversality at angle `h / 4`
    have hcase' : 2 * a < h * b := not_le.mp hcase
    have htrans' : ∀ y ∈ H k, ∃ i ∈ K, y ∈ H i ∧ h / 4 ≤ pd (u i 0) (u k 0) := by
      intro y hy
      obtain ⟨i, i', hi, hi', hyi, hyi', hpd⟩ := htrans y ⟨k, hk, hy⟩
      have hab' : a / b < h / 2 := by
        rw [div_lt_iff₀ hb0]
        linarith
      have htri : pd (u i 0) (u i' 0) ≤ pd (u i 0) (u k 0) + pd (u i' 0) (u k 0) := by
        have := pd_triangle (u i 0) (u k 0) (u i' 0)
        rw [pd_symm (u k 0) (u i' 0)] at this
        exact this
      by_cases h1 : h / 4 ≤ pd (u i 0) (u k 0)
      · exact ⟨i, hi, hyi, h1⟩
      · refine ⟨i', hi', hyi', ?_⟩
        have h1' : pd (u i 0) (u k 0) < h / 4 := not_le.mp h1
        linarith
    have hg := hglob n K a b h (h / 4) c u H k ha hab hb1 hh hh1 (by positivity) (by linarith)
      hu hmeas hsub hreg hk hdens htrans'
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hg
    apply div_le_div_of_nonneg_right _ hL0.le
    have hmin : min (4 / 1000) (Cg / 256) ≤ Cg / 256 := min_le_right _ _
    calc min (4 / 1000) (Cg / 256) * h ^ 8 * b ^ 2 ≤ Cg / 256 * h ^ 8 * b ^ 2 := by gcongr
      _ = Cg * h ^ 4 * (h / 4) ^ 4 * b ^ 2 := by ring

end

end WangZahlLot.Obl.wz_transverse_cell_weighted_cover
