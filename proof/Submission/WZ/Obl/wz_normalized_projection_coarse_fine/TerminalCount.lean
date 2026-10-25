-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.TerminalCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.ParameterCount
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.DyadicHierarchy

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya

noncomputable section

attribute [local instance] Classical.propDecidable

lemma tube_volume_upper {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) : volume (Tube δ x v) ≤ ENNReal.ofReal (56 * δ ^ 2) := by
  have hseg : segment ℝ x (x + v) ⊆ segment ℝ x (x + (6 : ℝ) • v) := by
    apply (convex_segment x (x + (6 : ℝ) • v)).segment_subset
      (left_mem_segment ℝ _ _)
    rw [segment_eq_image']
    refine ⟨1 / 6, by norm_num, ?_⟩
    simp only [add_sub_cancel_left, smul_smul]
    norm_num
  have hh := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.cylinder_scaled_volume_le
    hv x (C := 1) (θ := δ) (by norm_num) hδ hδ1
  norm_num at hh
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 56), ENNReal.ofReal_ofNat] using
    (measure_mono (thickening_subset_of_subset δ hseg)).trans hh

/-- Convex Frostman counts bound the occupancy of a finest dyadic parameter cell
inside any thin slice of the omitted slope coordinate. -/
theorem thin_slice_dyadic_count {η δ c : ℝ} (hδ : 0 < δ)
    {n J : ℕ} (x v : Fin n → Space) (U : Finset (Fin n))
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (hthin : ∀ i ∈ U, |slope (v i) 0 - c| ≤ δ)
    (hδσ : δ ≤ ((2 : ℝ) ^ J)⁻¹) (hσ : 5 * ((2 : ℝ) ^ J)⁻¹ ≤ 1)
    (l : Fin 3 → ℤ) :
    ((U.filter (fun i => dyadicLabel J (parameters (x i) (v i)) = l)).card : ℝ) ≤
      2080000 * δ ^ (-η) * (n : ℝ) * (((2 : ℝ) ^ J)⁻¹) ^ 2 := by
  classical
  let σ := ((2 : ℝ) ^ J)⁻¹
  have hσpos : 0 < σ := by dsimp [σ]; positivity
  let S := U.filter (fun i => dyadicLabel J (parameters (x i) (v i)) = l)
  rcases S.eq_empty_or_nonempty with he | hS
  · change (S.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨i₀, hi₀⟩ := hS
  have hi₀U := (Finset.mem_filter.mp hi₀).1
  have hsub : (↑S : Set (Fin n)) ⊆
      {i | lineParameters (x i) (v i) ∈ ball (lineParameters (x i₀) (v i₀)) (5 * σ)} := by
    intro i hi
    obtain ⟨hiU, hil⟩ := Finset.mem_filter.mp hi
    have he := hil.trans (Finset.mem_filter.mp hi₀).2.symm
    have hp (j : Fin 3) := (abs_coordinate_sub_lt_of_dyadicLabel_eq he j).le
    have hcs : |slope (v i) 0 - slope (v i₀) 0| ≤ 2 * σ := by
      have ht := abs_sub_le (slope (v i) 0) c (slope (v i₀) 0)
      rw [abs_sub_comm c (slope (v i₀) 0)] at ht
      linarith [hthin i hiU, hthin i₀ hi₀U]
    have hcoord (j : Fin 4) :
        |lineParameters (x i) (v i) j - lineParameters (x i₀) (v i₀) j| ≤ 2 * σ := by
      fin_cases j
      · change |intercept (x i) (v i) 0 - intercept (x i₀) (v i₀) 0| ≤ _
        exact (hp 0).trans (by linarith)
      · change |intercept (x i) (v i) 1 - intercept (x i₀) (v i₀) 1| ≤ _
        exact (hp 1).trans (by linarith)
      · exact hcs
      · change |slope (v i) 1 - slope (v i₀) 1| ≤ _
        exact (hp 2).trans (by linarith)
    have hn : ‖lineParameters (x i) (v i) - lineParameters (x i₀) (v i₀)‖ ^ 2 ≤
        16 * σ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        _ ≤ ∑ _j : Fin 4, (2 * σ) ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hh := mul_self_le_mul_self (abs_nonneg _) (hcoord j)
          simpa only [PiLp.sub_apply, ← sq, sq_abs] using hh
        _ = _ := by simp; ring
    rw [mem_ofPred_eq, mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg (lineParameters (x i) (v i) - lineParameters (x i₀) (v i₀)),
      sq_pos_of_pos hσpos]
  have hcard : S.card ≤ Set.ncard {i | lineParameters (x i) (v i) ∈
      ball (lineParameters (x i₀) (v i₀)) (5 * σ)} := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_mono hsub
  have hh := lineParameters_frostman_count hδ x v hv htrans hball hF
    (lineParameters (x i₀) (v i₀)) (r := 5 * σ) (by linarith) hσ
  calc
    _ ≤ (Set.ncard {i | lineParameters (x i) (v i) ∈
        ball (lineParameters (x i₀) (v i₀)) (5 * σ)} : ℝ) := by exact_mod_cast hcard
    _ ≤ 83200 * δ ^ (-η) * (n : ℝ) * (5 * σ) ^ 2 := hh
    _ = _ := by dsimp [σ]; ring

/-- The mass of a thin-slice family controls how many finest parameter cells it occupies.
This form permits weighted regularization before scale selection. -/
theorem thin_slice_terminal_mass_bound {η δ c : ℝ} (hδ : 0 < δ)
    {n J : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space) (U : Finset (Fin n))
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hY : ∀ i ∈ U, Y i ⊆ Tube δ (x i) (v i))
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (hthin : ∀ i ∈ U, |slope (v i) 0 - c| ≤ δ)
    (hδσ : δ ≤ ((2 : ℝ) ^ J)⁻¹) (hσ : 5 * ((2 : ℝ) ^ J)⁻¹ ≤ 1) :
    (∑ i ∈ U, volume (Y i)) ≤ ENNReal.ofReal
      (116480000 * δ ^ (-η) * (n : ℝ) * δ ^ 2 * (((2 : ℝ) ^ J)⁻¹) ^ 2 *
        (U.image (fun i => dyadicLabel J (parameters (x i) (v i)))).card) := by
  classical
  let p := fun i => dyadicLabel J (parameters (x i) (v i))
  have hδ1 : δ ≤ 1 := by
    have hpos : 0 < ((2 : ℝ) ^ J)⁻¹ := by positivity
    linarith
  have hc : (U.card : ℝ) ≤ (2080000 * δ ^ (-η) * (n : ℝ) * (((2 : ℝ) ^ J)⁻¹) ^ 2) *
      (U.image p).card := by
    have he := Finset.card_eq_sum_card_image p U
    calc
      _ = ∑ l ∈ U.image p, ((U.filter (fun i => p i = l)).card : ℝ) := by exact_mod_cast he
      _ ≤ ∑ _l ∈ U.image p, 2080000 * δ ^ (-η) * (n : ℝ) * (((2 : ℝ) ^ J)⁻¹) ^ 2 :=
        Finset.sum_le_sum fun l _ => thin_slice_dyadic_count hδ x v U hv htrans hball hF
          hthin hδσ hσ l
      _ = _ := by simp; ring
  calc
    _ ≤ ∑ _i ∈ U, ENNReal.ofReal (56 * δ ^ 2) := Finset.sum_le_sum fun i hi =>
      (measure_mono (hY i hi)).trans (tube_volume_upper hδ.le hδ1 (x i) (v i) (hv i))
    _ = ENNReal.ofReal (56 * δ ^ 2 * U.card) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp [mul_comm]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ 56 * δ ^ 2 * ((2080000 * δ ^ (-η) * (n : ℝ) * (((2 : ℝ) ^ J)⁻¹) ^ 2) *
            (U.image p).card) := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by ring

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
