/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file CurveCells.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.NormalStrips
import Submission.Obl.k4_scalar_graph_residual_discovery.SpatialCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_initial_true_horizon

/-- A bounded-speed trajectory visits only a linear number of coarse
physical cells. The same bound permits assignment by the original fine-state
centers instead of by the actual trajectory points. -/
theorem curve_assigned_cell_list {n : ℕ} (γ : ℝ → Fin n → ℝ)
    {K ρ b : ℝ} (hK : 0 < K) (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hlip : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      ‖γ t - γ u‖ ≤ K * |t - u|) :
    ∃ L : Finset (Fin n → ℤ), (L.card : ℝ) ≤ (7 : ℝ) ^ n * (K / ρ + 2) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, cell ρ (leftCorner b (cell b (γ t))) ∈ L := by
  classical
  let σ : ℝ := ρ / K
  have hσ : 0 < σ := div_pos hρ hK
  let I : Finset ℤ := Finset.Icc 0 ⌊1 / σ⌋
  let a : ℤ → Fin n → ℝ := fun j e => γ ((j : ℝ) * σ) e - 2 * ρ
  let F : ℤ → Finset (Fin n → ℤ) := fun j => cubeIndices ρ (5 * ρ) (a j)
  let L : Finset (Fin n → ℤ) := I.biUnion F
  have hIcard : (I.card : ℝ) ≤ K / ρ + 2 := by
    have h := card_Icc_floor_le (x := (0 : ℝ)) (y := 1 / σ) (by positivity)
    simpa only [Int.floor_zero, sub_zero, I, σ, one_div_div] using h
  have hFcard (j : ℤ) : ((F j).card : ℝ) ≤ (7 : ℝ) ^ n := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (card_cubeIndices hρ (by positivity : 0 ≤ 5 * ρ) (a j))
    simpa only [F, mul_div_cancel_right₀ (5 : ℝ) hρ.ne',
      show (5 : ℝ) + 2 = 7 by norm_num, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (7 : ℝ) ^ n)] using h
  refine ⟨L, ?_, ?_⟩
  · calc
      (L.card : ℝ) ≤ ∑ j ∈ I, ((F j).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := I) (t := F))
      _ ≤ ∑ _j ∈ I, (7 : ℝ) ^ n := Finset.sum_le_sum (fun j _ => hFcard j)
      _ = (I.card : ℝ) * (7 : ℝ) ^ n := by simp [nsmul_eq_mul]
      _ ≤ (K / ρ + 2) * (7 : ℝ) ^ n := mul_le_mul_of_nonneg_right hIcard (by positivity)
      _ = _ := by ring
  · intro t ht
    let j : ℤ := ⌊t / σ⌋
    have hjI : j ∈ I := by
      exact Finset.mem_Icc.mpr
        ⟨Int.floor_nonneg.mpr (div_nonneg ht.1 hσ.le),
          Int.floor_mono (div_le_div_of_nonneg_right ht.2 hσ.le)⟩
    let u : ℝ := (j : ℝ) * σ
    have hu0 : 0 ≤ u := by
      have hj0 : (0 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hjI).1
      exact mul_nonneg hj0 hσ.le
    have hut : u ≤ t := (le_div_iff₀ hσ).1 (Int.floor_le (t / σ))
    have hu1 : u ≤ 1 := hut.trans ht.2
    have hgap : |t - u| ≤ σ := by
      have h := (div_lt_iff₀ hσ).1 (Int.lt_floor_add_one (t / σ))
      rw [abs_of_nonneg (sub_nonneg.mpr hut)]
      dsimp only [u, j]
      linarith
    have hpath : ‖γ t - γ u‖ ≤ ρ := by
      calc
        _ ≤ K * |t - u| := hlip t ht u ⟨hu0, hu1⟩
        _ ≤ K * σ := mul_le_mul_of_nonneg_left hgap hK.le
        _ = ρ := by dsimp only [σ]; field_simp
    have hdist : ‖leftCorner b (cell b (γ t)) - γ u‖ ≤ 2 * ρ := by
      calc
        _ ≤ ‖leftCorner b (cell b (γ t)) - γ t‖ + ‖γ t - γ u‖ := by
          simpa only [dist_eq_norm] using dist_triangle (leftCorner b (cell b (γ t))) (γ t) (γ u)
        _ ≤ b + ρ := by
          gcongr
          simpa only [norm_sub_rev] using norm_sub_leftCorner_le hb (γ t)
        _ ≤ 2 * ρ := by linarith
    have hbox : ∀ e, leftCorner b (cell b (γ t)) e ∈ Ico (a j e) (a j e + 5 * ρ) := by
      intro e
      have he : |leftCorner b (cell b (γ t)) e - γ u e| ≤ 2 * ρ :=
        (norm_le_pi_norm (leftCorner b (cell b (γ t)) - γ u) e).trans hdist
      obtain ⟨hlo, hhi⟩ := abs_le.mp he
      dsimp only [a]
      change leftCorner b (cell b (γ t)) e ∈ Ico (γ u e - 2 * ρ) (γ u e - 2 * ρ + 5 * ρ)
      constructor <;> linarith
    exact Finset.mem_biUnion.mpr ⟨j, hjI, cell_mem_cubeIndices hρ (a j) _ hbox⟩

theorem scalarPosition_time_lipschitz {H : ℝ} (hH : 1 ≤ H) (l : ScalarLine)
    (hcoeff : ∀ e, |l.2 e| ≤ H) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖scalarPosition (l, t) - scalarPosition (l, u)‖ ≤ 3 * H * |t - u| := by
  have hH0 : 0 ≤ H := by linarith
  have hyid : scalarY l t - scalarY l u = (t - u) * l.2 1 := by dsimp [scalarY]; ring
  have hy : |scalarY l t - scalarY l u| ≤ H * |t - u| := by
    rw [hyid, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hcoeff 1) (abs_nonneg _)
  have hxid : scalarX l t - scalarX l u = (t - u) * (l.2 3 + (t + u) * l.2 4) := by
    dsimp [scalarX]
    ring
  have htu : |t + u| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg ht.1 hu.1)]
    linarith [ht.2, hu.2]
  have hxcoeff : |l.2 3 + (t + u) * l.2 4| ≤ 3 * H := by
    have hm := mul_le_mul htu (hcoeff 4) (abs_nonneg (l.2 4)) (by norm_num : (0 : ℝ) ≤ 2)
    have hh := abs_add_le (l.2 3) ((t + u) * l.2 4)
    rw [abs_mul] at hh
    linarith [hcoeff 3]
  have hx : |scalarX l t - scalarX l u| ≤ 3 * H * |t - u| := by
    rw [hxid, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hxcoeff (abs_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 3 * H * |t - u|)).2
  intro e
  fin_cases e
  · change |t - u| ≤ 3 * H * |t - u|
    have h3H : 1 ≤ 3 * H := by linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h3H (abs_nonneg (t - u))
  · change |scalarY l t - scalarY l u| ≤ 3 * H * |t - u|
    have h3H : H ≤ 3 * H := by linarith
    exact hy.trans (mul_le_mul_of_nonneg_right h3H (abs_nonneg _))
  · change |scalarX l t - scalarX l u| ≤ 3 * H * |t - u|
    exact hx

theorem scalar_trajectory_assigned_cell_list {H ρ b : ℝ} (hH : 1 ≤ H)
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ) (l : ScalarLine)
    (hcoeff : ∀ e, |l.2 e| ≤ H) :
    ∃ L : Finset (Fin 3 → ℤ), (L.card : ℝ) ≤ 343 * (3 * H / ρ + 2) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        cell ρ (leftCorner b (cell b (scalarPosition (l, t)))) ∈ L := by
  simpa only [show (7 : ℝ) ^ 3 = 343 by norm_num] using
    curve_assigned_cell_list (fun t => scalarPosition (l, t)) (by linarith : 0 < 3 * H)
      hρ hb hbρ (fun t ht u hu => scalarPosition_time_lipschitz hH l hcoeff ht hu)

end Submission.Obl.k4_scalar_graph_residual_discovery
