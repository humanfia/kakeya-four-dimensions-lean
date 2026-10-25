import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

namespace Submission.Obl.k4_graph_atlas_representative_realization

open Submission.Obl.k4_quadratic_atlas_normalization

lemma exists_threshold {a ζ : ℝ} (ha : 0 < a) (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → 16 ≤ N ^ a ∧ 8 ≤ N ^ ζ := by
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (16 : ℝ)))
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hζ).eventually (Filter.eventually_ge_atTop (8 : ℝ)))
  refine ⟨max 2 (max n₁ n₂), le_max_left _ _, fun N hN => ?_⟩
  exact ⟨hn₁ N ((le_max_left n₁ n₂).trans ((le_max_right _ _).trans hN)),
    hn₂ N ((le_max_right n₁ n₂).trans ((le_max_right _ _).trans hN))⟩

lemma root_error_compare {N L θ gain h r₀ B : ℝ} (hN : 1 ≤ N)
    (hL : 0 < L) (hθ : 0 < θ) (hgain : 0 < gain) (hh : gain ≤ h)
    (hB : 0 < B) (hNa : 16 ≤ N ^ ((θ / 4) * gain * L)) :
    δ N r₀ / B * N ^ (-(θ * h * L)) ≤
      δ N (r₀ + (θ / 4) * gain * L) / (8 * B) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let a := (θ / 4) * gain * L
  have ha : 0 < a := by dsimp [a]; positivity
  have htheta : 2 * a ≤ θ * h * L := by
    have hm := mul_le_mul_of_nonneg_left hh hθ.le
    have hm' := mul_le_mul_of_nonneg_right hm hL.le
    dsimp [a]
    nlinarith [mul_pos (mul_pos hθ hgain) hL]
  have hneg : N ^ (-a) ≤ 1 / 16 := by
    rw [Real.rpow_neg hN0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hNa
  have hd : δ N r₀ ≤ 2 * δ N (r₀ + a) * N ^ a := by
    have ht := delta_shift_upper hN0 (r₀ + a) a
    simpa only [add_sub_cancel_right] using ht
  have hpow : N ^ (a - θ * h * L) ≤ N ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hproduct : δ N r₀ * N ^ (-(θ * h * L)) ≤ δ N (r₀ + a) / 8 := by
    calc
      _ ≤ (2 * δ N (r₀ + a) * N ^ a) * N ^ (-(θ * h * L)) := by gcongr
      _ = 2 * δ N (r₀ + a) * N ^ (a - θ * h * L) := by
        rw [mul_assoc, ← Real.rpow_add hN0]
        congr 2
      _ ≤ 2 * δ N (r₀ + a) * (1 / 16) := by
        exact mul_le_mul_of_nonneg_left (hpow.trans hneg) (by unfold δ; positivity)
      _ = δ N (r₀ + a) / 8 := by ring
  calc
    _ = (δ N r₀ * N ^ (-(θ * h * L))) / B := by ring
    _ ≤ (δ N (r₀ + a) / 8) / B := div_le_div_of_nonneg_right hproduct hB.le
    _ = _ := by dsimp [a]; ring

end Submission.Obl.k4_graph_atlas_representative_realization
