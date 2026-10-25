import Mathlib

namespace Submission.Obl.k4_scalar_coefficient_clustering

open Filter
open scoped Topology

noncomputable section

theorem scalar_budget_identity {N : ℝ} (hN : 0 < N) (C η c s τ d ε : ℝ) :
    (2 * (N ^ η) ^ 4) *
      (500000000000 * C * (4 * N ^ η) * (N ^ (-c)) ^ 2 * N ^ ((c + 2) * τ) *
        (N ^ η * (N ^ (-c)) ^ (-1 - d)) *
        (N ^ η * (N ^ (-c) * N ^ s) ^ (d - 1) +
          (N ^ s) ^ 3 * N ^ (-c * d - ε) / N ^ (-c))) =
      4000000000000 * C *
        (N ^ (7 * η + (c + 2) * τ + s * (d - 1)) +
          N ^ (6 * η + (c + 2) * τ + 3 * s - ε)) := by
  have hn (a : ℝ) (m : ℕ) : (N ^ a) ^ m = N ^ (a * (m : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  have hh (a b : ℝ) : (N ^ a) ^ b = N ^ (a * b) := (Real.rpow_mul hN.le _ _).symm
  have hm (a b : ℝ) : N ^ a * N ^ b = N ^ (a + b) := (Real.rpow_add hN _ _).symm
  have h₁ : (N ^ η) ^ 7 * (N ^ (-c)) ^ 2 * N ^ ((c + 2) * τ) *
      (N ^ (-c)) ^ (-1 - d) * (N ^ (-c) * N ^ s) ^ (d - 1) =
      N ^ (7 * η + (c + 2) * τ + s * (d - 1)) := by
    rw [hn η 7, hn (-c) 2, hm (-c) s, hh (-c + s) (d - 1), hh (-c) (-1 - d)]
    simp only [mul_assoc, hm]
    congr 1
    ring
  have h₂ : (N ^ η) ^ 6 * (N ^ (-c)) ^ 2 * N ^ ((c + 2) * τ) *
      (N ^ (-c)) ^ (-1 - d) * (N ^ s) ^ 3 * N ^ (-c * d - ε) / N ^ (-c) =
      N ^ (6 * η + (c + 2) * τ + 3 * s - ε) := by
    rw [hn η 6, hn (-c) 2, hn s 3, hh (-c) (-1 - d)]
    simp only [div_eq_mul_inv, ← Real.rpow_neg hN.le, mul_assoc, hm]
    congr 1
    ring
  linear_combination (4000000000000 * C) * h₁ + (4000000000000 * C) * h₂

theorem scalar_budget_upper {N D M : ℝ} (hN : 0 < N) (hD : 0 < D)
    (C η c s τ d ε : ℝ) (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hM : 0 ≤ M)
    (hlo : 4 * N ^ η ≤ D * N ^ (-c)) (hhigh : D ≤ N ^ (c + 2))
    (hsize : M ≤ N ^ η * (N ^ (-c)) ^ (-1 - d)) :
    (2 * (N ^ η) ^ 4) *
      (500000000000 * C * (4 * N ^ η) ^ 3 / D ^ 2 * D ^ τ * M *
        (N ^ η * (N ^ (-c) * N ^ s) ^ (d - 1) +
          (N ^ s) ^ 3 * N ^ (-c * d - ε) / N ^ (-c))) ≤
      4000000000000 * C *
        (N ^ (7 * η + (c + 2) * τ + s * (d - 1)) +
          N ^ (6 * η + (c + 2) * τ + 3 * s - ε)) := by
  have hR : 0 < 4 * N ^ η := by positivity
  have hp : 0 < N ^ (-c) := Real.rpow_pos_of_pos hN _
  have hratio : (4 * N ^ η) ^ 3 / D ^ 2 ≤ (4 * N ^ η) * (N ^ (-c)) ^ 2 := by
    apply (div_le_iff₀ (pow_pos hD 2)).mpr
    have hs := pow_le_pow_left₀ hR.le hlo 2
    have hh := mul_le_mul_of_nonneg_left hs hR.le
    nlinarith
  have hpow : D ^ τ ≤ N ^ ((c + 2) * τ) := by
    have hh := Real.rpow_le_rpow hD.le hhigh hτ
    rwa [← Real.rpow_mul hN.le] at hh
  calc
    _ ≤ (2 * (N ^ η) ^ 4) *
      (500000000000 * C * (4 * N ^ η) * (N ^ (-c)) ^ 2 * N ^ ((c + 2) * τ) *
        (N ^ η * (N ^ (-c)) ^ (-1 - d)) *
        (N ^ η * (N ^ (-c) * N ^ s) ^ (d - 1) +
          (N ^ s) ^ 3 * N ^ (-c * d - ε) / N ^ (-c))) := by
      rw [show 500000000000 * C * (4 * N ^ η) ^ 3 / D ^ 2 =
        (500000000000 * C) * ((4 * N ^ η) ^ 3 / D ^ 2) by ring]
      have hh := mul_le_mul hratio hpow (Real.rpow_nonneg hD.le τ)
        (by positivity : 0 ≤ (4 * N ^ η) * (N ^ (-c)) ^ 2)
      have hh' := mul_le_mul hh hsize hM (by positivity : 0 ≤
        ((4 * N ^ η) * (N ^ (-c)) ^ 2) * N ^ ((c + 2) * τ))
      have hm := mul_le_mul_of_nonneg_left hh' (by positivity : 0 ≤
        (2 * (N ^ η) ^ 4) * (500000000000 * C) *
          (N ^ η * (N ^ (-c) * N ^ s) ^ (d - 1) +
            (N ^ s) ^ 3 * N ^ (-c * d - ε) / N ^ (-c)))
      convert hm using 1 <;> ring
    _ = _ := scalar_budget_identity hN C η c s τ d ε

theorem discrete_scale {N η c : ℝ} (hN : 8 ≤ N) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hc : 0 < c) :
    ∃ D : ℕ, 1 ≤ D ∧ 4 * N ^ η ≤ (D : ℝ) * N ^ (-c) ∧
      (D : ℝ) * N ^ (-c) ≤ 2 * (4 * N ^ η) ∧
      (D : ℝ) ≤ N ^ (c + 2) ∧ N ^ c ≤ (D : ℝ) := by
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hK1 : 1 ≤ N ^ η := Real.one_le_rpow hN1 hη
  have hKN : N ^ η ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hη1
  have hp : 0 < N ^ (-c) := Real.rpow_pos_of_pos hNpos _
  have hp1 : N ^ (-c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  let x : ℝ := 4 * N ^ η / N ^ (-c)
  have hx1 : 1 ≤ x := (le_div_iff₀ hp).mpr (by nlinarith)
  let D : ℕ := ⌈x⌉₊
  have hceil : x ≤ (D : ℝ) := Nat.le_ceil _
  have hceilhi : (D : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le
  have hDpos : (0 : ℝ) < D := by linarith
  have hlo : 4 * N ^ η ≤ (D : ℝ) * N ^ (-c) := (div_le_iff₀ hp).mp hceil
  have hhi : (D : ℝ) * N ^ (-c) ≤ 8 * N ^ η := by
    have hh : (D : ℝ) ≤ 2 * x := by linarith
    have hm := mul_le_mul_of_nonneg_right hh hp.le
    dsimp [x] at hm
    field_simp at hm
    nlinarith
  have hidentity : N ^ (c + 2) * N ^ (-c) = N ^ (2 : ℕ) := by
    rw [← Real.rpow_add hNpos]
    norm_num [show c + 2 + -c = (2 : ℝ) by ring]
  have hhigh : (D : ℝ) ≤ N ^ (c + 2) := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [hidentity]
  have hNc : N ^ c * N ^ (-c) = 1 := by rw [← Real.rpow_add hNpos]; simp
  have hbase : N ^ c ≤ (D : ℝ) := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [hNc]
  exact ⟨D, by exact_mod_cast (by linarith : (1 : ℝ) ≤ D), hlo, by linarith, hhigh, hbase⟩

theorem negative_two_powers_eventually {C e₁ e₂ : ℝ} (he₁ : e₁ < 0) (he₂ : e₂ < 0) :
    ∀ᶠ N : ℝ in atTop, C * (N ^ e₁ + N ^ e₂) < 1 := by
  have h₁ : Tendsto (fun N : ℝ => N ^ e₁) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr he₁)
  have h₂ : Tendsto (fun N : ℝ => N ^ e₂) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr he₂)
  have hh : Tendsto (fun N : ℝ => C * (N ^ e₁ + N ^ e₂)) atTop (𝓝 0) := by
    simpa using (h₁.add h₂).const_mul C
  exact hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))

theorem inverse_cube_rpow {N : ℝ} (hN : 0 < N) (η : ℝ) :
    1 / (N ^ η) ^ 3 = N ^ (-3 * η) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, one_div, ← Real.rpow_neg hN.le]
  congr 1
  ring

theorem long_label_threshold {N η ε : ℝ} (hN : 1 ≤ N) (hη : 3 * η ≤ ε) :
    N ^ (-ε) ≤ 1 / (N ^ η) ^ 3 := by
  rw [inverse_cube_rpow (by linarith) η]
  exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem discrete_density {N D η ζ c : ℝ} (hN : 1 ≤ N) (hD : 0 < D) (hζ : 0 < ζ)
    (hbase : N ^ c ≤ D) (hη : 3 * η ≤ c * ζ) :
    D ^ (1 - ζ) ≤ D / (N ^ η) ^ 3 := by
  have hNpos : 0 < N := by linarith
  have hh : D ^ (-ζ) ≤ N ^ (-3 * η) := by
    calc
      _ ≤ (N ^ c) ^ (-ζ) := Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
      _ = N ^ (c * (-ζ)) := (Real.rpow_mul hNpos.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  calc
    D ^ (1 - ζ) = D ^ (1 : ℝ) * D ^ (-ζ) := by rw [← Real.rpow_add hD]; rfl
    _ = D * D ^ (-ζ) := by rw [Real.rpow_one]
    _ ≤ D * N ^ (-3 * η) := mul_le_mul_of_nonneg_left hh hD.le
    _ = _ := by rw [← inverse_cube_rpow hNpos η]; ring

end
end Submission.Obl.k4_scalar_coefficient_clustering
