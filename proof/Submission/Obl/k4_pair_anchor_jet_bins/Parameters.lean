import Submission.Obl.k4_pair_anchor_jet_bins.Powers

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Filter

/-- Choose all powers before the coefficients, the trajectory, or `δ` are specified. -/
theorem choose_scale_parameters (J : ℕ) (k CF C₁ C₂ C₀ A₁ : ℝ)
    (hk : 1 ≤ k) (hCF : 0 < CF) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ CR CK CB CV V A₀ : ℝ, 0 < CR ∧ 0 < CK ∧ 2 ≤ k * C₁ + V ∧ 2 ≤ CV ∧
      ∀ A : ℝ, A₀ ≤ A → A₁ ≤ A ∧ 2 ≤ A ∧
        C₀ * A ^ (k * CF + 1) ≤ A ^ CB ∧
        (2 * (3 : ℝ) ^ J) * A ^ CB ≤ A ^ V ∧
        2 * A ^ (k * C₂ + 2 * (k * C₁ + V)) ≤ A ^ CV ∧
        6 * A ^ (CV + 1) ≤ A ^ CK ∧
        A ^ (-CR) ≤ (8 * A ^ k)⁻¹ ∧ A ^ (-CR) ≤ A⁻¹ / 100 := by
  let CB : ℝ := k * CF + 2
  let V : ℝ := CB + 1
  let CV : ℝ := k * C₂ + 2 * (k * C₁ + V) + 1
  let CK : ℝ := CV + 3
  have hk0 : 0 < k := by linarith
  have hCB : 2 ≤ CB := by dsimp [CB]; nlinarith [mul_pos hk0 hCF]
  have hE : 2 ≤ k * C₁ + V := by dsimp [V]; nlinarith [mul_pos hk0 hC₁]
  have hCV : 2 ≤ CV := by dsimp [CV]; nlinarith [mul_pos hk0 hC₂]
  have hlarge : ∀ᶠ A : ℝ in atTop, A₁ ≤ A ∧ 2 ≤ A ∧
        C₀ * A ^ (k * CF + 1) ≤ A ^ CB ∧
        (2 * (3 : ℝ) ^ J) * A ^ CB ≤ A ^ V ∧
        2 * A ^ (k * C₂ + 2 * (k * C₁ + V)) ≤ A ^ CV ∧
        6 * A ^ (CV + 1) ≤ A ^ CK ∧
        A ^ (-(k + 2)) ≤ (8 * A ^ k)⁻¹ ∧ A ^ (-(k + 2)) ≤ A⁻¹ / 100 := by
    filter_upwards [eventually_ge_atTop A₁, eventually_ge_atTop (2 : ℝ),
      eventually_mul_power_le C₀ (p := k * CF + 1) (q := CB) (by dsimp [CB]; linarith),
      eventually_mul_power_le (2 * (3 : ℝ) ^ J) (p := CB) (q := V) (by dsimp [V]; linarith),
      eventually_mul_power_le 2 (p := k * C₂ + 2 * (k * C₁ + V)) (q := CV)
        (by dsimp [CV]; linarith),
      eventually_mul_power_le 6 (p := CV + 1) (q := CK) (by dsimp [CK]; linarith),
      eventually_short_radius hk] with A hA₁ hA₂ hforward hbin hreturn hfinish hradius
    exact ⟨hA₁, hA₂, hforward, hbin, hreturn, hfinish, hradius⟩
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hlarge
  exact ⟨k + 2, CK, CB, CV, V, A₀, by linarith,
    by dsimp [CK]; linarith, hE, hCV, hA₀⟩

end Submission.Obl.k4_pair_anchor_jet_bins
