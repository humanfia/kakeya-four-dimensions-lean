import Submission.Obl.k4_oss_flat_decay.Energy

open scoped BigOperators

namespace Submission.Obl.k4_oss_weighted_level_transfer

lemma exists_transfer_parameters {θ γ r₀ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hr₀ : 0 < r₀) :
    ∃ (a r : ℝ) (M : ℕ), 0 < a ∧ 100 * a ≤ θ ∧ 100 * a ≤ γ ∧ 100 * a ≤ 1 ∧
      0 < r ∧ r ≤ 1 ∧ r ≤ r₀ ∧ 3 ≤ a * (M : ℝ) ∧
      ∀ δ : ℝ, 0 < δ → δ < r → 390 * ((M : ℝ) + 1) ^ 4 * δ ^ a ≤ 1 := by
  let a := min θ (min γ 1) / 100
  have ha : 0 < a := div_pos (lt_min hθ (lt_min hγ (by norm_num))) (by norm_num)
  have haθ : 100 * a ≤ θ := by dsimp [a]; nlinarith [min_le_left θ (min γ 1)]
  have haγ : 100 * a ≤ γ := by
    dsimp [a]
    nlinarith [(min_le_right θ (min γ 1)).trans (min_le_left γ 1)]
  have ha1 : 100 * a ≤ 1 := by
    dsimp [a]
    nlinarith [(min_le_right θ (min γ 1)).trans (min_le_right γ 1)]
  obtain ⟨M, hM⟩ := exists_nat_gt (3 / a)
  have hMa : 3 ≤ a * (M : ℝ) := by
    have := (div_lt_iff₀ ha).mp hM
    nlinarith
  let C := 390 * ((M : ℝ) + 1) ^ 4
  obtain ⟨r₁, hr₁, hr₁1, hscale⟩ :=
    Submission.Obl.k4_oss_flat_decay.exists_scale_absorb_constant C a ha
  refine ⟨a, min r₁ r₀, M, ha, haθ, haγ, ha1, lt_min hr₁ hr₀,
    (min_le_left _ _).trans hr₁1, min_le_right _ _, hMa, ?_⟩
  intro δ hδ hδr
  have hc := hscale δ hδ (hδr.trans_le (min_le_left _ _))
  have hp := mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hδ a).le
  have heq : δ ^ (-a) * δ ^ a = 1 := by
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
  simpa only [heq] using hp

lemma direction_cap_of_small_power {δ a θ s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : 0 ≤ s) (hθ : 2 * a ≤ θ) (hsmall : 4 * δ ^ a ≤ 1)
    (ν : MeasureTheory.Measure ℝ)
    (hcap : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (4 * δ ^ (-a) * u ^ s)) :
    ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (s / 2)) := by
  intro x u hδu hu1
  apply (hcap x u hδu hu1).trans
  apply ENNReal.ofReal_le_ofReal
  have hu : 0 < u := hδ.trans_le hδu
  have hc : 4 * δ ^ (-a) ≤ δ ^ (-θ) := by
    have heq : 4 * δ ^ (-a) = (4 * δ ^ a) * δ ^ (-2 * a) := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 1
      congr 1
      ring
    calc
      _ = _ := heq
      _ ≤ 1 * δ ^ (-2 * a) :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hδ _).le
      _ = δ ^ (-2 * a) := one_mul _
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have he : u ^ s ≤ u ^ (s / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith)
  exact mul_le_mul hc he (Real.rpow_pos_of_pos hu _).le (Real.rpow_pos_of_pos hδ _).le

end Submission.Obl.k4_oss_weighted_level_transfer
