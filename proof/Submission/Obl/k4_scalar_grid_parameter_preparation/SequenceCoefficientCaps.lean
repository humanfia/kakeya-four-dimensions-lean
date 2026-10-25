/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/SequenceCoefficientCaps.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientPriorCaps
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

/-! One subpower loss for every mixed coefficient-bin ceiling on the sequence. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical ENNReal

theorem exists_subpower_mixed_coefficient_caps (N K H : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hH : (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (W : ℕ → ℕ)
    (ν θ : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ)
    (Z : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (d : ℝ)
    (hbase : ∀ k g, IsProbabilityMeasure (ν k g) ∧ MeasurableSet (Z k g) ∧
      Z k g ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
      ρ k g ≤ ENNReal.ofReal (K k) • (ν k g).prod volume)
    (hduration : ∀ k g (C : Set (ℕ × (Fin 5 → ℝ))), MeasurableSet C →
      ENNReal.ofReal (1 / (100 * K k)) * θ k g C ≤
        (ρ k g).restrict (Z k g) (C ×ˢ Set.univ))
    (htrace : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
      R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
      ∀ (t : ℝ) (q a c : ℤ),
        ν k g {l | (l,t) ∈ Z k g ∧ l.2 0 + t * l.2 1 ∈ scalarVelocityBin (N k ^ (-r)) q ∧
          l.2 2 + t * l.2 3 + t ^ 2 * l.2 4 ∈ scalarVelocityBin (N k ^ (-s)) a ∧
          l.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
            ENNReal.ofReal (H k * N k ^ (-r - d * s)) *
              π k g (scalarVelocityBin (N k ^ (-b)) c)) :
    ∃ L : ℕ → ℝ, (∀ k, 1 ≤ L k ∧ H k ≤ L k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L k ≤ N k ^ ε) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s : ℝ),
        R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → ∀ q : Fin 5 → ℤ,
          θ k g {l | scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-s)) l.2 = q} ≤
            ENNReal.ofReal (L k * N k ^ (-r - d * s)) *
              π k g (scalarVelocityBin (N k ^ (-r)) (q 1)) := by
  let Q : ℕ → ℝ := fun k => max (K k) (H k)
  let L : ℕ → ℝ := fun k => 40000 * Q k ^ 3
  have hQ := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hK hH
  have hL := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
    (fun k => show 1 ≤ N k by linarith [hN k]) hNt hQ (A := 40000) (by norm_num) 3
  have hQ₁ (k) : 1 ≤ Q k := (hK.1 k).trans (le_max_left _ _)
  have hfactor (k) : (400 * K k / (1 / (100 * K k))) * H k ≤ L k := by
    have hKk : 0 < K k := zero_lt_one.trans_le (hK.1 k)
    have hprod : K k ^ 2 * H k ≤ Q k ^ 3 := by
      calc
        _ ≤ Q k ^ 2 * Q k := mul_le_mul
          (pow_le_pow_left₀ hKk.le (le_max_left _ _) 2) (le_max_right _ _)
          (by linarith [hH.1 k]) (sq_nonneg _)
        _ = _ := by ring
    calc
      _ = 40000 * (K k ^ 2 * H k) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num)
  refine ⟨L, ?_, hL.2, ?_⟩
  · intro k
    have hQ3 : Q k ≤ Q k ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ (hQ₁ k) (show 1 ≤ 3 by norm_num)
    refine ⟨hL.1 k, ?_⟩
    exact (le_max_right _ _).trans (hQ3.trans (by dsimp [L]; nlinarith [hQ₁ k]))
  · intro R hR
    filter_upwards [htrace R hR] with k hk
    intro g r s hr hr' hs hs' q
    letI : IsProbabilityMeasure (ν k g) := (hbase k g).1
    have hKk : 0 < K k := zero_lt_one.trans_le (hK.1 k)
    have hNk : 0 < N k := by linarith [hN k]
    have h := mixed_coefficient_prior_cap (ν k g) (θ k g) (ρ k g) Prod.snd measurable_snd
      (Z k g) (hbase k g).2.1 (hbase k g).2.2.1
      (K k) (1 / (100 * K k)) (N k ^ (-r)) (N k ^ (-s)) hKk.le
      (by positivity) (Real.rpow_pos_of_pos hNk _) (Real.rpow_pos_of_pos hNk _)
      (hbase k g).2.2.2 (hduration k g) (π k g) q
      (ENNReal.ofReal (H k * N k ^ (-r - d * s)))
      (fun t ht i j => hk g r s r hr hr' hs hs' hr hr' t i j (q 1))
    apply h.trans
    apply mul_le_mul _ le_rfl bot_le bot_le
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 400 * K k / (1 / (100 * K k)))]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hfactor k) (Real.rpow_nonneg hNk.le _)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
