/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarRegularizedPreparation.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarTracePreparation
import Submission.Obl.k4_scalar_grid_parameter_preparation.RegularizedPriorCore
import Submission.Obl.k4_scalar_grid_parameter_preparation.WeightedPruning

/-! Original-law density comparability and all-time caps on one regularized sequence. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal

/-- Density and duration regularization preserve a common all-real-scale trace mask.
The weights and the palette in every bound are the original ones. -/
theorem exists_scalar_regularized_preparation (N K : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (W : ℕ → ℕ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) (d : ℝ)
    (hbase : ∀ k g, IsProbabilityMeasure (ν k g) ∧
      (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧
      ρ k g ≤ ENNReal.ofReal (K k) • (ν k g).prod volume ∧
      ρ k g {p | p.2 ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0)
    (hcaps : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
      R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → ∀ i j a c : ℤ,
      ρ k g {p | (⌊p.2 / N k ^ (-r)⌋ : ℤ) = i ∧
        (⌊(p.1.2 0 + p.2 * p.1.2 1) / N k ^ (-r)⌋ : ℤ) = j ∧
        (⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / N k ^ (-s)⌋ : ℤ) = a ∧
        p.1.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
          ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) *
            π k g (scalarVelocityBin (N k ^ (-b)) c))
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (hω : ∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1)
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤
      ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) :
    ∃ (H : ℕ → ℝ)
      (θ : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
      (E Z : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)),
      (∀ k, 1 ≤ H k ∧ 100 * K k ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      (∀ k, ENNReal.ofReal ((H k)⁻¹) ≤
        ∑ g, ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ) ∧
      (∀ k g, θ k g ≤ ν k g ∧ θ k g Set.univ ≤ 1 ∧
        MeasurableSet (E k g) ∧ E k g ⊆ Z k g ∧ MeasurableSet (Z k g) ∧
        (∀ p ∈ Z k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ K k) ∧
        (∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ H k) ∧
        ρ k g (E k g)ᶜ ≤ ENNReal.ofReal (5 / (100 * K k)) ∧
        ENNReal.ofReal ((H k)⁻¹) • ((θ k g).prod volume).restrict (E k g) ≤
          (ρ k g).restrict (E k g) ∧
        (ρ k g).restrict (E k g) ≤
          ENNReal.ofReal (H k) • ((θ k g).prod volume).restrict (E k g) ∧
        (∀ C : Set (ℕ × (Fin 5 → ℝ)), MeasurableSet C →
          ENNReal.ofReal (1 / (100 * K k)) * θ k g C ≤
            (ρ k g).restrict (Z k g) (C ×ˢ Set.univ))) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
        R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
        ∀ (t : ℝ) (q a c : ℤ),
          ν k g {l | (l, t) ∈ Z k g ∧ l.2 0 + t * l.2 1 ∈ scalarVelocityBin (N k ^ (-r)) q ∧
            l.2 2 + t * l.2 3 + t ^ 2 * l.2 4 ∈ scalarVelocityBin (N k ^ (-s)) a ∧
            l.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
              ENNReal.ofReal (H k * N k ^ (-r - d * s)) *
                π k g (scalarVelocityBin (N k ^ (-b)) c) := by
  obtain ⟨L, Z, hL, hLsubpower, hZ, htrace⟩ :=
    exists_scalar_trace_preparation N K hN hNt hK W ν ρ π d hbase hcaps
  let H : ℕ → ℝ := fun k => 100 * L k
  have hKpos (k) : 0 < K k := zero_lt_one.trans_le (hK.1 k)
  letI (k : ℕ) (g : Fin (W k)) : IsProbabilityMeasure (ν k g) := (hbase k g).1
  have hregular (k) (g : Fin (W k)) := exists_regularized_original_prior
    (ν k g) (ρ k g) (K k) (1 / (100 * K k)) (3 / (100 * K k))
    (hKpos k).le (by have hKk := hKpos k; positivity) (by have hKk := hKpos k; positivity) (hbase k g).2.2.1
    (Z k g) (hZ k g).1 (fun p hp => ⟨Set.mem_univ _, ((hZ k g).2.1 p hp).1⟩)
    (hZ k g).2.2
  choose θ E hθν hθ₁ hE hEZ hloss hlo hhi hduration using hregular
  have hHK (k) : 100 * K k ≤ H k := by
    dsimp [H]
    nlinarith [(hL k).2, hKpos k]
  have hHpos (k) : 0 < H k := (by have hKk := hKpos k; positivity : 0 < 100 * K k).trans_le (hHK k)
  have hinv (k) : (H k)⁻¹ ≤ 1 / (100 * K k) := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by have hKk := hKpos k; positivity : 0 < 100 * K k) (hHK k)
  have hloss' (k) (g : Fin (W k)) : ρ k g (E k g)ᶜ ≤
      ENNReal.ofReal (5 / (100 * K k)) := by
    convert hloss k g using 1 <;> congr 1 <;> ring
  refine ⟨H, θ, E, Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(by dsimp [H]; nlinarith [(hL k).1]), hHK k⟩
  · intro ε hε
    have hp := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      (fun k => show 1 ≤ N k by linarith [hN k]) hNt (fun k => (hL k).1) hLsubpower
      1 (a := 0) (b := ε) hε (A := 100) (by norm_num)
    simpa only [pow_one, Real.rpow_zero, mul_one, H] using hp.mono (fun k hk => hk.le)
  · intro k
    have hw : (∑ g, ENNReal.ofReal (ω k g)) ≤ 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun g hg => (hω k).1 g), (hω k).2]
      norm_num
    have hbudget : 5 / (100 * K k) ≤ (K k)⁻¹ / 2 := by
      rw [inv_eq_one_div, div_div]
      apply (div_le_div_iff₀ (by have hKk := hKpos k; positivity : 0 < 100 * K k)
        (by have hKk := hKpos k; positivity : 0 < K k * 2)).mpr
      nlinarith [hKpos k]
    have hm := weighted_retained_mass_of_uniform_loss (ρ k)
      (fun g => ENNReal.ofReal (ω k g)) (E k) (K k)⁻¹ (5 / (100 * K k))
      (by have hKk := hKpos k; positivity) (by have hKk := hKpos k; positivity) hbudget hw (hmass k) (hloss' k)
    have hnum : (H k)⁻¹ ≤ (K k)⁻¹ / 2 := by
      calc
        _ ≤ 1 / (100 * K k) := hinv k
        _ ≤ _ := by
          rw [inv_eq_one_div, div_div]
          apply (div_le_div_iff₀ (by have hKk := hKpos k; positivity : 0 < 100 * K k)
            (by have hKk := hKpos k; positivity : 0 < K k * 2)).mpr
          nlinarith [hKpos k]
    simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using
      (ENNReal.ofReal_le_ofReal hnum).trans hm
  · intro k g
    refine ⟨hθν k g, hθ₁ k g, hE k g, hEZ k g, (hZ k g).1, (hZ k g).2.1,
      ?_, hloss' k g, ?_, ?_, hduration k g⟩
    · have hc : ∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ K k :=
        ae_mono (hθν k g) (hbase k g).2.1
      exact hc.mono fun l hl e => (hl e).trans (by nlinarith [hHK k, hKpos k])
    · apply le_trans ?_ (hlo k g)
      apply Measure.le_iff.mpr
      intro C hC
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul (ENNReal.ofReal_le_ofReal (hinv k)) le_rfl bot_le bot_le
    · apply le_trans (hhi k g)
      apply Measure.le_iff.mpr
      intro C hC
      simp only [Measure.smul_apply, smul_eq_mul]
      apply mul_le_mul _ le_rfl bot_le bot_le
      exact ENNReal.ofReal_le_ofReal (by nlinarith [hHK k, hKpos k])
  · intro R hR
    filter_upwards [htrace R hR] with k hk
    intro g r s b hr hr' hs hs' hb hb' t q a c
    apply (hk g r s b hr hr' hs hs' hb hb' t q a c).trans
    apply mul_le_mul _ le_rfl bot_le bot_le
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (by dsimp [H]; nlinarith [(hL k).1] : L k ≤ H k)
      (Real.rpow_nonneg (by linarith [hN k]) _)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
