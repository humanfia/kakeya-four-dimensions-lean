import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_unit_decay.ChainTower
import Submission.Obl.k4_oss_unit_decay.Iteration
import Submission.Obl.k4_oss_unit_decay.Stability
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_unit_decay`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_unit_decay`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_unit_decay/`
belong to this obligation.
-/


open MeasureTheory

namespace Submission.Obl.k4_oss_unit_decay

/-- The source index after the required range is immaterial. -/
noncomputable def mixingTower (m : ℕ) (μ : Fin (m + 2) → Measure ℝ) :
    ℕ → Measure ℝ :=
  Nat.rec (halfLaw (μ 0))
    (fun k α => mix α (μ (Fin.ofNat (m + 2) (k + 1))))

lemma frostman_weaken {α : Measure ℝ} {r s a b : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hab : a ≤ b)
    (h : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      α (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-a) * u ^ s)) :
    ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      α (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-b) * u ^ s) := by
  intro x u hu hu1
  exact (h x u hu hu1).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (neg_le_neg hab))
      (Real.rpow_nonneg (hr.le.trans hu) s)))

end Submission.Obl.k4_oss_unit_decay

open Submission.Obl.k4_oss_unit_decay

theorem Submission.k4_oss_unit_decay : (∀ δ : ℝ, 0 < δ → ∀ α β : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure β → ∀ ω : MeasureTheory.Measure ℝ, ω = MeasureTheory.Measure.map (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q.1.1 * q.1.2 - q.2.1 * q.2.2) / 4) ((α.prod β).prod (α.prod β)) → (ω.prod ω) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≤ 3 * MeasureTheory.lintegral (β.prod β) (fun p : ℝ × ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ})) → (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ c ε δ₀ : ℝ, 0 < c ∧ 0 < ε ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ α β : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure β → α (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → β (Set.Icc (1 : ℝ) 2)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → α (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → β (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → ENNReal.ofReal (δ ^ (1 - γ)) ≤ (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} → MeasureTheory.lintegral (β.prod β) (fun p : ℝ × ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ}) ≤ ENNReal.ofReal (δ ^ c) * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}) → (∀ s : ℝ, 0 < s → s ≤ 1 → ∃ γ ε τ δ₀ : ℝ, 0 < γ ∧ 0 < ε ∧ 0 < τ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ α β : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure β → α (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → β (Set.Icc (1 : ℝ) 2)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → β (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≤ ENNReal.ofReal (δ ^ (1 - γ)) → ∀ ζ : ℝ, δ⁻¹ ≤ |ζ| → |ζ| ≤ 2 * δ⁻¹ → ‖MeasureTheory.integral (α.prod β) (fun p : ℝ × ℝ => Complex.exp (((-2 * Real.pi * ζ * (p.1 * p.2) : ℝ) : ℂ) * Complex.I))‖ ≤ δ ^ τ) → ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ n : ℕ, 2 ≤ n ∧ ∃ ε τ δ₀ : ℝ, 0 < ε ∧ 0 < τ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ μ : Fin n → MeasureTheory.Measure ℝ, (∀ j : Fin n, MeasureTheory.IsProbabilityMeasure (μ j)) → (∀ j : Fin n, μ j (Set.Icc (1 : ℝ) 2)ᶜ = 0) → (∀ (j : Fin n) (x u : ℝ), δ ≤ u → u ≤ 1 → μ j (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → ∀ ξ : ℝ, δ⁻¹ ≤ |ξ| → |ξ| ≤ 2 * δ⁻¹ → ‖MeasureTheory.integral (MeasureTheory.Measure.pi μ) (fun x : Fin n → ℝ => Complex.exp (((-2 * Real.pi * ξ * (∏ j : Fin n, x j) : ℝ) : ℂ) * Complex.I))‖ ≤ δ ^ τ := by
  intro collision_cs projection_flattening flat_decay s hs hs1
  rcases flat_decay s hs hs1 with
    ⟨γL, εL, τL, δL, hγL, hεL, hτL, hδL, hflat⟩
  let γ : ℝ := min γL (1 / 2)
  have hγ : 0 < γ := lt_min hγL (by norm_num)
  have hγ1 : γ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  rcases collision_iteration projection_flattening
      s hs hs1 γ hγ hγ1 with ⟨m, ηI, r₀, hηI, hr₀, hiteration⟩
  let η : ℝ := min ηI εL
  have hη : 0 < η := lt_min hηI hεL
  rcases mixing_frostman m s hs hs1 η hη with
    ⟨ε, δF, hε, hδF, hpreserve⟩
  have hP : 0 < (2 ^ m : ℕ) := by positivity
  have hPR : 0 < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hP
  refine ⟨m + 2, by omega, ε, τL / ((2 ^ m : ℕ) : ℝ),
    min δF (min r₀ (min δL 1)), hε, div_pos hτL hPR,
    lt_min hδF (lt_min hr₀ (lt_min hδL (by norm_num))), ?_⟩
  intro δ hδ hδsmall μ hμ hμsupport hμfrost ξ hξlo hξhi
  rcases lt_min_iff.mp hδsmall with ⟨hδF', hδsmall⟩
  rcases lt_min_iff.mp hδsmall with ⟨hδr₀, hδsmall⟩
  rcases lt_min_iff.mp hδsmall with ⟨hδδL, hδ1⟩
  let K : ℝ := 2 * (4 : ℝ) ^ m
  let r : ℝ := δ / K
  have hK1 : 1 ≤ K := by
    have h4 : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
    dsimp [K]
    linarith
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) hK1
  have hr : 0 < r := div_pos hδ hK
  have hrδ : r ≤ δ := div_le_self hδ.le hK1
  have hr1 : r < 1 := hrδ.trans_lt hδ1
  let ν : ℕ → Measure ℝ := mixingTower m μ
  have hνstep (k : ℕ) (_hk : k < m) :
      ν (k + 1) = mix (ν k) (μ (Fin.ofNat (m + 2) (k + 1))) := rfl
  rcases hpreserve δ hδ hδF' μ hμ hμsupport hμfrost ν rfl hνstep with
    ⟨hνprob, hνsupport, hνfrost, hμfrost'⟩
  have hνfrostI : ∀ k : ℕ, k ≤ m → ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      ν k (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ηI) * u ^ s) := by
    intro k hk
    exact frostman_weaken hr hr1.le (min_le_left _ _) (hνfrost k hk)
  have hμfrostI : ∀ j : Fin (m + 2), ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      μ j (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ηI) * u ^ s) := by
    intro j
    exact frostman_weaken hr hr1.le (min_le_left _ _) (hμfrost' j)
  have hcollision := hiteration r hr (hrδ.trans_lt hδr₀) μ hμ hμsupport
    hμfrostI ν hνprob hνsupport hνfrostI hνstep
  have hcollisionL : (ν m).prod (ν m) {p : ℝ × ℝ | |p.1 - p.2| ≤ r} ≤
      ENNReal.ofReal (r ^ (1 - γL)) := by
    exact hcollision.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hr hr1.le
        (sub_le_sub_left (min_le_left γL (1 / 2)) 1)))
  have hμfrostL : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      μ (Fin.last (m + 1)) (Set.Icc (x - u) (x + u)) ≤
        ENNReal.ofReal (r ^ (-εL) * u ^ s) :=
    frostman_weaken hr hr1.le (min_le_right _ _) (hμfrost' _)
  have hrinv : r⁻¹ = K * δ⁻¹ := by
    dsimp [r]
    rw [inv_div, div_eq_mul_inv]
  have hfreqlo : r⁻¹ ≤ |K * ξ| := by
    rw [hrinv, abs_mul, abs_of_pos hK]
    exact mul_le_mul_of_nonneg_left hξlo hK.le
  have hfreqhi : |K * ξ| ≤ 2 * r⁻¹ := by
    rw [hrinv, abs_mul, abs_of_pos hK]
    calc
      K * |ξ| ≤ K * (2 * δ⁻¹) := mul_le_mul_of_nonneg_left hξhi hK.le
      _ = 2 * (K * δ⁻¹) := by ring
  have hbilinear := hflat r hr (hrδ.trans_lt hδδL)
    (ν m) (μ (Fin.last (m + 1))) (hνprob m le_rfl) (hμ _)
    (hνsupport m le_rfl) (hμsupport _) hμfrostL hcollisionL
    (K * ξ) hfreqlo hfreqhi
  have hchain := cs_chain m μ hμ ν rfl hνstep ξ
  have hpower := hchain.trans (hbilinear.trans
    (Real.rpow_le_rpow hr.le hrδ hτL.le))
  have hroot : (δ ^ (τL / ((2 ^ m : ℕ) : ℝ))) ^ (2 ^ m : ℕ) = δ ^ τL := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le,
      div_mul_cancel₀ _ (ne_of_gt hPR)]
  apply (pow_le_pow_iff_left₀ (norm_nonneg _)
    (Real.rpow_nonneg hδ.le _) (ne_of_gt hP)).mp
  rw [hroot]
  exact hpower
