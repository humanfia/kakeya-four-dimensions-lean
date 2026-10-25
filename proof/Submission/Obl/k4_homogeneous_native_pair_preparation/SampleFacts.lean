import Submission.Obl.k4_homogeneous_native_pair_preparation.Sequence
import Submission.Obl.k4_homogeneous_native_pair_preparation.HalfOpen

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set

/-- Enlarging the slack preserves the native mask and all its density caps. -/
theorem GoodAt.mono_slack {N K κ : ℝ} {W : ℕ}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : Fin W → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a u : ℝ} {depths : Finset ℝ}
    {Good : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hGood : GoodAt N K W E P B f g G L S a u depths Good)
    (hK : 0 < K) (hKκ : K ≤ κ) (hB : ∀ γ, 0 ≤ B γ) :
    GoodAt N κ W E P B f g G L S a u depths Good := by
  intro γ
  refine ⟨(hGood γ).1, (hGood γ).2.1, ?_⟩
  intro p hp
  obtain ⟨hy, hv, hd, hg, hG⟩ := (hGood γ).2.2 p hp
  exact ⟨hy.trans hKκ, hv.trans hKκ,
    (div_le_div_of_nonneg_left (hB γ) hK hKκ).trans hd, hg, hG⟩

/-- A true old chart remains true after endpoint trimming and slack enlargement;
the old observer knowledge is inherited on the retained incidence set. -/
theorem true_chart_halfOpen_mono {N κ₀ κ j r B q : ℝ} {M₀ D₀ M D T : ℕ}
    {E F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    (ν : Measure (ℕ × (Fin 6 → ℝ)))
    (knowledge : ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop)
    (hN : 2 ≤ N) (hκ₀ : 0 < κ₀) (hκ : κ₀ ≤ κ) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hM : M₀ + 1 ≤ M) (hD : max D₀ 1 ≤ D)
    (hc : chart N M₀ D₀ κ₀ T j r B E c u Q R A F
      (ENNReal.ofReal (q / ((2 : ℝ) ^ T * κ₀)) ≤ (ν.prod volume) F ∧
        ∀ p ∈ F, knowledge p)) :
    chart N M D κ T j r B E c u Q R A
      (F ∩ {p | p.2 < (j + 1) / (2 : ℝ) ^ T})
      (ENNReal.ofReal (q / ((2 : ℝ) ^ T * κ)) ≤
          (ν.prod volume) (F ∩ {p | p.2 < (j + 1) / (2 : ℝ) ^ T}) ∧
        ∀ p ∈ F ∩ {p | p.2 < (j + 1) / (2 : ℝ) ^ T}, knowledge p) := by
  apply Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
    (one_le_two.trans hN) hM hD hκ₀ hκ hB (chart_halfOpen hN hκ₀ hB hc)
  rintro ⟨hfloor, hkn⟩
  refine ⟨?_, fun p hp => hkn p hp.1⟩
  rw [chart_halfOpen_mass hc ν]
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hfloor
  exact div_le_div_of_nonneg_left hq (by positivity)
    (mul_le_mul_of_nonneg_left hκ (by positivity))

end Submission.Obl.k4_homogeneous_native_pair_preparation
