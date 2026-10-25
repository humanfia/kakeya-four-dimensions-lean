import Submission.Obl.k4_profile_endpoint_crop.Interface

namespace Submission.Obl.k4_profile_endpoint_crop

lemma finiteSource_of_single {N K : ℕ → ℝ}
    {ν : ℕ → MeasureTheory.Measure Line} {E : ℕ → Set Inc}
    (h : SingleFormat N K ν E) : FiniteSource ν E := by
  obtain ⟨M, D, h⟩ := h
  intro k
  exact ⟨(h k).1, (h k).2.2.1, (h k).2.2.2.1⟩

def AngularCap (N : ℕ → ℝ) (L : ℝ) (f : ℝ → ℝ) (S η : ℝ)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc)
    (G : (k : ℕ) → Fin (W k) → ℝ → Joint → ENNReal) : Prop :=
  ∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) *
      (Selected (ν k γ) (E k γ))
        {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) <
          G k γ u (JointObs N k L u p)}) ≤ ENNReal.ofReal (N k ^ (-c))

lemma angular_cap_of_typical
    {N : ℕ → ℝ} {F : ℝ → ℝ → ℝ} {L u₀ β S η : ℝ}
    {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line}
    {E : (k : ℕ) → Fin (W k) → Set Inc}
    {G : (k : ℕ) → Fin (W k) → ℝ → Joint → ENNReal}
    (hN : ∀ k, 2 ≤ N k) (hroom : u₀ + η * L < 4)
    (hgrowth : ∀ v : ℝ, 0 ≤ v → v ≤ η * L →
      S * v ≤ F L (u₀ + v) - F L u₀)
    (htyp : AngularTypical N L (fun u => F L (u₀ + u) + 2 * u₀ - β)
      u₀ W ω ν E G) :
    AngularCap N L (fun r => F r u₀ + 2 * u₀ - β) S η W ω ν E G := by
  intro u τ hu huη hτ
  obtain ⟨c, hc, he⟩ := htyp u τ hu (by linarith) hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [he] with k hk
  apply le_trans (Finset.sum_le_sum fun γ _ => ?_) hk
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply MeasureTheory.measure_mono
  intro p hp
  apply Or.inr
  have hg := hgrowth u hu.le huη
  have hpow : ENNReal.ofReal (N k ^ (-(F L (u₀ + u) + 2 * u₀ - β) + τ)) ≤
      ENNReal.ofReal (N k ^ (-(F L u₀ + 2 * u₀ - β) - S * u + τ)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hN k])
    linarith
  exact lt_of_le_of_lt hpow hp

end Submission.Obl.k4_profile_endpoint_crop
