import Submission.Obl.k4_horizontal_strict_parameter_step.Interface

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

namespace LayerAt

/-- Enlarging the loss leaves every original assignment and its law intact. -/
theorem mono_loss {N : ℕ → ℝ} {d e₀ : ℝ} {α : Type} [MeasurableSpace α]
    {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ} {k : ℕ} {ε δ D a : ℝ}
    {ρH : Measure (α × ℝ)} {n : ℕ} {A : Fin n → Set α}
    {q : Fin n → Fin 3 → ℤ} {h : Fin n → Fin 6 → ℝ}
    (H : LayerAt N d e₀ π b k ε ρH D a n A q h)
    (hN : 1 ≤ N k) (ha : 0 ≤ a) (hεδ : ε ≤ δ) :
    LayerAt N d e₀ π b k δ ρH D a n A q h := by
  have hNp : 0 < N k := zero_lt_one.trans_le hN
  have hpow : N k ^ ε ≤ N k ^ δ := Real.rpow_le_rpow_of_exponent_le hN hεδ
  refine ⟨H.1, H.2.1, ?_, H.2.2.2⟩
  intro i
  obtain ⟨hg, hn, hf, hm⟩ := H.2.2.1 i
  refine ⟨hg, fun t ht p hp z hz => (hn t ht p hp z hz).trans hpow,
    fun l hl t ht => (hf l hl t ht).trans (mul_le_mul_of_nonneg_right hpow ha), ?_⟩
  apply le_trans _ hm
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg D) (Real.rpow_nonneg ha _))
    (Real.rpow_pos_of_pos hNp ε) hpow

end LayerAt

end Submission.Obl.k4_horizontal_strict_parameter_step
