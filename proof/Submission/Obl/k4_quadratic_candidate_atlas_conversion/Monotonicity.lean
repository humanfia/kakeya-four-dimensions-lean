import Submission.Obl.k4_quadratic_candidate_atlas_conversion.Certificates
import Submission.Obl.k4_quadratic_candidate_atlas_conversion.Width

set_option linter.unusedVariables false

namespace Submission.Obl.k4_quadratic_candidate_atlas_conversion

/-- Enlarging the numerical and degree bounds preserves a Boolean format. -/
theorem fmt_mono {n D D' : ℕ} {H H' : ℝ} {A : Set (Fin n → ℝ)}
    (hH : H ≤ H') (hD : D ≤ D') (h : fmt n H D A) : fmt n H' D' A := by
  rcases h with ⟨q, hq, p, hp, b, hb⟩
  exact ⟨q, hq.trans hH, p, fun a => (hp a).trans hD, b, hb⟩

/-- A chart tolerates a larger format bound and a larger positive spatial slack. -/
theorem chart_mono
    {Nk : ℝ} {M M' D D' T : ℕ} {κ κ' j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (hN : 1 ≤ Nk) (hM : M ≤ M') (hD : D ≤ D')
    (hκ : 0 < κ) (hκ' : κ ≤ κ')
    (h : chart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    chart Nk M' D' κ' T j r Bv Ev c u Q R A F ex := by
  have hbound : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hN hM
  have hδ : 0 < δ Nk r := by unfold δ; positivity
  rcases h with ⟨hdet, hcu, hQ, hsize, hdeg, hcoeff, hAm, hFm, hfmt,
    hwhole, hinc, hex⟩
  refine ⟨hdet, hcu.trans hbound, hQ.trans hbound,
    hsize.trans (div_le_div_of_nonneg_right hκ' (by positivity)), hdeg,
    fun e => (hcoeff e).trans hbound, hAm, hFm, ?_, ?_, ?_, hex⟩
  · intro i
    exact ⟨fmt_mono hbound hD (hfmt i).1, fmt_mono hbound hD (hfmt i).2⟩
  · intro l hl
    rcases hwhole l hl with ⟨hcopy, hcoords, ht⟩
    refine ⟨hcopy.trans hbound, fun e => (hcoords e).trans hbound, ?_⟩
    intro t ht'
    rcases ht t ht' with ⟨hy, hv, hd, hc⟩
    have hB : 0 ≤ Bv := by
      have hz : 0 ≤ κ * Bv := (abs_nonneg _).trans hd
      exact nonneg_of_mul_nonneg_right hz hκ
    refine ⟨hy.trans hκ', hv.trans (mul_le_mul_of_nonneg_right hκ' hδ.le),
      hd.trans (mul_le_mul_of_nonneg_right hκ' hB), ?_⟩
    exact hc.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hκ' (sq_nonneg Bv)) hδ.le)
  · intro p hp
    rcases hinc p hp with ⟨hE, hA, ht, hd⟩
    have hB : 0 ≤ Bv := by
      have hwhole' := (hwhole p.1 hA).2.2 p.2 ht
      have hz : 0 ≤ κ * Bv := (abs_nonneg _).trans hwhole'.2.2.1
      exact nonneg_of_mul_nonneg_right hz hκ
    exact ⟨hE, hA, ht, (div_le_div_of_nonneg_left hB hκ hκ').trans hd⟩

/-- Only the allowed upper bound on kappa depends on the path exponent. -/
theorem path_mono_exponent
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ σ' : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {κ : ℝ} {C : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
    {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}
    (hN : 1 ≤ Nk) (hσ : σ ≤ σ')
    (h : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst) :
    path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ' r T nw κ C lev par γ j c u Q R A F lst := by
  exact ⟨h.1, h.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN hσ), h.2.2⟩

/-- Enlarge count and format bounds and the requested list/mass slack. -/
theorem improvementAt_mono
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {κ₁ Δ : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {M D M' D' : ℕ} {ε τ : ℝ}
    (hN : 1 ≤ Nk) (hM : M ≤ M') (hD : D ≤ D') (hε : ε ≤ τ)
    (h : ImprovementAt Nk L W ω ν E B κ₁ Δ m r T nw M D ε) :
    ImprovementAt Nk L W ω ν E B κ₁ Δ m r T nw M' D' τ := by
  rcases h with ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hroom, htime, hcount, hdisj, hlist, hchart, hmass⟩
  have hslack := Real.rpow_le_rpow_of_exponent_le hN hε
  refine ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hroom, htime, hcount.trans (pow_le_pow_right₀ hN hM), hdisj,
    fun w o => (hlist w o).trans hslack, ?_, ?_⟩
  · intro b
    exact chart_mono hN hM hD (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _) hslack (hchart b)
  · exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hε))).trans hmass

end Submission.Obl.k4_quadratic_candidate_atlas_conversion
