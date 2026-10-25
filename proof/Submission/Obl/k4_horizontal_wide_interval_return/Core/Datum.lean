import Submission.Obl.k4_horizontal_wide_interval_return.Core.Basics

/-!
# The three-layer datum of o250, unpacked

`LayerDatum cfg k ε R χ D depth` records the projected layers at one index `k` exactly as the
frozen premise states them (field `piece` is the frozen conjunction verbatim), and
`projected_unpack` extracts the buffered depths and an eventual family of such data.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open MeasureTheory Set Filter

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The three-layer datum at one index. -/
structure LayerDatum (cfg : Data α) (k : ℕ) (ε R χ D : ℝ) (depth : Fin 3 → ℝ) where
  ρs : Measure (α × ℝ)
  np : Fin 3 → ℕ
  C : (h : Fin 3) → Fin (np h) → Set α
  qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ
  G : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ
  le_rho : ρs ≤ cfg.ρ k
  mass : ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ ρs univ
  cover : ∀ᵐ p ∂ρs, ∀ h : Fin 3, ∃ i, p.1 ∈ C h i
  meas : ∀ h i, MeasurableSet (C h i)
  disj : ∀ h i i', i ≠ i' → Disjoint (C h i) (C h i')
  piece : ∀ h i, (∀ l ∈ C h i, ⌊cfg.b k l 3 / χ⌋ = qp h i 0 ∧ ⌊cfg.b k l 0 / χ⌋ = qp h i 1 ∧ ⌊cfg.b k l 1 / D⌋ = qp h i 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε)) ∧ |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| + |(qp h i 2 : ℝ) * D| ≤ cfg.N k ^ ε ∧ (G h i).totalDegree ≤ 2 ∧ (∀ e, |(G h i).coeff e| ≤ cfg.N k ^ R) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w] (G h i)| ≤ cfg.N k ^ ε) ∧ (∀ l ∈ C h i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(cfg.x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤ cfg.N k ^ ε * D ∧ |(cfg.x k l t) 3 - MvPolynomial.eval ![t, (cfg.x k l t) 2] (G h i)| ≤ cfg.N k ^ ε * cfg.N k ^ (-depth h)) ∧ ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) * cfg.π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤ cfg.ρ k (C h i ×ˢ Set.Icc (0 : ℝ) 1)
  sum : (∀ h, (∑ i : Fin (np h), ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) * cfg.π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (cfg.N k ^ ε))

/-- The buffered exponents of the datum. -/
structure Depths (cfg : Data α) (buffer s₀ s u v R M : ℝ) : Prop where
  s₀_pos : 0 < s₀
  buf_U : buffer * s₀ < cfg.U
  buf_e : buffer * s₀ < cfg.e₀
  s₀_lt : s₀ < s
  u_pos : 0 < u
  v_pos : 0 < v
  v_lt_u : v < u
  v_small : v < (1 - cfg.d) * u / 4
  su_U : s + u < cfg.U
  su_lt : s + u < 3 * s₀ / 2
  wide_D : (10 / (1 - cfg.d) + 3) * u < 2 * cfg.κ * (s - s₀)
  wide_h : (10 / (1 - cfg.d) + 3) * u < cfg.κ * s
  R_gt : 1 < R
  M_gt : buffer * s₀ < M
  M_U : buffer * M < cfg.U
  M_e : buffer * M < cfg.e₀

theorem projected_unpack {cfg : Data α} (hp : cfg.Projected) {buffer : ℝ} (hbuf : 100 < buffer) :
    ∃ s₀ s u v R M : ℝ, Depths cfg buffer s₀ s u v R M ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, Nonempty (LayerDatum cfg k ε R (cfg.N k ^ (-M))
        (cfg.N k ^ (-2 * cfg.κ * s₀)) ![s, s + u, s + v]) := by
  obtain ⟨s₀, s, u, v, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, M, h14, h15,
    h16, hmain⟩ := hp buffer hbuf
  refine ⟨s₀, s, u, v, R, M, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16⟩, fun ε hε => ?_⟩
  filter_upwards [hmain ε hε] with k hk
  obtain ⟨ρs, np, C, qp, G, hle, hmass, hcover, hmeas, hdisj, hpiece, hsum⟩ := hk
  exact ⟨⟨ρs, np, C, qp, G, hle, hmass, hcover, hmeas, hdisj, hpiece, hsum⟩⟩

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
