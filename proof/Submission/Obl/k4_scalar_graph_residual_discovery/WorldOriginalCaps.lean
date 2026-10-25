/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldOriginalCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldNormalFromCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open WangZahlLot.Obl.wz_slab_local_linearity

namespace Zoom

/-- Original spatial caps and full-prior floors on the global event.
Active fine pieces are tested in the specified coarse coefficient world,
before any subsequent whole-state restriction. -/
structure OriginalWorldCaps (θ : Measure ScalarLine) (R : Set ScalarIncidence)
    (ρ ζ d : ℝ) (q : Fin 5 → ℤ) where
  H : ℝ
  A : ℝ
  η : ℝ
  H_pos : 0 < H
  one_le_A : 1 ≤ A
  eta_pos : 0 < η
  β : ℝ → ℝ
  beta_bounds : ∀ r, ζ ≤ r → r ≤ 1 →
    0 < β r ∧ β r ≤ ρ * r ∧ ρ * r ≤ A * β r
  π₀ : ℝ≥0∞
  coarse_floor : ENNReal.ofReal (ρ ^ (1 + d) / H) * π₀ ≤ θ {l | cell ρ l.2 = q}
  coarse_cap : ∀ (t a : ℝ), ζ ≤ a → a ≤ 1 → ∀ z,
    θ {l | (l, t) ∈ R ∧ cell ρ l.2 = q ∧ cell (β a) (spatial l t) = z} ≤
      ENNReal.ofReal (H * (β a) ^ (1 + d)) * π₀
  π : ℝ → (Fin 5 → ℤ) → ℝ≥0∞
  fine_floor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ b,
    (∃ p ∈ R, cell ρ p.1.2 = q ∧ cell (β r) p.1.2 = b) →
    ENNReal.ofReal ((β r) ^ (1 + d) / H) * π r b ≤ θ {l | cell (β r) l.2 = b}
  intersection_floor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ b,
    (∃ p ∈ R, cell ρ p.1.2 = q ∧ cell (β r) p.1.2 = b) →
    ENNReal.ofReal η * θ {l | cell (β r) l.2 = b} ≤
      θ {l | cell (β r) l.2 = b ∧ cell ρ l.2 = q}
  fine_cap : ∀ r, ζ ≤ r → r ≤ 1 → ∀ b,
    (∃ p ∈ R, cell ρ p.1.2 = q ∧ cell (β r) p.1.2 = b) →
    ∀ (t a : ℝ), ζ ≤ a → a ≤ r → ∀ z,
    θ {l | (l, t) ∈ R ∧ cell (β r) l.2 = b ∧ cell (β a) (spatial l t) = z} ≤
      ENNReal.ofReal (H * (β a) ^ (1 + d)) * π r b

noncomputable section

/-- The original cap certificate survives every later measurable subset
of the coefficient world. Floors refer to the unchanged full priors, so
there is no request to restore incidence floors after residual selection. -/
theorem OriginalWorldCaps.normal_on_subset
    {θ : Measure ScalarLine} [IsFiniteMeasure θ] {R : Set ScalarIncidence}
    {ρ ζ d : ℝ} {q : Fin 5 → ℤ} (caps : OriginalWorldCaps θ R ρ ζ d q)
    (μ : Measure ScalarIncidence) {E : Set ScalarIncidence}
    (hE : MeasurableSet E) (hsub : E ⊆ R ∩ {p | cell ρ p.1.2 = q})
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    {K U δ : ℝ} (hK : 1 ≤ K) (hU : 0 < U) (hδ : 0 < δ)
    (hbudget : U / δ ≤ K)
    (hACbudget : 9 * caps.H ^ 2 * caps.A ^ 4 ≤ K)
    (hBCbudget : 9 * caps.H ^ 2 * caps.A ^ 4 / caps.η ≤ K)
    (hμ : μ ≤ ENNReal.ofReal U • θ.prod volume)
    (hpositive : θ {l | cell ρ l.2 = q} ≠ 0)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal δ * θ {l | cell ρ l.2 = q} ≤ μ E)
    (F : ℝ → ℝ) (hF : Measurable F) (hbound : ∀ p ∈ E, |F p.2| ≤ K)
    (hsupport : ∀ t, IntervalAD ζ d K
      {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ scalar ρ q F l t = s})
    (hrow : ∀ p ∈ E, ∀ p' ∈ E, |F p.2 - F p'.2| ≤ K * (|p.2 - p'.2| + ζ))
    (hresidual : ∀ p ∈ E, ∀ p' ∈ E,
      |residual ρ q F p.1 p.2 - residual ρ q F p'.1 p'.2| ≤
        K * (‖position ρ q p - position ρ q p'‖ + ζ)) :
    Jets.ScalarNormal (prior θ ρ q) (coeff ρ q) E F
      (fun r l => cell (caps.β r) l.2) K ζ d := by
  refine scalarNormal_of_original_caps θ μ hρ hζ hζ₁ hd hd₁ hK hU hδ hbudget
    caps.H_pos caps.one_le_A caps.eta_pos hACbudget hBCbudget hμ q hpositive E hE
    (fun p hp => (hsub hp).2) htime hmass F hF hbound caps.β caps.beta_bounds hsupport
    caps.π₀ caps.coarse_floor ?_ caps.π ?_ ?_ ?_ hrow hresidual
  · intro t a ha ha₁ z
    apply (measure_mono ?_).trans (caps.coarse_cap t a ha ha₁ z)
    intro l hl
    exact ⟨(hsub hl.1).1, hl.2⟩
  · intro r hr hr₁ b hactive
    apply caps.fine_floor r hr hr₁ b
    obtain ⟨p, hp, hb⟩ := hactive
    exact ⟨p, (hsub hp).1, (hsub hp).2, hb⟩
  · intro r hr hr₁ b hactive
    apply caps.intersection_floor r hr hr₁ b
    obtain ⟨p, hp, hb⟩ := hactive
    exact ⟨p, (hsub hp).1, (hsub hp).2, hb⟩
  · intro r hr hr₁ b hactive t a ha har z
    have hactive' : ∃ p ∈ R, cell ρ p.1.2 = q ∧ cell (caps.β r) p.1.2 = b := by
      obtain ⟨p, hp, hb⟩ := hactive
      exact ⟨p, (hsub hp).1, (hsub hp).2, hb⟩
    apply (measure_mono ?_).trans (caps.fine_cap r hr hr₁ b hactive' t a ha har z)
    intro l hl
    exact ⟨(hsub hl.1).1, hl.2⟩

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
