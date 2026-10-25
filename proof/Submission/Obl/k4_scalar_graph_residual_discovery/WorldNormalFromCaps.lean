/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldNormalFromCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldNormal
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open WangZahlLot.Obl.wz_slab_local_linearity

namespace Zoom

/-- The spatial cap fields of the higher-jet input follow from ORIGINAL
palette caps, original coefficient-bin floors, and retained intersections.
Only pieces participating in the final world need floors; every other
piece has an empty labelled section. In particular this does not assert
that arbitrary real-width bins have a new lower floor. -/
theorem scalarNormal_of_original_caps
    (θ : Measure ScalarLine) [IsFiniteMeasure θ] (μ : Measure ScalarIncidence)
    {ρ ζ d K H δ Hc A η : ℝ}
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hK : 1 ≤ K) (hH : 0 < H) (hδ : 0 < δ) (hbudget : H / δ ≤ K)
    (hHc : 0 < Hc) (hA : 1 ≤ A) (hη : 0 < η)
    (hACbudget : 9 * Hc ^ 2 * A ^ 4 ≤ K)
    (hBCbudget : 9 * Hc ^ 2 * A ^ 4 / η ≤ K)
    (hμ : μ ≤ ENNReal.ofReal H • θ.prod volume)
    (q : Fin 5 → ℤ) (hpositive : θ {l | cell ρ l.2 = q} ≠ 0)
    (E : Set ScalarIncidence) (hE : MeasurableSet E)
    (hworld : ∀ p ∈ E, cell ρ p.1.2 = q)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal δ * θ {l | cell ρ l.2 = q} ≤ μ E)
    (F : ℝ → ℝ) (hF : Measurable F) (hbound : ∀ p ∈ E, |F p.2| ≤ K)
    (β : ℝ → ℝ)
    (hβ : ∀ r, ζ ≤ r → r ≤ 1 →
      0 < β r ∧ β r ≤ ρ * r ∧ ρ * r ≤ A * β r)
    (hsupport : ∀ t, IntervalAD ζ d K
      {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ scalar ρ q F l t = s})
    (π₀ : ℝ≥0∞)
    (hcoarseFloor : ENNReal.ofReal (ρ ^ (1 + d) / Hc) * π₀ ≤
      θ {l | cell ρ l.2 = q})
    (hcoarseCap : ∀ (t a : ℝ), ζ ≤ a → a ≤ 1 → ∀ z,
      θ {l | (l, t) ∈ E ∧ cell ρ l.2 = q ∧ cell (β a) (spatial l t) = z} ≤
        ENNReal.ofReal (Hc * (β a) ^ (1 + d)) * π₀)
    (π : ℝ → (Fin 5 → ℤ) → ℝ≥0∞)
    (hfineFloor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ b,
      (∃ p ∈ E, cell (β r) p.1.2 = b) →
      ENNReal.ofReal ((β r) ^ (1 + d) / Hc) * π r b ≤
        θ {l | cell (β r) l.2 = b})
    (hintersection : ∀ r, ζ ≤ r → r ≤ 1 → ∀ b,
      (∃ p ∈ E, cell (β r) p.1.2 = b) →
      ENNReal.ofReal η * θ {l | cell (β r) l.2 = b} ≤
        θ {l | cell (β r) l.2 = b ∧ cell ρ l.2 = q})
    (hfineCap : ∀ r, ζ ≤ r → r ≤ 1 → ∀ b,
      (∃ p ∈ E, cell (β r) p.1.2 = b) →
      ∀ (t a : ℝ), ζ ≤ a → a ≤ r → ∀ z,
      θ {l | (l, t) ∈ E ∧ cell (β r) l.2 = b ∧ cell (β a) (spatial l t) = z} ≤
        ENNReal.ofReal (Hc * (β a) ^ (1 + d)) * π r b)
    (hrow : ∀ p ∈ E, ∀ p' ∈ E,
      |F p.2 - F p'.2| ≤ K * (|p.2 - p'.2| + ζ))
    (hresidual : ∀ p ∈ E, ∀ p' ∈ E,
      |residual ρ q F p.1 p.2 - residual ρ q F p'.1 p'.2| ≤
        K * (‖position ρ q p - position ρ q p'‖ + ζ)) :
    Jets.ScalarNormal (prior θ ρ q) (coeff ρ q) E F
      (fun r l => cell (β r) l.2) K ζ d := by
  apply scalarNormal_of_world_estimates θ μ hρ hζ hζ₁ hK hH hδ hbudget hμ q
    hpositive E hE hworld htime hmass F hF hbound β
    (fun r hr hr₁ => ⟨(hβ r hr hr₁).1, (hβ r hr hr₁).2.1⟩) hsupport
  · intro t v a ha ha₁
    have hapos : 0 < a := hζ.trans_le ha
    have hraw := interpolated_absolute_spatial_cap θ E t hρ (hβ a ha ha₁).1 hapos
      hHc hA hd hd₁ (hβ a ha ha₁).2.1 (hβ a ha ha₁).2.2 q hpositive hworld π₀
      (hcoarseCap t a ha ha₁) hcoarseFloor v
    exact hraw.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hACbudget (Real.rpow_nonneg hapos.le _)))
  · exact hrow
  · exact hresidual
  · intro r hr hr₁ b t v a ha har
    by_cases hactive : ∃ p ∈ E, cell (β r) p.1.2 = b
    · have hapos : 0 < a := hζ.trans_le ha
      have ha₁ : a ≤ 1 := har.trans hr₁
      have hrpos : 0 < r := hζ.trans_le hr
      have hraw := interpolated_piece_spatial_cap θ E t hρ (hβ r hr hr₁).1
        (hβ a ha ha₁).1 hrpos hapos hHc hA hη hd hd₁
        (hβ a ha ha₁).2.1 (hβ a ha ha₁).2.2 (hβ r hr hr₁).2.2 q b (π r b)
        (hfineCap r hr hr₁ b hactive t a ha har)
        (hfineFloor r hr hr₁ b hactive) (hintersection r hr hr₁ b hactive) v
      exact hraw.trans (mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hBCbudget
          (Real.rpow_nonneg (div_nonneg hapos.le hrpos.le) _))) zero_le)
    · have hempty : {l : ScalarLine | cell (β r) l.2 = b ∧ (l, t) ∈ E ∧
          ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact hactive ⟨(l, t), hl.2.1, hl.1⟩
      rw [hempty, measure_empty]
      exact bot_le

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
