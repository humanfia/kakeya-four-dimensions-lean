-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Regularization.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.FirstJetStatement

namespace Submission.Obl.k4_fixed_prior_chart_regularization

open MeasureTheory

noncomputable section

/-- The two estimates obtained from the raw geometry, after density cutoff and
line/time-bin duration preparation. The trajectory prior is fixed throughout.
All later label selections restrict `E` and preserve these upper bounds. -/
structure UnregularizedChart {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ)
    (d K ζ : ℝ) : Prop where
  measurable_y : Measurable y
  measurable_β : Measurable β
  measurable_γ : Measurable γ
  measurable_F : Measurable F
  measurableSet_E : MeasurableSet E
  subset_E : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1
  bound_y : ∀ l i, |y l i| ≤ K
  bound_β : ∀ l, |β l| ≤ K
  bound_γ : ∀ l, |γ l| ≤ K
  bound_F : ∀ t i, |F t i| ≤ K
  mass : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E
  mixedCap : ∀ t r w : ℝ, ζ ≤ r → r ≤ 1 → ζ ≤ w → w ≤ 1 →
    ∀ (z : Fin 2 → ℤ) (j : ℤ),
    ν {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / w⌋ = j ∧
      ⌊y l 0 / r⌋ = z 0 ∧ ⌊y l 1 / r⌋ = z 1} ≤ ENNReal.ofReal (K * r ^ 2 * w ^ d)
  support : ∀ t w : ℝ, ζ ≤ w → w ≤ 1 →
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ K * w ^ (-d) ∧
      ∀ l, (l, t) ∈ E → ⌊FirstJet.scal y β γ F l t / w⌋ ∈ C

/-- Pure chart regularization: absolute mixed caps and a global scalar support
count give local counts, row and slope comparisons, and relative dyadic coefficient-bin
caps after a dense label restriction. The original probability measure `ν` is unchanged. -/
def ChartRegularization : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        UnregularizedChart ν y β γ E F d (N ^ η) (N ^ (-c)) →
        ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧
          FirstJet.Data ν y β γ E' F d (N ^ ε) (N ^ (-c))

/-- Both geometric upper estimates pass to an arbitrary measurable sublabel set. -/
theorem UnregularizedChart.restrict_labels {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E E' : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : UnregularizedChart ν y β γ E F d K ζ) (hE' : MeasurableSet E')
    (hsub : E' ⊆ E) (hmass : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E') :
    UnregularizedChart ν y β γ E' F d K ζ := by
  refine { h with
    measurableSet_E := hE'
    subset_E := hsub.trans h.subset_E
    mass := hmass
    mixedCap := ?_
    support := ?_ }
  · intro t r w hr hr1 hw hw1 z j
    apply le_trans (measure_mono ?_) (h.mixedCap t r w hr hr1 hw hw1 z j)
    rintro l ⟨hl, hx, hy0, hy1⟩
    exact ⟨hsub hl, hx, hy0, hy1⟩
  · intro t w hw hw1
    obtain ⟨C, hC, hcover⟩ := h.support t w hw hw1
    exact ⟨C, hC, fun l hl => hcover l (hsub hl)⟩

/-- A smaller raw hypothesis loss also meets every larger positive bound. -/
theorem UnregularizedChart.mono_bound {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K H ζ : ℝ}
    (h : UnregularizedChart ν y β γ E F d K ζ) (hK : 0 < K) (hKH : K ≤ H)
    (hζ : 0 ≤ ζ) : UnregularizedChart ν y β γ E F d H ζ := by
  refine { h with
    bound_y := fun l i => (h.bound_y l i).trans hKH
    bound_β := fun l => (h.bound_β l).trans hKH
    bound_γ := fun l => (h.bound_γ l).trans hKH
    bound_F := fun t i => (h.bound_F t i).trans hKH
    mass := (ENNReal.ofReal_le_ofReal (inv_anti₀ hK hKH)).trans h.mass
    mixedCap := ?_
    support := ?_ }
  · intro t r w hr hr1 hw hw1 z j
    apply (h.mixedCap t r w hr hr1 hw hw1 z j).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKH (sq_nonneg _)) (Real.rpow_nonneg (hζ.trans hw) _)
  · intro t w hw hw1
    obtain ⟨C, hC, hcover⟩ := h.support t w hw hw1
    exact ⟨C, hC.trans (mul_le_mul_of_nonneg_right hKH (Real.rpow_nonneg (hζ.trans hw) _)), hcover⟩


end
end Submission.Obl.k4_fixed_prior_chart_regularization
