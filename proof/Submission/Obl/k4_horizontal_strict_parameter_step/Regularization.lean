import Submission.Obl.k4_horizontal_strict_parameter_step.FirstJet.Statement
import Submission.Obl.k4_fixed_prior_chart_regularization.Regularization

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Regularization.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory

noncomputable section

/-- The two estimates obtained from the raw geometry, after density cutoff and
line/time-bin duration preparation. The trajectory prior is fixed throughout.
All later label selections restrict `E` and preserve these upper bounds. -/
abbrev UnregularizedChart {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ)
    (d K ζ : ℝ) : Prop :=
  Submission.Obl.k4_fixed_prior_chart_regularization.UnregularizedChart ν y β γ E F d K ζ

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
  exact Submission.Obl.k4_fixed_prior_chart_regularization.UnregularizedChart.restrict_labels
    h hE' hsub hmass

/-- A smaller raw hypothesis loss also meets every larger positive bound. -/
theorem UnregularizedChart.mono_bound {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K H ζ : ℝ}
    (h : UnregularizedChart ν y β γ E F d K ζ) (hK : 0 < K) (hKH : K ≤ H)
    (hζ : 0 ≤ ζ) : UnregularizedChart ν y β γ E F d H ζ := by
  exact Submission.Obl.k4_fixed_prior_chart_regularization.UnregularizedChart.mono_bound
    h hK hKH hζ

/-- The first-jet conclusion only becomes stronger when more original incidences
are counted; the selected trajectories and menu are unchanged. -/
theorem FirstJet.Cover.mono_labels {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E E' : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d N ε w : ℝ} (hsub : E' ⊆ E)
    (h : FirstJet.Cover ν y β γ E' F d N ε w) :
    FirstJet.Cover ν y β γ E F d N ε w := by
  obtain ⟨t, ht, A, hA, L, hL, hmass, P, hcard, hcover⟩ := h
  refine ⟨t, ht, A, hA, L, hL, hmass.trans (measure_mono ?_), P, hcard, hcover⟩
  exact Set.inter_subset_inter_left _ hsub

/-- The single analytic chart input needed by the raw geometric bootstrap. -/
def RawFirstJetCover : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        UnregularizedChart ν y β γ E F d (N ^ η) ((N ^ (-c)) ^ (1000 / (1 - d))) →
        FirstJet.Cover ν y β γ E F d N ε (N ^ (-c))

/-- Chart regularization and the normalized first jet compose without changing
or renormalizing the original probability measure. -/
theorem raw_firstJet_of_regularization (hreg : ChartRegularization)
    (hjet : FirstJet.FirstJetCover) : RawFirstJetCover := by
  intro d hd hd1 c hc ε hε
  obtain ⟨ηj, hηj, Nj, hNj, hjet⟩ := hjet d hd hd1 c hc ε hε
  let c₀ := c * (1000 / (1 - d))
  have hc₀ : 0 < c₀ := mul_pos hc (div_pos (by norm_num) (by linarith))
  obtain ⟨η, hη, -, Nr, hNr, hreg⟩ := hreg d hd hd1 c₀ hc₀ ηj hηj
  refine ⟨η, hη, max Nj Nr, hNj.trans (le_max_left _ _), ?_⟩
  intro N hN Ω _ ν hν y β γ E F hdata
  have hNp : 0 < N := lt_of_lt_of_le (by linarith : 0 < Nj)
    ((le_max_left _ _).trans hN)
  have hζ : (N ^ (-c)) ^ (1000 / (1 - d)) = N ^ (-c₀) := by
    rw [← Real.rpow_mul hNp.le]
    congr 1
    dsimp [c₀]
    ring
  rw [hζ] at hdata
  obtain ⟨E', hsub, hprepared⟩ := hreg N ((le_max_right _ _).trans hN)
    Ω ν hν y β γ E F hdata
  rw [← hζ] at hprepared
  exact FirstJet.Cover.mono_labels hsub
    (hjet N ((le_max_left _ _).trans hN) Ω ν hν y β γ E' F hprepared)

end

end Submission.Obl.k4_horizontal_strict_parameter_step
