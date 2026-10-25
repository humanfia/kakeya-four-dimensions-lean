import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Statement

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

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

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
