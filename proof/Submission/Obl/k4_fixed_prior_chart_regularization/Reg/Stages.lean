-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Reg/Stages.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.Regularization

/-!
# Chart regularization in four restriction stages

Paper §9 ("Regularizing the scalar-normal input", proof of `prop:bootstrap`) prepares the
hypotheses of the first jet (`FirstJet.Data`) from the unregularized chart (absolute mixed caps
and a global scalar support count) by successive label restrictions under the fixed prior `ν`:

* `StageLocal`: local scalar counts (`LocalCounts`, the `support` field of `Data`);
* `StageRow`: the row comparison (`RowComparison`, the `rowLip` field);
* `StageSlope`: the slope comparison (`SlopeComparison`, the `slopeLip` field);
* `StageBin`: the relative dyadic coefficient-bin caps (`BinCaps`, the `binCap` field).

The absolute cap of `Data` is the mixed cap at equal widths (`absCap_of_mixedCap`). Every
property is downward closed under label restriction and monotone in the constant, so the four
stages compose (`chartRegularization_of_stages`).
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.Reg

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Local scalar counts (the `support` field of `FirstJet.Data`). -/
def LocalCounts (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ)
    (d K ζ : ℝ) : Prop :=
  ∀ t q r a : ℝ, ζ ≤ q → q ≤ r → r ≤ 1 →
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ K * (r / q) ^ d ∧
      ∀ l, (l, t) ∈ E → a ≤ FirstJet.scal y β γ F l t → FirstJet.scal y β γ F l t ≤ a + r →
        ⌊FirstJet.scal y β γ F l t / q⌋ ∈ C

/-- The row comparison (the `rowLip` field of `FirstJet.Data`). -/
def RowComparison (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (K ζ : ℝ) : Prop :=
  ∀ t u : ℝ, (∃ l, (l, t) ∈ E) → (∃ l, (l, u) ∈ E) → ∀ i,
    |F t i - F u i| ≤ K * (|t - u| + ζ)

/-- The slope comparison (the `slopeLip` field of `FirstJet.Data`). -/
def SlopeComparison (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (K ζ : ℝ) : Prop :=
  ∀ l l' t u, (l, t) ∈ E → (l', u) ∈ E →
    |γ l - γ l'| ≤ K * (|t - u| + |FirstJet.xbar β γ l t - FirstJet.xbar β γ l' u| +
      |y l 0 - y l' 0| + |y l 1 - y l' 1| + ζ)

/-- The relative dyadic coefficient-bin caps (the `binCap` field of `FirstJet.Data`). -/
def BinCaps (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (d K ζ : ℝ) : Prop :=
  ∀ (q : ℝ) (n : ℕ), ζ ≤ q → q ≤ (2 : ℝ) ^ (-(n : ℤ)) → ∀ (b : Fin 4 → ℤ) (t : ℝ)
    (z : Fin 3 → ℤ),
    ν {l | (⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
        ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3) ∧
        (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧
        ⌊y l 1 / q⌋ = z 2} ≤
      ENNReal.ofReal (K * (q / (2 : ℝ) ^ (-(n : ℤ))) ^ (2 + d)) *
        ν {l | ⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
          ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3}

/-! ### Monotonicity -/

theorem LocalCounts.mono {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E E' : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K K' ζ : ℝ} (h : LocalCounts y β γ E F d K ζ) (hE : E' ⊆ E)
    (hK : K ≤ K') (hζ : 0 < ζ) : LocalCounts y β γ E' F d K' ζ := by
  intro t q r a hq hqr hr
  obtain ⟨C, hC, hmem⟩ := h t q r a hq hqr hr
  have hq0 : 0 < q := hζ.trans_le hq
  refine ⟨C, hC.trans (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg
    (div_nonneg (hq0.le.trans hqr) hq0.le) _)), fun l hl => hmem l (hE hl)⟩

theorem RowComparison.mono {E E' : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {K K' ζ : ℝ}
    (h : RowComparison E F K ζ) (hE : E' ⊆ E) (hK : K ≤ K') (hζ : 0 ≤ ζ) :
    RowComparison E' F K' ζ := by
  intro t u ⟨l, hl⟩ ⟨l', hl'⟩ i
  exact (h t u ⟨l, hE hl⟩ ⟨l', hE hl'⟩ i).trans
    (mul_le_mul_of_nonneg_right hK (by positivity))

theorem SlopeComparison.mono {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E E' : Set (Ω × ℝ)}
    {K K' ζ : ℝ} (h : SlopeComparison y β γ E K ζ) (hE : E' ⊆ E) (hK : K ≤ K')
    (hζ : 0 ≤ ζ) : SlopeComparison y β γ E' K' ζ := by
  intro l l' t u hl hl'
  exact (h l l' t u (hE hl) (hE hl')).trans
    (mul_le_mul_of_nonneg_right hK (by positivity))

theorem BinCaps.mono {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E E' : Set (Ω × ℝ)}
    {d K K' ζ : ℝ} (h : BinCaps ν y β γ E d K ζ) (hE : E' ⊆ E) (hK : K ≤ K') (hζ : 0 < ζ) :
    BinCaps ν y β γ E' d K' ζ := by
  intro q n hq hqn b t z
  have hq0 : 0 < q := hζ.trans_le hq
  refine (measure_mono ?_).trans ((h q n hq hqn b t z).trans ?_)
  · rintro l ⟨hb, hl, hz⟩
    exact ⟨hb, hE hl, hz⟩
  · gcongr

/-- The absolute cap of `FirstJet.Data` is the mixed cap at equal widths. -/
theorem absCap_of_mixedCap {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : UnregularizedChart ν y β γ E F d K ζ) (hζ : 0 < ζ) (t q : ℝ) (hq : ζ ≤ q)
    (hq1 : q ≤ 1) (z : Fin 3 → ℤ) :
    ν {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧
      ⌊y l 1 / q⌋ = z 2} ≤ ENNReal.ofReal (K * q ^ (2 + d)) := by
  have hq0 : 0 < q := hζ.trans_le hq
  have key := h.mixedCap t q q hq hq1 hq hq1 ![z 1, z 2] (z 0)
  have e : K * q ^ 2 * q ^ d = K * q ^ (2 + d) := by
    rw [Real.rpow_add hq0, Real.rpow_two]; ring
  rw [e] at key
  simpa using key

/-! ### The four stages -/

/-- Stage 1: local scalar counts. -/
def StageLocal : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        UnregularizedChart ν y β γ E F d (N ^ η) (N ^ (-c)) →
        ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ UnregularizedChart ν y β γ E' F d (N ^ ε) (N ^ (-c)) ∧
          LocalCounts y β γ E' F d (N ^ ε) (N ^ (-c))

/-- Stage 2: the row comparison. -/
def StageRow : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        UnregularizedChart ν y β γ E F d (N ^ η) (N ^ (-c)) →
        LocalCounts y β γ E F d (N ^ η) (N ^ (-c)) →
        ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ UnregularizedChart ν y β γ E' F d (N ^ ε) (N ^ (-c)) ∧
          RowComparison E' F (N ^ ε) (N ^ (-c))

/-- Stage 3: the slope comparison. -/
def StageSlope : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        UnregularizedChart ν y β γ E F d (N ^ η) (N ^ (-c)) →
        LocalCounts y β γ E F d (N ^ η) (N ^ (-c)) → RowComparison E F (N ^ η) (N ^ (-c)) →
        ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ UnregularizedChart ν y β γ E' F d (N ^ ε) (N ^ (-c)) ∧
          SlopeComparison y β γ E' (N ^ ε) (N ^ (-c))

/-- Stage 4: the relative dyadic coefficient-bin caps. -/
def StageBin : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        UnregularizedChart ν y β γ E F d (N ^ η) (N ^ (-c)) →
        LocalCounts y β γ E F d (N ^ η) (N ^ (-c)) → RowComparison E F (N ^ η) (N ^ (-c)) →
        SlopeComparison y β γ E (N ^ η) (N ^ (-c)) →
        ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ UnregularizedChart ν y β γ E' F d (N ^ ε) (N ^ (-c)) ∧
          BinCaps ν y β γ E' d (N ^ ε) (N ^ (-c))

/-- **The four stages give the chart regularization.** -/
theorem chartRegularization_of_stages (h1 : StageLocal) (h2 : StageRow) (h3 : StageSlope)
    (h4 : StageBin) : ChartRegularization := by
  intro d hd hd1 c hc ε hε
  obtain ⟨η₄, hη₄, hη₄ε, N₄, hN₄, h4⟩ := h4 d hd hd1 c hc ε hε
  obtain ⟨η₃, hη₃, hη₃₄, N₃, hN₃, h3⟩ := h3 d hd hd1 c hc η₄ hη₄
  obtain ⟨η₂, hη₂, hη₂₃, N₂, hN₂, h2⟩ := h2 d hd hd1 c hc η₃ hη₃
  obtain ⟨η₁, hη₁, hη₁₂, N₁, hN₁, h1⟩ := h1 d hd hd1 c hc η₂ hη₂
  refine ⟨η₁, hη₁, hη₁₂.trans (hη₂₃.trans (hη₃₄.trans hη₄ε)),
    max (max N₁ N₂) (max N₃ N₄), hN₁.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N hN Ω _ ν hν y β γ E F hE
  have hN₁' : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN₂' : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN₃' : N₃ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₄' : N₄ ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hpow : ∀ a b : ℝ, a ≤ b → N ^ a ≤ N ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le hN1 hab
  have hζ' : 0 < N ^ (-c) := Real.rpow_pos_of_pos (by linarith) _
  have hζ : 0 ≤ N ^ (-c) := hζ'.le
  obtain ⟨E₁, hE₁, hU₁, hL₁⟩ := h1 N hN₁' Ω ν hν y β γ E F hE
  obtain ⟨E₂, hE₂, hU₂, hR₂⟩ := h2 N hN₂' Ω ν hν y β γ E₁ F hU₁ hL₁
  have hL₂ := hL₁.mono hE₂ (hpow _ _ hη₂₃) hζ'
  obtain ⟨E₃, hE₃, hU₃, hS₃⟩ := h3 N hN₃' Ω ν hν y β γ E₂ F hU₂ hL₂ hR₂
  have hL₃ := hL₂.mono hE₃ (hpow _ _ hη₃₄) hζ'
  have hR₃ := hR₂.mono hE₃ (hpow _ _ hη₃₄) hζ
  obtain ⟨E₄, hE₄, hU₄, hB₄⟩ := h4 N hN₄' Ω ν hν y β γ E₃ F hU₃ hL₃ hR₃ hS₃
  have hL₄ := hL₃.mono hE₄ (hpow _ _ hη₄ε) hζ'
  have hR₄ := hR₃.mono hE₄ (hpow _ _ hη₄ε) hζ
  have hS₄ := hS₃.mono hE₄ (hpow _ _ hη₄ε) hζ
  refine ⟨E₄, hE₄.trans (hE₃.trans (hE₂.trans hE₁)), ?_⟩
  exact
    { measurable_y := hU₄.measurable_y
      measurable_β := hU₄.measurable_β
      measurable_γ := hU₄.measurable_γ
      measurable_F := hU₄.measurable_F
      measurableSet_E := hU₄.measurableSet_E
      subset_E := hU₄.subset_E
      bound_y := hU₄.bound_y
      bound_β := hU₄.bound_β
      bound_γ := hU₄.bound_γ
      bound_F := hU₄.bound_F
      mass := hU₄.mass
      support := hL₄
      absCap := fun t q hq hq1 z =>
        absCap_of_mixedCap hU₄ hζ' t q hq hq1 z
      rowLip := hR₄
      slopeLip := hS₄
      binCap := hB₄ }

end Submission.Obl.k4_fixed_prior_chart_regularization.Reg

end
