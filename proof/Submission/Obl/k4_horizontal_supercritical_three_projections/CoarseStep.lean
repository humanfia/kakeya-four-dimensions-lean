import Submission.Obl.k4_horizontal_supercritical_three_projections.ReturnNumerics
import Submission.Obl.k4_horizontal_supercritical_three_projections.FamilyMass

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory Filter
open scoped ENNReal BigOperators

/-- The remaining chart selection task, stated before fine intercept slicing.
The entire family has scalar floors under the current measure and dense total
coverage; no chart is selected on its own. -/
def CoarseProjectionPreparation {α : Type} [MeasurableSpace α]
    (N K : ℕ → ℝ) (d κ e₀ s₀ depth M : ℝ) (b : ℕ → α → Fin 6 → ℝ)
    (π : ℕ → Measure ℝ) (ρ : ℕ → Measure (α × ℝ)) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop,
    ∀ ζ : Measure (α × ℝ), ζ ≤ ρ k → ENNReal.ofReal (N k ^ (-η)) ≤ ζ univ →
      ∃ L : CoarseProjectionLayer α,
        L.Certified (b k) (N k ^ (-M)) (N k ^ (-(2 * κ * s₀)))
          (10 * K k) (N k ^ (-e₀)) (240 * (N k ^ τ) ^ 5)
          (N k ^ τ * N k ^ (-depth)) ∧
        (∀ i, 0 < π k (Ico ((L.q i 0 : ℝ) * N k ^ (-M))
          (((L.q i 0 : ℝ) + 1) * N k ^ (-M)))) ∧
        (∀ i, ENNReal.ofReal
          (L.weight (π k) (N k ^ (-M)) (N k ^ (-(2 * κ * s₀)))
            (N k ^ (-depth)) d i * N k ^ (-τ) / N k ^ τ) ≤
          ζ (L.A i ×ˢ Icc (0 : ℝ) 1)) ∧
        ENNReal.ofReal (N k ^ (-2 * τ)) ≤ ζ {p | ∃ i, p.1 ∈ L.A i}

/-- Dense coarse scalar ensembles give the exact uniform physical projection
step, with one coefficient exponent fixed before the fine mesh is chosen. -/
theorem single_projection_of_coarse_of_sequences {α : Type} [MeasurableSpace α]
    (N K : ℕ → ℝ) (d κ e₀ : ℝ)
    (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ)
    (b : ℕ → α → Fin 6 → ℝ)
    (hN₂ : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK₁ : ∀ k, 1 ≤ K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, K k ≤ N k ^ ξ)
    (hκ₀ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hbasic : ∀ k, Measurable (b k) ∧ IsProbabilityMeasure (ν k) ∧
      IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod volume) ∧
      ρ k ≤ μ k ∧ μ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    {s₀ depth M : ℝ}
    (hs₀ : 0 < s₀) (he₀ : 100 * s₀ < e₀) (hM : 100 * s₀ < M)
    (hdepth : depth < 3 * s₀ / 2)
    (hc : CoarseProjectionPreparation N K d κ e₀ s₀ depth M b π ρ) :
    SingleProjection N d depth (10 + 8 * s₀) M (2 * κ * s₀) b π ρ := by
  intro ε hε
  let τ := min (ε / 1000) (min (s₀ / 1000) (1 / 1000))
  have hτ : 0 < τ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hτε : τ ≤ ε / 1000 := min_le_left _ _
  have hτs : τ ≤ s₀ / 1000 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₁ : τ ≤ 1 / 1000 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨η, hη, hc⟩ := hc τ hτ
  refine ⟨η, hη, ?_⟩
  filter_upwards [hc, eventually_return_estimates_of_sequences N K κ e₀ hN₂ hNt hK₁ hKsub hκ₁ hs₀ he₀ hM hdepth hτ hε hτε hτs hτ₁]
    with k hc hnum
  intro ζ hζρ hmass
  obtain ⟨L, hL, hpalette, hfloor, hcovered⟩ := hc ζ hζρ hmass
  obtain ⟨hb, hν, hπ, hμdom, hρμ, hμsupp⟩ := hbasic k
  have : IsProbabilityMeasure (ν k) := hν
  have : IsProbabilityMeasure (π k) := hπ
  have hN : 1 ≤ N k := by linarith [hN₂ k]
  have hN₀ : 0 < N k := by linarith
  have hK : 0 < K k := by linarith [hK₁ k]
  have hζμ : ζ ≤ μ k := hζρ.trans hρμ
  have hdom := hζμ.trans hμdom
  have hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((hζμ _).trans_eq hμsupp) bot_le
  have hmassK : ζ univ ≤ ENNReal.ofReal (K k) := by
    simpa only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one] using
      incidence_assignment_bound (ν k) ζ univ (ENNReal.ofReal (K k)) hdom hsupp
  have hbudget := coarse_weight_budget hN₀ (by linarith [hK₁ k])
    ζ (π k) L hL.measurable hL.disjoint hfloor hmassK
  have hD : 0 < N k ^ (-(2 * κ * s₀)) := Real.rpow_pos_of_pos hN₀ _
  have hD₁ : N k ^ (-(2 * κ * s₀)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith [hκ₀])
  obtain ⟨hχD, hround, hcorner, hnorm, hfit, hcoeff, hbudget', hlost⟩ := hnum
  obtain ⟨ζ', L', hζ', hcover', hgood, hremaining⟩ := refine_coarse_layer
    hN hD hD₁ (Real.rpow_pos_of_pos hN₀ _) hχD
    (by positivity : 0 ≤ 10 * K k) (by positivity : 0 ≤ 240 * (N k ^ τ) ^ 5)
    hround (b k) hb (π k) ζ (ρ k) hζρ hsupp L hL hpalette
    hcorner hnorm hfit hcoeff (by linarith [hbudget])
  refine ⟨L', ζ', hζ', ?_, hcover', hgood⟩
  apply ENNReal.le_of_add_le_add_right (ENNReal.ofReal_ne_top :
    ENNReal.ofReal ((N k ^ ε)⁻¹ * (4 * (N k ^ τ) ^ 2 * K k)) ≠ ⊤)
  calc
    _ = ENNReal.ofReal (N k ^ (-ε) +
        (N k ^ ε)⁻¹ * (4 * (N k ^ τ) ^ 2 * K k)) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (N k ^ (-2 * τ)) := ENNReal.ofReal_le_ofReal hlost
    _ ≤ ζ' univ + ENNReal.ofReal ((N k ^ ε)⁻¹ *
        (4 * ∑ i, L.weight (π k) (N k ^ (-M)) (N k ^ (-(2 * κ * s₀)))
          (N k ^ (-depth)) d i)) := hcovered.trans hremaining
    _ ≤ _ := by
      have hmul :
          4 * ∑ i, L.weight (π k) (N k ^ (-M)) (N k ^ (-(2 * κ * s₀)))
            (N k ^ (-depth)) d i ≤ 4 * (N k ^ τ) ^ 2 * K k := by
        linarith [hbudget]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hmul (by positivity)))

namespace HorizontalModel

variable {α : Type} [MeasurableSpace α] (m : HorizontalModel α)

/-- The coarse ensemble target for the original horizontal model. -/
def CoarsePreparation (s₀ depth M : ℝ) : Prop :=
  CoarseProjectionPreparation m.N m.K m.d m.κ m.e₀ s₀ depth M m.b m.π m.ρ

/-- The generic physical return specialized to the original model. -/
theorem single_projection_of_coarse (hm : m.Valid) {s₀ depth M : ℝ}
    (hs₀ : 0 < s₀) (he₀ : 100 * s₀ < m.e₀) (hM : 100 * s₀ < M)
    (hdepth : depth < 3 * s₀ / 2) (hc : m.CoarsePreparation s₀ depth M) :
    SingleProjection m.N m.d depth (10 + 8 * s₀) M (2 * m.κ * s₀) m.b m.π m.ρ := by
  apply single_projection_of_coarse_of_sequences m.N m.K m.d m.κ m.e₀
    m.ν m.μ m.ρ m.π m.b hm.N_ge hm.N_tendsto hm.K_ge hm.K_subpower hm.κ_pos hm.κ_le
    _ hs₀ he₀ hM hdepth hc
  intro k
  obtain ⟨hb, hν, hπ, hdom, hρ, ht, -⟩ := hm.basic k
  exact ⟨hb, hν, hπ, hdom, hρ, ht⟩

end HorizontalModel

end Submission.Obl.k4_horizontal_supercritical_three_projections
