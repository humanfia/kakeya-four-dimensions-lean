import Submission.Obl.k4_horizontal_supercritical_three_projections.CellCaps
import Submission.Obl.k4_horizontal_supercritical_three_projections.SupportCount
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

/-!
# Chart caps in the scalar coordinates (one index `k`)

The scalar trajectory of a chart `(P, Q, β)` has coefficients
`![(b₁ - QD)/D, -2(b₀ - PD)/D, b₂, b₅, 0]`: its `y` is the scalar parameter
`R(t)` and its `x` is the hidden coordinate. This file states the pure cell
caps, the angular cell caps (slope `-2p` in an interval) and the terminal
support count in exactly these coordinates.
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Parent
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped ENNReal

noncomputable section

/-- The scalar coefficients of a trajectory in the chart `(P, Q)`. -/
def chartParams (D : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![(b 1 - (Q : ℝ) * D) / D, -2 * ((b 0 - (P : ℝ) * D) / D), b 2, b 5, 0]

theorem scalarCell_chartParams (D σ : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) (t : ℝ) :
    scalarCell (chartParams D P Q b) t σ = chartCell D σ P Q b t := by
  have hy : scalarY (chartParams D P Q b) t =
      scalarParameter t ((b 0 - P * D) / D) ((b 1 - Q * D) / D) := by
    simp only [scalarY, chartParams, scalarParameter, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  simp only [scalarCell, chartCell, hy]

theorem scalarX_chartParams (D : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) (t : ℝ) :
    scalarX (chartParams D P Q b) t = b 2 + t * b 5 := by
  simp [scalarX, chartParams]

theorem chartParams_one (D : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) :
    chartParams D P Q b 1 = -2 * ((b 0 - (P : ℝ) * D) / D) := by
  simp [chartParams]

theorem measurable_chartParams {α : Type*} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (D : ℝ) (P Q : ℤ) : Measurable fun l => chartParams D P Q (b l) := by
  apply measurable_pi_iff.mpr
  intro i
  have h0 : Measurable fun l => b l 0 := (measurable_pi_apply 0).comp hb
  have h1 : Measurable fun l => b l 1 := (measurable_pi_apply 1).comp hb
  have h2 : Measurable fun l => b l 2 := (measurable_pi_apply 2).comp hb
  have h5 : Measurable fun l => b l 5 := (measurable_pi_apply 5).comp hb
  fin_cases i
  · exact (h1.sub_const _).div_const D
  · exact ((h0.sub_const _).div_const D).const_mul (-2)
  · exact h2
  · exact h5
  · exact measurable_const

variable {α : Type*} [MeasurableSpace α]

/-- Incidences outside the unit time interval are null. -/
theorem measure_le_of_time_support {μ : Measure (α × ℝ)}
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) (E : Set (α × ℝ)) :
    μ E ≤ μ (E ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) := by
  have hsub : E ⊆ (E ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
    intro p hp
    by_cases ht : p.2 ∈ Icc (0 : ℝ) 1
    · exact Or.inl ⟨hp, ht⟩
    · exact Or.inr (fun h => ht h.2)
  calc μ E ≤ μ ((E ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) :=
        measure_mono hsub
    _ ≤ μ (E ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) + μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ :=
        measure_union_le _ _
    _ = μ (E ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) := by rw [hsupp, add_zero]

/-- **Pure scalar cell cap** of a chart, at one index. -/
theorem pure_cell_cap {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ} (hb : Measurable b)
    {π : Measure ℝ} {K D χ ζ σ ρ δc d : ℝ} {P Q β : ℤ}
    (hK : 1 ≤ K) (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hρ : 0 < ρ) (hδc : 0 < δc) (hδcσ : δc ≤ D * σ ^ 2)
    (hχσ : χ ≤ D * σ) (hζσ : ζ ≤ D * σ) (hζ : 0 ≤ ζ)
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcap : DirectionCap μ b π K δc χ ρ d β) (z : Fin 2 → ℤ) (j : ℤ) :
    μ {p | p.1 ∈ chartSet b K ζ D χ P Q β ∧
        scalarCell (chartParams D P Q (b p.1)) p.2 σ = z ∧
        ⌊scalarX (chartParams D P Q (b p.1)) p.2 / ρ⌋ = j} ≤
      ENNReal.ofReal (3 * 10 ^ 6 * K ^ 4 * σ ^ 2 * D ^ 2 * ρ ^ d) *
        π {x | ⌊x / χ⌋ = β} := by
  by_cases hne : (chartSet b K ζ D χ P Q β).Nonempty
  swap
  · have hE : {p : α × ℝ | p.1 ∈ chartSet b K ζ D χ P Q β ∧
        scalarCell (chartParams D P Q (b p.1)) p.2 σ = z ∧
        ⌊scalarX (chartParams D P Q (b p.1)) p.2 / ρ⌋ = j} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hp
      exact absurd ⟨p.1, hp⟩ hne
    rw [hE, measure_empty]; exact bot_le
  obtain ⟨l, hl⟩ := hne
  obtain ⟨-, -, -, -, -, -, hPD, -, -, -, -⟩ := chartSet_bounds hD hχ hl
  have hpa : |2 * ((P : ℝ) * D) - (P : ℝ) * D| ≤ 3 * K := by
    have : 2 * ((P : ℝ) * D) - (P : ℝ) * D = (P : ℝ) * D := by ring
    rw [this]; linarith
  refine (measure_le_of_time_support hsupp _).trans ?_
  have h := sliced_cell_cap hb (β' := 1) (pa := (P : ℝ) * D) (Q := Q) (z := z) (j := j) hK hD hD1 hχ hσ
    hρ hδc hδcσ hσ1 le_rfl hχσ hζσ hζ hpa hcap
    ({p | p.1 ∈ chartSet b K ζ D χ P Q β ∧ scalarCell (chartParams D P Q (b p.1)) p.2 σ = z ∧
      ⌊scalarX (chartParams D P Q (b p.1)) p.2 / ρ⌋ = j} ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) ?_
  · simpa only [mul_one] using h
  · rintro p ⟨⟨hc, hz, hj⟩, ht⟩
    rw [scalarCell_chartParams] at hz
    rw [scalarX_chartParams] at hj
    obtain ⟨-, -, -, -, hP, -⟩ := chartSet_bounds hD hχ hc
    exact ⟨hc, ht, hz, hj, by simpa using hP⟩

/-- **Angular scalar cell cap** of a chart, at one index: fixing the scalar slope
`-2p` to an interval of width `h` gains the factor `h`. -/
theorem angular_cell_cap {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ} (hb : Measurable b)
    {π : Measure ℝ} {K D χ ζ σ ρ δc d h : ℝ} {P Q β : ℤ}
    (hK : 1 ≤ K) (hD : 0 < D) (hD4 : D ≤ 1 / 4) (hχ : 0 < χ) (hσ : 0 < σ)
    (hρ : 0 < ρ) (hδc : 0 < δc) (hδcσ : δc ≤ D * σ ^ 2)
    (hσh : 4 * σ ≤ h) (hh : h ≤ 1)
    (hχσ : χ ≤ D * σ) (hζσ : ζ ≤ D * σ) (hζ : 0 ≤ ζ)
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcap : DirectionCap μ b π K δc χ ρ d β) (z : Fin 2 → ℤ) (j i : ℤ) :
    μ {p | p.1 ∈ chartSet b K ζ D χ P Q β ∧
        scalarCell (chartParams D P Q (b p.1)) p.2 σ = z ∧
        ⌊scalarX (chartParams D P Q (b p.1)) p.2 / ρ⌋ = j ∧
        ⌊chartParams D P Q (b p.1) 1 / h⌋ = i} ≤
      ENNReal.ofReal (3 * 10 ^ 6 * K ^ 4 * σ ^ 2 * (h / 4) * D ^ 2 * ρ ^ d) *
        π {x | ⌊x / χ⌋ = β} := by
  have hh0 : 0 < h := by linarith
  set E := {p : α × ℝ | p.1 ∈ chartSet b K ζ D χ P Q β ∧
        scalarCell (chartParams D P Q (b p.1)) p.2 σ = z ∧
        ⌊scalarX (chartParams D P Q (b p.1)) p.2 / ρ⌋ = j ∧
        ⌊chartParams D P Q (b p.1) 1 / h⌋ = i} with hEdef
  -- the slice pins the first intercept near `pa`
  set pa := (P : ℝ) * D - D / 2 * ((i : ℝ) + 1 / 2) * h with hpadef
  have hslice : ∀ p ∈ E, |b p.1 0 - pa| ≤ D * (h / 4) := by
    rintro p ⟨-, -, -, hi⟩
    rw [chartParams_one] at hi
    obtain ⟨h₀, h₁⟩ := floor_cell_mem (x := -2 * ((b p.1 0 - (P : ℝ) * D) / D)) hh0
    rw [hi] at h₀ h₁
    have hb0 : b p.1 0 = (P : ℝ) * D - D / 2 * (-2 * ((b p.1 0 - (P : ℝ) * D) / D)) := by
      field_simp; ring
    have heq : b p.1 0 - pa =
        D / 2 * (((i : ℝ) + 1 / 2) * h - (-2 * ((b p.1 0 - (P : ℝ) * D) / D))) := by
      rw [hpadef]; nth_rewrite 1 [hb0]; ring
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < D / 2)]
    have : |((i : ℝ) + 1 / 2) * h - (-2 * ((b p.1 0 - (P : ℝ) * D) / D))| ≤ h / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    calc D / 2 * |((i : ℝ) + 1 / 2) * h - (-2 * ((b p.1 0 - (P : ℝ) * D) / D))|
        ≤ D / 2 * (h / 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = D * (h / 4) := by ring
  rcases E.eq_empty_or_nonempty with hE0 | ⟨p₀, hp₀⟩
  · rw [hE0, measure_empty]; exact bot_le
  -- bound on the slice centre, from one incidence
  have hpa : |2 * ((P : ℝ) * D) - pa| ≤ 3 * K := by
    obtain ⟨hc₀, -, -, hi₀⟩ := hp₀
    obtain ⟨hp₀', hp₁', -, -, -, -, hPD, -, -, -, -⟩ := chartSet_bounds hD hχ hc₀
    rw [chartParams_one] at hi₀
    obtain ⟨h₀, h₁⟩ := floor_cell_mem (x := -2 * ((b p₀.1 0 - (P : ℝ) * D) / D)) hh0
    rw [hi₀] at h₀ h₁
    have hc' : |((i : ℝ) + 1 / 2) * h| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith
    have hc : |(i : ℝ) + 1 / 2| * h ≤ 3 := by
      have e := abs_mul ((i : ℝ) + 1 / 2) h
      rw [abs_of_pos hh0] at e
      linarith
    have heq : 2 * ((P : ℝ) * D) - pa = (P : ℝ) * D + D / 2 * (((i : ℝ) + 1 / 2) * h) := by
      rw [hpadef]; ring
    rw [heq]
    calc |(P : ℝ) * D + D / 2 * (((i : ℝ) + 1 / 2) * h)|
        ≤ |(P : ℝ) * D| + D / 2 * (|(i : ℝ) + 1 / 2| * h) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < D / 2),
            abs_of_pos hh0]
      _ ≤ (K + D) + D / 2 * 3 := by
          gcongr
      _ ≤ 3 * K := by linarith
  have hσ1 : σ ≤ 1 := by linarith
  refine (measure_le_of_time_support hsupp _).trans ?_
  have h4 : σ ≤ h / 4 := by linarith
  exact sliced_cell_cap hb (β' := h / 4) (pa := pa) (Q := Q) (z := z) (j := j) hK hD
    (by linarith) hχ hσ hρ hδc hδcσ h4 (by linarith) hχσ hζσ hζ hpa hcap
    (E ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) (by
      rintro p ⟨hp, ht⟩
      have hs := hslice p hp
      obtain ⟨hc, hz, hj, -⟩ := hp
      rw [scalarCell_chartParams] at hz
      rw [scalarX_chartParams] at hj
      exact ⟨hc, ht, hz, hj, hs⟩)

variable {ν : Measure α}

/-- **The terminal support count** in scalar coordinates, at one index. -/
theorem scalar_support_count {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {K a q g d D χ ζ σ δc : ℝ} {T n : ℕ} {j : Fin n → Fin (2 ^ T)}
    {A B : Fin n → Set α} {c : Fin n → Fin 5 → ℝ} {L : Fin n → Fin 4 → ℝ}
    (H : BlockHyp ν μ b K a q g d T n j A B c L)
    (hK : 1 ≤ K) (ha : 0 < a) (hq : 0 < q) (hg : 0 < g) (hD : 0 < D) (hχ : 0 < χ)
    (hσ : 0 < σ) (hδc : 0 < δc)
    (hgq : g ≤ K * q) (hqg : q ≤ K * g) (haq : a ≤ K * q) (hDa : D ≤ a)
    (hq1 : q ≤ 1 / 2) (hδcq : δc ≤ q ^ 2) (hσq : σ ≤ q / 2) (hσ1 : σ ≤ 1 / 2)
    (hDq : D ≤ q / 8) (hχD : χ ≤ D)
    (hsmall : 2 * D * σ + ζ + χ ≤ q ^ 2 / 2)
    (hcontact : 8 * K ^ 2 * (1 + a / q ^ 2) * (χ + ζ) ≤ K * a)
    (hcellosc : 8 * K ^ 2 * (1 + a / q ^ 2) * σ * (4 + 2 * K) ≤ K * a)
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ blockTime T (j i))
    (hx3 : ∀ᵐ p ∂μ, |b p.1 2 + p.2 * b p.1 5| ≤ K)
    (hcap : ∀ (w : Fin 3 → ℤ) (j' : ℤ), μ {p | (fun e => ⌊(![p.2, b p.1 0 + p.2 * b p.1 3,
        b p.1 1 + p.2 * b p.1 4] : Fin 3 → ℝ) e / δc⌋) = w ∧
        ⌊b p.1 2 + p.2 * b p.1 5⌋ = j'} ≤ ENNReal.ofReal (K * δc ^ 3))
    (P Q β : ℤ) :
    ∃ F : Finset ((Fin 2 → ℤ) × ℤ), (F.card : ℝ) * σ ^ 2 ≤ 10 ^ 12 * K ^ 20 * a ^ (-d) ∧
      ∀ᵐ p ∂μ, p.1 ∈ chartSet b K ζ D χ P Q β →
        (scalarCell (chartParams D P Q (b p.1)) p.2 σ,
          ⌊scalarX (chartParams D P Q (b p.1)) p.2 / a⌋) ∈ F := by
  obtain ⟨hcard, hmem⟩ := support_count_finite hb H hK ha hq hg hD hχ hσ hδc hgq hqg haq
    hDa hq1 hδcq hσq hσ1 hDq hχD hsmall hcontact hcellosc hcover hx3 hcap P Q β
  refine ⟨_, hcard, ?_⟩
  have htime : ∀ᵐ p ∂μ, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    refine measure_mono_null ?_ hsupp
    intro p hp
    exact fun h => hp h.2
  filter_upwards [hmem, htime] with p hp ht hc
  rw [scalarCell_chartParams, scalarX_chartParams]
  exact hp hc ht

/-- **Total chart cap** at one index: summing the pure cell caps with unit hidden
bins over all scalar cells. -/
theorem total_chart_cap {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ} (hb : Measurable b)
    {π : Measure ℝ} {K D χ ζ σ δc d : ℝ} {P Q β : ℤ}
    (hK : 1 ≤ K) (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (hδc : 0 < δc) (hδcσ : δc ≤ D * σ ^ 2)
    (hχσ : χ ≤ D * σ) (hζσ : ζ ≤ D * σ) (hζ : 0 ≤ ζ)
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hx3 : ∀ᵐ p ∂μ, |b p.1 2 + p.2 * b p.1 5| ≤ K)
    (hcap : DirectionCap μ b π K δc χ 1 d β) :
    μ (chartSet b K ζ D χ P Q β ×ˢ univ) ≤
      ENNReal.ofReal (2 * 10 ^ 8 * K ^ 5 * D ^ 2) * π {x | ⌊x / χ⌋ = β} := by
  classical
  have hK0 : 0 ≤ K := by linarith
  set cells := chartCells σ
  set bins := intervalBins 1 0 K
  set E : Set (α × ℝ) := ⋃ z ∈ cells, ⋃ j ∈ bins,
    {p | p.1 ∈ chartSet b K ζ D χ P Q β ∧ scalarCell (chartParams D P Q (b p.1)) p.2 σ = z ∧
      ⌊scalarX (chartParams D P Q (b p.1)) p.2 / 1⌋ = j}
  have hnull : μ {p : α × ℝ | ¬ (p.2 ∈ Icc (0 : ℝ) 1 ∧ |b p.1 2 + p.2 * b p.1 5| ≤ K)} = 0 := by
    have ht : ∀ᵐ p ∂μ, p.2 ∈ Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      refine measure_mono_null ?_ hsupp
      intro p hp
      exact fun h => hp h.2
    have := ht.and hx3
    rwa [ae_iff] at this
  have hsub : chartSet b K ζ D χ P Q β ×ˢ univ ⊆
      E ∪ {p : α × ℝ | ¬ (p.2 ∈ Icc (0 : ℝ) 1 ∧ |b p.1 2 + p.2 * b p.1 5| ≤ K)} := by
    rintro p ⟨hp, -⟩
    by_cases hg : p.2 ∈ Icc (0 : ℝ) 1 ∧ |b p.1 2 + p.2 * b p.1 5| ≤ K
    · left
      refine Set.mem_biUnion (chartCell_mem_chartCells hD hχ hσ hp hg.1) ?_
      refine Set.mem_biUnion (mem_intervalBins (c := 0) one_pos (by simpa using hg.2)) ?_
      refine ⟨hp, scalarCell_chartParams D σ P Q (b p.1) p.2, ?_⟩
      rw [scalarX_chartParams]
    · exact Or.inr hg
  have hcell : ∀ z j, μ {p | p.1 ∈ chartSet b K ζ D χ P Q β ∧
      scalarCell (chartParams D P Q (b p.1)) p.2 σ = z ∧
      ⌊scalarX (chartParams D P Q (b p.1)) p.2 / 1⌋ = j} ≤
      ENNReal.ofReal (3 * 10 ^ 6 * K ^ 4 * σ ^ 2 * D ^ 2 * 1 ^ d) * π {x | ⌊x / χ⌋ = β} :=
    fun z j => pure_cell_cap hb hK hD hD1 hχ hσ (by linarith) one_pos hδc hδcσ hχσ hζσ hζ hsupp
      hcap z j
  have hcells := card_chartCells_mul_sq hσ hσ1
  have hbins : (bins.card : ℝ) ≤ 2 * K + 5 := by
    have := card_intervalBins one_pos hK0 0
    simpa using this
  calc μ (chartSet b K ζ D χ P Q β ×ˢ univ)
      ≤ μ (E ∪ {p : α × ℝ | ¬ (p.2 ∈ Icc (0 : ℝ) 1 ∧ |b p.1 2 + p.2 * b p.1 5| ≤ K)}) :=
        measure_mono hsub
    _ ≤ μ E + 0 := (measure_union_le _ _).trans (by rw [hnull])
    _ = μ E := add_zero _
    _ ≤ ∑ z ∈ cells, ∑ j ∈ bins, μ {p | p.1 ∈ chartSet b K ζ D χ P Q β ∧
          scalarCell (chartParams D P Q (b p.1)) p.2 σ = z ∧
          ⌊scalarX (chartParams D P Q (b p.1)) p.2 / 1⌋ = j} :=
        (measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun z _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ _z ∈ cells, ∑ _j ∈ bins,
          ENNReal.ofReal (3 * 10 ^ 6 * K ^ 4 * σ ^ 2 * D ^ 2 * 1 ^ d) * π {x | ⌊x / χ⌋ = β} :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun j _ => hcell z j
    _ = ENNReal.ofReal ((cells.card : ℝ) * (bins.card : ℝ) *
          (3 * 10 ^ 6 * K ^ 4 * σ ^ 2 * D ^ 2 * 1 ^ d)) * π {x | ⌊x / χ⌋ = β} := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (p := (cells.card : ℝ) * (bins.card : ℝ)) (by positivity),
          ENNReal.ofReal_mul (p := (cells.card : ℝ)) (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        ring
    _ ≤ ENNReal.ofReal (2 * 10 ^ 8 * K ^ 5 * D ^ 2) * π {x | ⌊x / χ⌋ = β} := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [Real.one_rpow, mul_one]
        calc (cells.card : ℝ) * (bins.card : ℝ) * (3 * 10 ^ 6 * K ^ 4 * σ ^ 2 * D ^ 2)
            = ((cells.card : ℝ) * σ ^ 2) * (bins.card : ℝ) * (3 * 10 ^ 6 * K ^ 4 * D ^ 2) := by
              ring
          _ ≤ 6 * (7 * K) * (3 * 10 ^ 6 * K ^ 4 * D ^ 2) := by
              gcongr
              linarith
          _ = (126 * 10 ^ 6) * (K ^ 5 * D ^ 2) := by ring
          _ ≤ (2 * 10 ^ 8) * (K ^ 5 * D ^ 2) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = 2 * 10 ^ 8 * K ^ 5 * D ^ 2 := by ring

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
