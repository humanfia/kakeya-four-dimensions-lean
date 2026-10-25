import Submission.Obl.k4_scalar_grid_cartesian_field.DataFacts
import Submission.Obl.k4_scalar_grid_cartesian_field.Growth
import Submission.Obl.k4_scalar_grid_cartesian_field.MassRatio

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- The exact bad set whose original weighted fraction vanishes in the frozen qualification oracle. -/
noncomputable def unqualified (data : Data) (M : ℕ)
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (data.W k) → Set Incidence) (B ε : ℝ)
    (k : ℕ) (g : Fin (data.W k)) : Set Incidence :=
  {p | ∃ i : Fin (data.n k 1), data.γ k 1 i = g ∧ p.1 ∈ data.A k 1 i ∧
    p.2 ∈ I data (data.T k 1) (data.j k 1 i) ∧ ¬fit data k M G E B ε p i}

/-- A measurable qualified family with a floor in the original weighted graph law. -/
noncomputable def qualifiedPartsAt (data : Data) (M : ℕ)
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (data.W k) → Set Incidence) (B : ℝ) (H : ℕ → ℝ)
    (ε : ℝ) (k : ℕ) : Prop :=
  ∃ Good : Fin (data.W k) → Set Incidence,
    (∀ g, MeasurableSet (Good g) ∧ Good g ⊆ E k g ∧
      ∀ p ∈ Good g, p ∉ unqualified data M G E B ε k g) ∧
    ENNReal.ofReal (1 / (2 * H k)) ≤
      ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (Good g)

/-- Qualification is selected at a slowly vanishing accuracy, before the packet pigeonhole.
No quantitative rate against a subpower loss is imposed on the bad fraction. -/
theorem qualified_parts_fixed_accuracy (data : Data) (hb : baseHyp data)
    (M : ℕ) (L B : ℝ) (H : ℕ → ℝ)
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E E₀ : (k : ℕ) → Fin (data.W k) → Set Incidence)
    (hg : graphData data E₀ L H B G E) (ε : ℝ)
    (hq : Tendsto (fun k =>
      (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) *
        (data.ρ k g).restrict (E k g) (unqualified data M G E B ε k g)).toReal /
      (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) *
        (data.ρ k g).restrict (E k g) univ).toReal) atTop (nhds 0)) :
    ∀ᶠ k in atTop, qualifiedPartsAt data M G E B H ε k := by
  classical
  let total : ℕ → ENNReal := fun k => ∑ g : Fin (data.W k),
    ENNReal.ofReal (data.ω k g) * (data.ρ k g).restrict (E k g) univ
  let bad : ℕ → ENNReal := fun k => ∑ g : Fin (data.W k),
    ENNReal.ofReal (data.ω k g) * (data.ρ k g).restrict (E k g)
      (unqualified data M G E B ε k g)
  have htotal (k : ℕ) : total k ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro g _
    letI := original_finite_of_base data hb k g
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hbad (k : ℕ) : bad k ≤ total k := by
    exact Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (measure_mono (subset_univ _))
  have hpos : ∀ᶠ k in atTop, 0 < total k := by
    filter_upwards [hg.2.2 2 (by norm_num)] with k hk
    have hH : 0 < H k := lt_of_lt_of_le zero_lt_one (hg.1.1 k)
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr hH)) hk.1
  have hsmall := eventually_relative_mass_small bad total htotal hbad hpos hq
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hg.2.2 2 (by norm_num), hsmall] with k hk hs
  obtain ⟨Good, hGood, hbudget⟩ := weighted_measurable_qualified_parts
    (data.ρ k) (fun g => ENNReal.ofReal (data.ω k g)) (E k)
    (unqualified data M G E B ε k) (fun g => (hk.2 g).1)
  refine ⟨Good, hGood, ?_⟩
  let kept : ENNReal := ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (Good g)
  have hkept : kept ≤ total k := by
    apply Finset.sum_le_sum
    intro g _
    simpa only [Measure.restrict_apply_univ] using
      (mul_le_mul' le_rfl (measure_mono (hGood g).2.1) :
        ENNReal.ofReal (data.ω k g) * data.ρ k g (Good g) ≤
        ENNReal.ofReal (data.ω k g) * data.ρ k g (E k g))
  have hcover : total k ≤ kept + bad k := by
    simpa only [total, kept, bad, Measure.restrict_apply_univ] using hbudget
  have hhalf := half_mass_of_quarter_bad (htotal k) hkept (hbad k) hcover hs
  calc
    _ = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal ((H k)⁻¹) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * total k := mul_le_mul' le_rfl hk.1
    _ ≤ _ := hhalf

/-- The fixed positive qualification accuracies can be relaxed slowly while all losses stay subpower. -/
theorem qualified_parts_slow_accuracy (data : Data) (hscale : scaleHyp data) (hb : baseHyp data)
    (M : ℕ) (L B : ℝ) (H : ℕ → ℝ)
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E E₀ : (k : ℕ) → Fin (data.W k) → Set Incidence)
    (hg : graphData data E₀ L H B G E)
    (hq : ∀ ε : ℝ, 0 < ε → Tendsto (fun k =>
      (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) *
        (data.ρ k g).restrict (E k g) (unqualified data M G E B ε k g)).toReal /
      (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) *
        (data.ρ k g).restrict (E k g) univ).toReal) atTop (nhds 0)) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (nhds 0) ∧
      subpower data (fun k => data.N k ^ ε k) ∧
      ∀ᶠ k in atTop, qualifiedPartsAt data M G E B H (ε k) k := by
  exact exists_subpower_accuracy (fun k => by linarith [hscale.1 k])
    (fun ε k => qualifiedPartsAt data M G E B H ε k)
    (fun ε hε => qualified_parts_fixed_accuracy data hb M L B H G E E₀ hg ε (hq ε hε))

end Submission.Obl.k4_scalar_grid_cartesian_field
