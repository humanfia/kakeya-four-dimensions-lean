/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/PlanarSupport.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.PlanarEnergy
import Submission.Obl.k4_scalar_heavy_intercept_selection.PairBreadth

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open MeasureTheory Set
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- Original cellwise velocity breadth and a prior-to-current-mass
comparison turn planar Kakeya into a lower occupied-area bound. -/
theorem planar_support_floor {α ι : Type*} [MeasurableSpace α]
    {C : ℝ} (hC : 0 ≤ C) (hMK : FiniteMK 2 C)
    (θ : Measure α) [IsFiniteMeasure θ]
    (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin 2)) (hΦ : Measurable Φ)
    (a e : α → EuclideanSpace ℝ (Fin 2)) (ha : Measurable a) (he : Measurable e)
    (he₁ : ∀ l, ‖e l‖ = 1) {B : ℝ} (hB : ∀ l, ‖a l‖ ≤ B)
    {r : ℝ} (hr : 0 < r) (R : ℝ) (Λ : Set α) (hΛ : MeasurableSet Λ)
    (F : Finset ι) (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hEm : ∀ j ∈ F, MeasurableSet (E j)) (hEd : (F : Set ι).PairwiseDisjoint E)
    (hER : ∀ j ∈ F, E j ⊆ Metric.closedBall 0 R)
    (c : NNReal) (hc : 0 < c)
    (hpush : ∀ j ∈ F, (μ.restrict {p | p.1 ∈ Λ ∧ Φ p ∈ E j}).map Prod.fst ≤
      c • θ.restrict Λ)
    (htube : ∀ j ∈ F, ∀ p : α × ℝ, p.1 ∈ Λ → Φ p ∈ E j →
      ∀ x ∈ E j, x ∈ tube r (a p.1) (e p.1))
    (v : α → ℝ) (hv : Measurable v) {η β volume₀ L : ℝ}
    (hβ : 0 < β) (hvol₀ : 0 < volume₀) (hL : 0 ≤ L)
    (hvol : ∀ j ∈ F, ENNReal.ofReal volume₀ ≤ volume (E j))
    (hdet : ∀ l ∈ Λ, ∀ l' ∈ Λ, η ≤ |v l - v l'| →
      β ≤ |Matrix.det (Matrix.of fun i k : Fin 2 => (![e l, e l'] i) k)|)
    (hthin : ∀ j ∈ F, ∀ w,
      (μ.restrict {p | p.1 ∈ Λ ∧ Φ p ∈ E j}) {p | |v p.1 - w| < η} ≤
        ENNReal.ofReal (1 / 2 : ℝ) * μ {p | p.1 ∈ Λ ∧ Φ p ∈ E j})
    (hsum : ∑ j ∈ F, (μ {p | p.1 ∈ Λ ∧ Φ p ∈ E j}).toReal = (μ univ).toReal)
    (hmass : 0 < (μ univ).toReal)
    (hprior : (θ Λ).toReal ≤ L * (μ univ).toReal) :
    1 ≤ (F.card : ℝ) *
      (4 * C * r ^ 2 * L ^ 2 / (volume₀ * β * (1 / 2 : ℝ) / (c : ℝ) ^ 2)) := by
  classical
  let S : ι → Set (α × ℝ) := fun j => {p | p.1 ∈ Λ ∧ Φ p ∈ E j}
  have hS (j : ι) (hj : j ∈ F) : MeasurableSet (S j) :=
    (measurable_fst hΛ).inter (hΦ (hEm j hj))
  have hsuccess (j : ι) (hj : j ∈ F) :
      μ (S j) ^ 2 / (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ ≤
        Measure.pi (fun _ : Fin 2 => μ)
          {p | (∀ i, (p i).1 ∈ Λ ∧ Φ (p i) ∈ E j) ∧
            β ≤ |Matrix.det (Matrix.of fun i k : Fin 2 => e (p i).1 k)|} := by
    have hsep := separated_cell_tuple_mass_floor μ (fun p => v p.1)
      (hv.comp measurable_fst) (S j) (hS j hj) η (hthin j hj)
    calc
      _ = ENNReal.ofReal (1 / 2 : ℝ) * μ (S j) ^ 2 := by simp [div_eq_mul_inv, mul_comm]
      _ ≤ _ := hsep.trans (measure_mono (by
        intro p hp
        refine ⟨hp.1, ?_⟩
        have ht := hdet (p 0).1 (hp.1 0).1 (p 1).1 (hp.1 1).1 hp.2
        convert ht using 1
        congr 2
        ext i k
        fin_cases i <;> rfl))
  have h := planar_kakeya_cell_energy hC hMK θ μ Φ hΦ a e ha he he₁ hB hr R Λ hΛ F E
    hEm hEd hER c hc hpush htube β ((ENNReal.ofReal (1 / 2 : ℝ))⁻¹)
    (ENNReal.ofReal volume₀) (fun j => μ (S j)) hvol hsuccess
  have hreal := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun j hj => ENNReal.pow_ne_top (measure_ne_top μ (S j)))] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal hvol₀.le, ENNReal.toReal_ofReal hβ.le,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * C * r ^ 2)] at hreal
  let A : ℝ := volume₀ * β * (1 / 2 : ℝ) / (c : ℝ) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hreal' : A * ∑ j ∈ F, (μ (S j)).toReal ^ 2 ≤ 4 * C * r ^ 2 * (θ Λ).toReal ^ 2 := by
    convert hreal using 1 <;> dsimp [A] <;> ring
  have hprior_sq : (θ Λ).toReal ^ 2 ≤ L ^ 2 * (μ univ).toReal ^ 2 := by
    have ht := mul_le_mul hprior hprior ENNReal.toReal_nonneg (mul_nonneg hL hmass.le)
    nlinarith
  have henergy : ∑ j ∈ F, (μ (S j)).toReal ^ 2 ≤
      (4 * C * r ^ 2 * L ^ 2 / A) * (μ univ).toReal ^ 2 := by
    have hb := hreal'.trans (mul_le_mul_of_nonneg_left hprior_sq (by positivity : 0 ≤ 4 * C * r ^ 2))
    calc
      _ ≤ (4 * C * r ^ 2 * (L ^ 2 * (μ univ).toReal ^ 2)) / A :=
        (le_div_iff₀ hA).2 (by simpa only [mul_comm] using hb)
      _ = _ := by ring
  exact cell_count_floor_of_energy F (fun j => (μ (S j)).toReal) hmass hsum henergy

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
