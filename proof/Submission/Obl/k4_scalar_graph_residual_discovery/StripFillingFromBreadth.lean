/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file StripFillingFromBreadth.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.AssignedStripFilling
import Submission.Obl.k4_scalar_graph_residual_discovery.PlanarBreadth

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped NNReal ENNReal
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- The actual independent breadth in every assigned base cell supplies
the determinant-success input for strip filling. The cell masses and
trajectory prior remain unnormalized. -/
theorem assigned_strip_filling_of_cell_breadth
    (θ : Measure ScalarLine) [IsFiniteMeasure θ]
    (inc : Measure ScalarIncidence) [IsFiniteMeasure inc]
    {C K ρ p b vsep H D L : ℝ} (hC : 0 ≤ C) (hMK : FiniteMK 2 C)
    (hK : 0 < K) (hρ : 0 < ρ) (hp : 0 < p) (hb : 0 < b) (hbp : b ≤ p)
    (hvsep : 0 < vsep) (hH : 0 ≤ H) (hL : 0 < L)
    (U : ℝ≥0) (hU : 3 * (U : ℝ) ≤ K) (hinc : inc ≤ U • θ.prod volume)
    (Λ : Set ScalarLine) (hΛ : MeasurableSet Λ) (hΛbound : ∀ l ∈ Λ, |l.2 0| ≤ H)
    (s : Finset (Fin 2 → ℤ))
    (hER : ∀ q ∈ s, baseSquare p q ⊆ Metric.closedBall 0 D)
    (hcover : ∀ᵐ z ∂inc, ∃ q ∈ s, z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q)
    (hpositive : inc univ ≠ 0)
    (hprior : (θ Λ).toReal ≤ K * (inc univ).toReal / ρ)
    (hvelocity : ∀ᵐ z ∂inc, |z.1.2 1| ≤ H)
    (hcap : ∀ q ∈ s, ∀ w,
      (inc.restrict {z | z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q})
        {z | |z.1.2 1 - w| ≤ vsep} ≤
          (1 / 2 : ℝ≥0∞) * inc {z | z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q})
    (hbudget : 200 * C * K ^ 4 * (1 + H) ^ 2 ≤ L * vsep) :
    (ρ / p) ^ 2 / L ≤ (s.card : ℝ) := by
  classical
  let A (q : Fin 2 → ℤ) := {z : ScalarIncidence |
    z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q}
  have hA (q : Fin 2 → ℤ) : MeasurableSet (A q) :=
    (hΛ.preimage measurable_fst).inter
      ((measurable_baseObservation b) (measurableSet_baseSquare p q))
  have hdisj : (↑s : Set (Fin 2 → ℤ)).PairwiseDisjoint A := by
    intro q _ q' _ hne
    apply disjoint_left.mpr
    intro z hz hz'
    exact (disjoint_left.mp (pairwiseDisjoint_baseSquare hp (mem_univ q) (mem_univ q') hne))
      hz.2 hz'.2
  have hUnion : inc (⋃ q ∈ s, A q) = inc univ := by
    apply le_antisymm (measure_mono (subset_univ _))
    apply measure_mono_ae
    filter_upwards [hcover] with z hz
    intro _
    obtain ⟨q, hq, hzq⟩ := hz
    exact mem_biUnion hq hzq
  have hsumMass : (∑ q ∈ s, inc (A q)) = inc univ := by
    rw [← measure_biUnion_finset hdisj (fun q _ => hA q)]
    exact hUnion
  let m (q : Fin 2 → ℤ) := (inc (A q)).toReal
  have hsumReal : (∑ q ∈ s, m q) = (inc univ).toReal := by
    change (∑ q ∈ s, (inc (A q)).toReal) = _
    rw [← ENNReal.toReal_sum (fun q _ => measure_ne_top inc (A q)), hsumMass]
  have hm : 0 < ∑ q ∈ s, m q := by
    rw [hsumReal]
    exact ENNReal.toReal_pos hpositive (measure_ne_top inc univ)
  have hprior' : (θ Λ).toReal ≤ K * (∑ q ∈ s, m q) / ρ := by
    rw [hsumReal]
    exact hprior
  have hV : Measurable (fun z : ScalarIncidence => z.1.2 1) := by fun_prop
  have hsucc (q : Fin 2 → ℤ) (hq : q ∈ s) :
      ENNReal.ofReal ((1 / 2 : ℝ) * m q ^ 2) ≤
        Measure.pi (fun _ : Fin 2 => inc)
          {z | (∀ i, (z i).1 ∈ Λ ∧ baseObservation b (z i) ∈ baseSquare p q) ∧
            vsep / (1 + H) ^ 2 ≤
              |Matrix.det (Matrix.of fun i j : Fin 2 => BaseLine.direction ((z i).1.2 1) j)|} := by
    have hh := planar_cell_determinant_mass inc (A q) (hA q) (fun z => z.1.2 1) hV hH hvsep.le
      (hvelocity.filter_mono (ae_mono Measure.restrict_le_self)) (hcap q hq)
    have hleft : ENNReal.ofReal ((1 / 2 : ℝ) * m q ^ 2) =
        (1 / 2 : ℝ≥0∞) * (inc (A q)) ^ 2 := by
      dsimp only [m]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top inc (A q))]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hleft]
    exact hh
  have hβ : 0 < vsep / (1 + H) ^ 2 := by positivity
  have hraw := assigned_base_strip_filling θ inc hC hMK hK hρ hp hb hbp hβ
    (by norm_num : (0 : ℝ) < 1 / 2) hH U hU hinc Λ hΛ hΛbound s m hER hm hprior' hsucc
  have hH₁ : 0 < 1 + H := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ 2 * (1 + H) ^ 2)
  have hclean : (ρ / p) ^ 2 * vsep ≤
      (200 * C * K ^ 4 * (1 + H) ^ 2) * (s.card : ℝ) := by
    convert hscaled using 1 <;> field_simp [hH₁.ne'] <;> ring
  have hcount : (ρ / p) ^ 2 ≤ L * (s.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hvsep).mp
    calc
      (ρ / p) ^ 2 * vsep ≤ (200 * C * K ^ 4 * (1 + H) ^ 2) * (s.card : ℝ) := hclean
      _ ≤ (L * vsep) * (s.card : ℝ) := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)
      _ = (L * (s.card : ℝ)) * vsep := by ring
  exact (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hcount)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
