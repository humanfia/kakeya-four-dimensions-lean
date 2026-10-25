import Mathlib
import ChallengeDeps
import Submission.Obl.k4_finite_row_graph_assembly.Selection
import Submission.Obl.k4_matching_switching_target_certificate.JetBins

namespace Submission.Obl.k4_original_prior_line_extraction

open MeasureTheory Set Filter
open scoped ENNReal

/-- Removing order zero forces a positive-order jet in one of the supplied directions. -/
lemma finite_jet_witness {A : Type*} (V : Finset A) (K : ℕ)
    (H : A → ℕ → ℝ) {c L u : ℝ} (hc : 0 < c) (hL : 0 < L) (hu : 0 ≤ u)
    (hzero : ∀ v ∈ V, |H v 0| ≤ u)
    (hsmall : ((V.card : ℝ) + 1) * u ≤ c * L / 2)
    (hsum : c * L ≤ ∑ v ∈ V, ∑ j ∈ Finset.range (K + 1), |H v j|) :
    ∃ v ∈ V, ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧
      c / (4 * ((V.card : ℝ) + 1) * (K + 1)) * L ≤ |H v j| := by
  classical
  let D : ℝ := (V.card : ℝ) + 1
  let b : ℝ := c / (4 * D * (K + 1))
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hb : 0 < b := div_pos hc (by positivity)
  by_contra h
  push_neg at h
  have hterm (v : A) (hv : v ∈ V) :
      (∑ j ∈ Finset.range (K + 1), |H v j|) ≤ u + (K + 1) * (b * L) := by
    rw [Finset.sum_range_succ']
    calc
      (∑ j ∈ Finset.range K, |H v (j + 1)|) + |H v 0| ≤
          (∑ _j ∈ Finset.range K, b * L) + u := by
        gcongr with j hj
        · exact (h v hv (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)).le
        · exact hzero v hv
      _ ≤ u + (K + 1) * (b * L) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hpos : 0 ≤ b * L := by positivity
        push_cast
        nlinarith
  have hupper : (∑ v ∈ V, ∑ j ∈ Finset.range (K + 1), |H v j|) ≤
      D * u + D * (K + 1) * (b * L) := by
    calc
      _ ≤ ∑ _v ∈ V, (u + (K + 1) * (b * L)) := Finset.sum_le_sum hterm
      _ = (V.card : ℝ) * (u + (K + 1) * (b * L)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D * u + D * (K + 1) * (b * L) := by
        have hpos : 0 ≤ (K + 1 : ℝ) * (b * L) := by positivity
        dsimp [D]
        nlinarith
  have hcancel : D * (K + 1) * (b * L) = c * L / 4 := by
    dsimp [b]
    field_simp
    <;> ring
  rw [hcancel] at hupper
  change D * u ≤ c * L / 2 at hsmall
  have : 0 < c * L := mul_pos hc hL
  linarith

/-- Finite measurable selection loses at most one fixed direction-count factor. -/
lemma select_mass_event {A Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V : Finset A) (E : A → Set Ω)
    (hcover : ∀ᵐ p ∂μ, p ∈ ⋃ v ∈ V, E v)
    {q : ℝ} (hq : 0 < q) (hmass : ENNReal.ofReal q ≤ μ univ) :
    ∃ v ∈ V, ENNReal.ofReal (q / ((V.card : ℝ) + 1)) ≤ μ (E v) := by
  classical
  have hsum : ENNReal.ofReal q ≤ ∑ v ∈ V, μ (E v) := by
    calc
      ENNReal.ofReal q ≤ μ univ := hmass
      _ ≤ μ (⋃ v ∈ V, E v) := measure_mono_ae (hcover.mono fun p hp _ => hp)
      _ ≤ ∑ v ∈ V, μ (E v) := measure_biUnion_finset_le V E
  have hsumReal : q ≤ ∑ v ∈ V, (μ (E v)).toReal := by
    have := ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr fun v _ => measure_ne_top μ (E v)) hsum
    simpa only [ENNReal.toReal_ofReal hq.le,
      ENNReal.toReal_sum (fun v _ => measure_ne_top μ (E v))] using this
  have hV : V.Nonempty := by
    by_contra h
    have hempty : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, Finset.sum_empty] at hsumReal
    linarith
  obtain ⟨v, hv, hbig⟩ := Submission.Obl.k4_finite_row_graph_assembly.exists_ge_avg
    V (fun v => (μ (E v)).toReal) q hV hsumReal
  refine ⟨v, hv, ?_⟩
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E v))]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans _ hbig
  have hcard : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  exact div_le_div_of_nonneg_left hq.le hcard (by linarith)

end Submission.Obl.k4_original_prior_line_extraction
