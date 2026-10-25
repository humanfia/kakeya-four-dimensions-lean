import Submission.Obl.k4_tempered_grid_selection.Interface

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set Filter
open scoped ENNReal

lemma subpower_mul {N K L : ℕ → ℝ} (hN : ∀ k, 0 < N k)
    (hK : Subpower N K) (hL : Subpower N L) :
    Subpower N (fun k => K k * L k) := by
  constructor
  · intro k
    nlinarith [hK.1 k, hL.1 k]
  · intro ε hε
    filter_upwards [hK.2 (ε / 2) (by linarith), hL.2 (ε / 2) (by linarith)] with k hk hl
    calc
      K k * L k ≤ N k ^ (ε / 2) * N k ^ (ε / 2) :=
        mul_le_mul hk hl (by linarith [hL.1 k]) (Real.rpow_nonneg (hN k).le _)
      _ = N k ^ ε := by rw [← Real.rpow_add (hN k)]; congr 1; ring

lemma inverse_mass_after_finite_loss {K : ℝ} {B : ℕ} {m m₀ : ℝ≥0∞}
    (hK : 0 < K) (hB : 0 < B) (hlo : ENNReal.ofReal K⁻¹ ≤ m)
    (hloss : m ≤ (B : ℝ≥0∞) * m₀) :
    ENNReal.ofReal (K * (B : ℝ))⁻¹ ≤ m₀ := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hBne : (B : ℝ≥0∞) ≠ 0 := by exact_mod_cast hB.ne'
  calc
    ENNReal.ofReal (K * (B : ℝ))⁻¹ =
        (B : ℝ≥0∞)⁻¹ * ENNReal.ofReal K⁻¹ := by
      rw [mul_inv_rev, ENNReal.ofReal_mul (inv_nonneg.mpr hB0.le),
        ENNReal.ofReal_inv_of_pos hB0, ENNReal.ofReal_natCast]
    _ ≤ (B : ℝ≥0∞)⁻¹ * ((B : ℝ≥0∞) * m₀) :=
      mul_le_mul_right (hlo.trans hloss) _
    _ = m₀ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hBne (by finiteness), one_mul]

lemma measurable_label_selection (n : ℝ) (H : ℕ) (R U : ℝ)
    {E : Set Incidence} (hE : MeasurableSet E) (T : Set Label) :
    MeasurableSet (E ∩ commonLabel n H R U ⁻¹' T) :=
  hE.inter ((Set.to_countable T).measurableSet.preimage (measurable_commonLabel n H R U))

lemma incidence_selection_mass (ν : Measure (ℕ × (Fin 6 → ℝ)))
    (E : Set Incidence) (n : ℝ) (H : ℕ) (R U : ℝ) (T : Set Label) :
    incidenceMeasure ν E (commonLabel n H R U ⁻¹' T) =
      incidenceMeasure ν (E ∩ commonLabel n H R U ⁻¹' T) univ := by
  rw [incidenceMeasure, Measure.restrict_apply
    ((Set.to_countable T).measurableSet.preimage (measurable_commonLabel n H R U)),
    incidenceMeasure, Measure.restrict_apply_univ, inter_comm]

lemma incidence_selection_le (ν : Measure (ℕ × (Fin 6 → ℝ)))
    (E : Set Incidence) (n : ℝ) (H : ℕ) (R U : ℝ) (T : Set Label) :
    incidenceMeasure ν (E ∩ commonLabel n H R U ⁻¹' T) ≤ incidenceMeasure ν E :=
  Measure.restrict_mono_set _ inter_subset_left

end Submission.Obl.k4_tempered_grid_selection
