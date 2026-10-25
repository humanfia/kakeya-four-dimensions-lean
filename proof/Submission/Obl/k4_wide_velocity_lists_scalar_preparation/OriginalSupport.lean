import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Model

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set Filter

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original first three coordinates are bounded on every original
incidence, from the original trajectory prior and unit-time support. -/
theorem Valid.base_bound_ae (h : Valid cfg) (k : ℕ) :
    ∀ᵐ p ∂cfg.μ k, ∀ e : Fin 3,
      |(cfg.x k p.1 p.2 ∘ Fin.castSucc) e| ≤ 2 * cfg.K k := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hmeas : MeasurableSet {p : α × ℝ |
      |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k} := by
    apply measurableSet_le _ measurable_const
    have hb := (h.basic k).1
    fun_prop
  have hprod : ∀ᵐ p ∂(cfg.ν k).prod (volume : Measure ℝ),
      |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [(h.basic k).2.2.2.2.2.2.2.2.1] with l hl
    exact Filter.Eventually.of_forall (fun _ => hl)
  have hb : ∀ᵐ p ∂cfg.μ k,
      |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k :=
    ae_mono (h.basic k).2.2.2.1 (Measure.ae_smul_measure hprod _)
  have ht : ∀ᵐ p ∂cfg.μ k, p ∈ (univ : Set α) ×ˢ Icc (0 : ℝ) 1 := by
    apply ae_iff.mpr
    exact (h.basic k).2.2.2.2.2.1
  filter_upwards [hb, ht] with p hb ht
  have hK : 1 ≤ cfg.K k := h.loss_lower k
  have ht0 : 0 ≤ p.2 := ht.2.1
  have ht1 : p.2 ≤ 1 := ht.2.2
  have ht_abs : |p.2| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hcoord (a b : ℝ) : |a + p.2 * b| ≤ |a| + |b| := by
    calc
      _ ≤ |a| + |p.2 * b| := abs_add_le _ _
      _ = |a| + |p.2| * |b| := by rw [abs_mul]
      _ ≤ |a| + 1 * |b| := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right ht_abs (abs_nonneg _))
      _ = _ := by ring
  intro e
  fin_cases e
  · change |p.2| ≤ _
    linarith
  · change |cfg.b k p.1 0 + p.2 * cfg.b k p.1 3| ≤ _
    have hc := hcoord (cfg.b k p.1 0) (cfg.b k p.1 3)
    linarith [abs_nonneg (cfg.b k p.1 1), abs_nonneg (cfg.b k p.1 4)]
  · change |cfg.b k p.1 1 + p.2 * cfg.b k p.1 4| ≤ _
    have hc := hcoord (cfg.b k p.1 1) (cfg.b k p.1 4)
    linarith [abs_nonneg (cfg.b k p.1 0), abs_nonneg (cfg.b k p.1 3)]

end Data

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
