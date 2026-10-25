/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, GroupBudget.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupDefs

/-! Finite group boxes, the total reference budget of the groups, and clamped
hidden coefficients (globally bounded, equal to the hidden coefficients on
the good set). -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_coefficient_clustering

theorem norm_coeff_le (x : Coeff) : ‖x‖ ≤ |x 0| + |x 1| + |x 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  have h2 := abs_nonneg (x 2)
  rw [show |x 0| + |x 1| + |x 2| = Real.sqrt ((|x 0| + |x 1| + |x 2|) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_abs (x 0), sq_abs (x 1), sq_abs (x 2), mul_nonneg h0 h1, mul_nonneg h1 h2,
    mul_nonneg h0 h2]

theorem floor_mem_Icc_ceil {x K a : ℝ} (ha : 0 < a) (hx : |x| ≤ K) :
    ⌊x / a⌋ ∈ Finset.Icc (-⌈K / a⌉) ⌈K / a⌉ := by
  have hb := abs_le.mp hx
  apply Finset.mem_Icc.mpr
  constructor
  · have : ⌊-K / a⌋ ≤ ⌊x / a⌋ := Int.floor_mono (div_le_div_of_nonneg_right hb.1 ha.le)
    rw [neg_div, Int.floor_neg] at this
    exact this
  · exact (Int.floor_mono (div_le_div_of_nonneg_right hb.2 ha.le)).trans (Int.floor_le_ceil _)

/-- The finite box of groups met by bounded trajectories. -/
def groupBox (K a δ : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-⌈K / a⌉) ⌈K / a⌉ ×ˢ (Finset.Icc (-⌈K / a⌉) ⌈K / a⌉ ×ˢ
    Finset.Icc (-⌈K / δ⌉) ⌈K / δ⌉)

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

theorem groupCode_mem_groupBox {k : ℕ} {s a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) {p : α × ℝ}
    (hp : p ∈ cfg.goodSet k s) : cfg.groupCode k a δ p.1 ∈ groupBox (cfg.K k) a δ := by
  obtain ⟨_, h0, h1, h3, -⟩ := hp
  exact Finset.mem_product.mpr ⟨floor_mem_Icc_ceil ha h0,
    Finset.mem_product.mpr ⟨floor_mem_Icc_ceil ha h1, floor_mem_Icc_ceil hδ h3⟩⟩

theorem groupWeight_nonneg (k : ℕ) (a δ : ℝ) (g : ℤ × ℤ × ℤ) : 0 ≤ cfg.groupWeight k a δ g := by
  unfold groupWeight
  positivity

/-- The total original reference budget of all groups in the box. -/
theorem groupBox_weight_sum (k : ℕ) [IsProbabilityMeasure (cfg.π k)] {a δ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 < δ) (hK : 1 ≤ cfg.K k) :
    ∑ g ∈ groupBox (cfg.K k) a δ, cfg.groupWeight k a δ g ≤ 25 * cfg.K k ^ 2 := by
  set A := Finset.Icc (-⌈cfg.K k / a⌉) ⌈cfg.K k / a⌉
  set V := Finset.Icc (-⌈cfg.K k / δ⌉) ⌈cfg.K k / δ⌉
  have hfloor : Measurable (fun w : ℝ => ⌊w / δ⌋) := Int.measurable_floor.comp (measurable_id.div_const δ)
  have hV : ∑ v ∈ V, (cfg.π k).real {w : ℝ | ⌊w / δ⌋ = v} ≤ 1 := by
    have hh := sum_measureReal_preimage_singleton (μ := cfg.π k) V
      (f := fun w : ℝ => ⌊w / δ⌋) (fun v _ => hfloor (measurableSet_singleton v))
    have heq : ∀ v, (fun w : ℝ => ⌊w / δ⌋) ⁻¹' {v} = {w : ℝ | ⌊w / δ⌋ = v} := fun v => rfl
    simp only [heq] at hh
    rw [hh]
    exact (measureReal_mono (subset_univ _)).trans (by simp)
  have hcard : ((A.card : ℝ)) * a ≤ 5 * cfg.K k := by
    have hc : (A.card : ℝ) = 2 * ⌈cfg.K k / a⌉ + 1 := by
      simp only [A, Int.card_Icc]
      have hpos : 0 ≤ ⌈cfg.K k / a⌉ := Int.ceil_nonneg (div_nonneg (by linarith) ha.le)
      have hnat : ((⌈cfg.K k / a⌉ + 1 - -⌈cfg.K k / a⌉).toNat : ℤ) =
          2 * ⌈cfg.K k / a⌉ + 1 := by
        rw [Int.toNat_of_nonneg (by omega)]; ring
      exact_mod_cast hnat
    have hceil : (⌈cfg.K k / a⌉ : ℝ) ≤ cfg.K k / a + 1 := (Int.ceil_lt_add_one _).le
    rw [hc]
    have : (2 * (⌈cfg.K k / a⌉ : ℝ) + 1) * a ≤ (2 * (cfg.K k / a + 1) + 1) * a :=
      mul_le_mul_of_nonneg_right (by linarith) ha.le
    calc
      _ ≤ (2 * (cfg.K k / a + 1) + 1) * a := this
      _ = 2 * cfg.K k + 3 * a := by field_simp; ring
      _ ≤ _ := by linarith
  calc
    ∑ g ∈ groupBox (cfg.K k) a δ, cfg.groupWeight k a δ g =
        ∑ x ∈ A, ∑ y ∈ A, ∑ v ∈ V, a ^ 2 * (cfg.π k).real {w : ℝ | ⌊w / δ⌋ = v} := by
      unfold groupBox groupWeight
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_product]
    _ = (A.card : ℝ) * ((A.card : ℝ) * (a ^ 2 * ∑ v ∈ V,
        (cfg.π k).real {w : ℝ | ⌊w / δ⌋ = v})) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (A.card : ℝ) * ((A.card : ℝ) * (a ^ 2 * 1)) := by gcongr
    _ = ((A.card : ℝ) * a) ^ 2 := by ring
    _ ≤ (5 * cfg.K k) ^ 2 := by gcongr
    _ = 25 * cfg.K k ^ 2 := by ring

/-- Hidden coefficients clamped to the native bounds of the good set. -/
def clampedCoeff (k : ℕ) (l : α) : Coeff :=
  if |cfg.b k l 2| ≤ cfg.K k ∧ |cfg.b k l 5| ≤ 2 * cfg.K k then cfg.hiddenCoeff k l else 0

theorem measurable_clampedCoeff (k : ℕ) (hb : Measurable (cfg.b k)) :
    Measurable (cfg.clampedCoeff k) := by
  have hc (i : Fin 6) : Measurable (fun l : α => cfg.b k l i) := (measurable_pi_apply i).comp hb
  apply Measurable.ite _ (cfg.measurable_hiddenCoeff k hb) measurable_const
  exact (measurableSet_le (hc 2).abs measurable_const).inter
    (measurableSet_le (hc 5).abs measurable_const)

theorem norm_clampedCoeff_le (k : ℕ) (hK : 0 ≤ cfg.K k) (l : α) :
    ‖cfg.clampedCoeff k l‖ ≤ 3 * cfg.K k := by
  unfold clampedCoeff
  split_ifs with hl
  · refine (norm_coeff_le _).trans ?_
    rw [cfg.hiddenCoeff_apply_zero, cfg.hiddenCoeff_apply_one, cfg.hiddenCoeff_apply_two,
      abs_zero]
    linarith [hl.1, hl.2]
  · simp only [norm_zero]
    linarith

theorem clampedCoeff_of_good {k : ℕ} {s : ℝ} {p : α × ℝ} (hp : p ∈ cfg.goodSet k s) :
    cfg.clampedCoeff k p.1 = cfg.hiddenCoeff k p.1 := by
  obtain ⟨_, -, -, -, -, h2, h5, -⟩ := hp
  simp [clampedCoeff, h2, h5]

theorem clampedCoeff_apply_two (k : ℕ) (l : α) : cfg.clampedCoeff k l 2 = 0 := by
  unfold clampedCoeff
  split_ifs
  · exact cfg.hiddenCoeff_apply_two k l
  · rfl

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
