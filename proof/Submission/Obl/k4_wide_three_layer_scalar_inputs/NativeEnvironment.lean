import Submission.Obl.k4_wide_three_layer_scalar_inputs.Model
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Caps
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Blocks
import Submission.Obl.k4_scalar_capped_heavy_potential.GroupPruning

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter

noncomputable section

/-- One common range contains any finite family of positive exponents
and their reciprocals. -/
theorem exists_common_exponent_range {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ R : ℝ, 1 < R ∧ ∀ i, R⁻¹ ≤ a i ∧ a i ≤ R := by
  let R := 2 + ∑ i, (a i + (a i)⁻¹)
  have hsum : 0 ≤ ∑ i, (a i + (a i)⁻¹) := Finset.sum_nonneg fun i _ => (add_pos (ha i) (inv_pos.mpr (ha i))).le
  have hR : 1 < R := by dsimp [R]; linarith
  refine ⟨R, hR, fun i => ?_⟩
  have hi : a i + (a i)⁻¹ ≤ ∑ j, (a j + (a j)⁻¹) :=
    Finset.single_le_sum (f := fun j => a j + (a j)⁻¹)
      (fun j _ => (add_pos (ha j) (inv_pos.mpr (ha j))).le) (Finset.mem_univ i)
  constructor
  · apply (inv_le_comm₀ (by linarith : 0 < R) (ha i)).mpr
    dsimp [R]
    linarith [ha i]
  · dsimp [R]
    linarith [inv_pos.mpr (ha i)]

/-- A fixed cap range contains all resolutions needed by the field and
agreement, including the entire varying hidden-window interval. -/
theorem exists_native_cap_range {s u B v₀ : ℝ}
    (hs : 0 < s) (hu : 0 ≤ u) (hB : 0 < B) (hv₀ : 0 < v₀) :
    ∃ R : ℝ, 1 < R ∧ R⁻¹ ≤ s ∧ s ≤ R ∧
      R⁻¹ ≤ 10 * B ∧ 10 * B ≤ R ∧ R⁻¹ ≤ B ∧ B ≤ R ∧
      R⁻¹ ≤ v₀ ∧ v₀ ≤ R ∧ s + u ≤ R := by
  obtain ⟨R, hR, hb⟩ := exists_common_exponent_range
    (![s, 10 * B, B, v₀, s + u] : Fin 5 → ℝ) (by
      intro i
      fin_cases i
      · exact hs
      · change 0 < 10 * B
        positivity
      · exact hB
      · exact hv₀
      · change 0 < s + u
        linarith)
  have h₀ := hb 0
  have h₁ := hb 1
  have h₂ := hb 2
  have h₃ := hb 3
  have h₄ := hb 4
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four] at h₀ h₁ h₂ h₃ h₄
  exact ⟨R, hR, h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2, h₄.2⟩

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Finiteness follows from the original probability prior, product
ceiling and unit-time support, independently of the rate. -/
theorem Valid.native_incidence_finite (hv : cfg.Valid) (k : ℕ) : IsFiniteMeasure (cfg.μ k) := by
  let _ : IsProbabilityMeasure (cfg.ν k) := (hv.basic k).2.1
  obtain ⟨-, -, -, hdom, -, hnull, -⟩ := hv.basic k
  apply Submission.Obl.k4_scalar_capped_heavy_potential.finite_incidence_of_time_support
    (cfg.ν k) (cfg.μ k) (ENNReal.ofReal (cfg.K k)) ENNReal.ofReal_ne_top 0 1 hdom
  rw [ae_iff]
  have heq : {p : α × ℝ | p.2 ∉ Icc (0 : ℝ) 1} = (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, mem_prod, mem_univ, true_and]
  rw [heq]
  exact hnull

end Data

/-- The original caps and both true atlas levels at one index, including
actual nesting of their complete assignment sets and time intervals. -/
structure NativeEnvironment {α : Type} [MeasurableSpace α]
    (cfg : Data α) (k : ℕ) (s se R : ℝ) : Prop where
  blocks : Support.BlocksAt cfg k s R
  deep_blocks : Support.BlocksAt cfg k se R
  caps : Support.CapsAt cfg k R
  nesting : ∀ i : Fin (cfg.n k se), ∃ h : Fin (cfg.n k s),
    cfg.A k se i ⊆ cfg.A k s h ∧
    Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k se) (cfg.j k se i) ⊆
      Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s h)

/-- A fixed admissible range supplies all original analytic hypotheses
for the native step simultaneously. -/
theorem eventually_native_environment {α : Type} [MeasurableSpace α]
    {cfg : Data α} (hv : cfg.Valid) {s se R : ℝ}
    (hR : 1 < R) (hs : R⁻¹ ≤ s) (hse : s < se) (hseU : se ≤ cfg.U) :
    ∀ᶠ k in atTop, NativeEnvironment cfg k s se R := by
  filter_upwards [Support.blocksAt_eventually hv.atlas hv.horizontal_rate hR,
    Support.capsAt_eventually hv.caps hR, hv.nested R hR] with k hB hcap hnest
  exact ⟨hB s hs (hse.le.trans hseU), hB se (hs.trans hse.le) hseU,
    hcap, hnest s se hs hse hseU⟩

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
