/- Adapted from our LOT tree o211, session x0736, commit fb9fb2638e83e4e42cdf985859ec4b5deb228222,
Submission/Obl/k4_critical_affine_derivative_preparation/ClippedJointCap.lean. -/

import Submission.Obl.k4_critical_conditional_row_preparation.NativeNormalization
import Submission.Obl.k4_critical_conditional_row_preparation.JointScales

namespace Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

def rowPositionCode {α : Type*} (ξ : ℝ) (b v : α → ℝ) (p : α × ℝ) : Fin 2 → ℤ :=
  fun e => ⌊(![p.2, b p.1 + p.2 * v p.1] : Fin 2 → ℝ) e / ξ⌋

theorem rowPositionCode_cell_eq {α : Type*} (ξ : ℝ) (b v : α → ℝ)
    (q : Fin 2 → ℤ) (j : ℤ) :
    {p : α × ℝ | rowPositionCode ξ b v p = q ∧ ⌊v p.1 / ξ⌋ = j} =
    {p | ⌊p.2 / ξ⌋ = q 0 ∧ ⌊(b p.1 + p.2 * v p.1) / ξ⌋ = q 1 ∧ ⌊v p.1 / ξ⌋ = j} := by
  ext p
  constructor
  · rintro ⟨hq, hj⟩
    exact ⟨congrFun hq 0, congrFun hq 1, hj⟩
  · rintro ⟨h₀, h₁, hj⟩
    refine ⟨?_, hj⟩
    funext e
    fin_cases e
    · exact h₀
    · exact h₁

theorem measurableSet_rowPositionCode_cell
    {α : Type*} [MeasurableSpace α] (ξ : ℝ) (b v : α → ℝ)
    (hb : Measurable b) (hv : Measurable v) (q : Fin 2 → ℤ) (j : ℤ) :
    MeasurableSet {p : α × ℝ | rowPositionCode ξ b v p = q ∧ ⌊v p.1 / ξ⌋ = j} := by
  have hz : Measurable (fun p : α × ℝ => (![p.2, b p.1 + p.2 * v p.1] : Fin 2 → ℝ)) := by
    apply Measurable.of_eval
    intro e
    fin_cases e <;> dsimp <;> fun_prop
  have hc : Measurable (rowPositionCode ξ b v) := by
    apply Measurable.of_eval
    intro e
    exact Int.measurable_floor.comp (((measurable_pi_apply e).comp hz).div_const ξ)
  exact (hc (measurableSet_singleton q)).inter
    ((Int.measurable_floor.comp ((hv.comp measurable_fst).div_const ξ)) (measurableSet_singleton j))

namespace Data

/-- The actual Row cell cap also holds for the globally bounded clipped
trajectory functions; clipping changes no event of the retained law. -/
theorem Valid.eventually_clipped_joint_cell_cap
    {α : Type} [MeasurableSpace α] {cfg : Data α} (h : cfg.Valid)
    (s a η : ℝ) (hs : 0 < s) (ha : 0 < a) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ (_lev : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s))
      (σ : Measure (α × ℝ)),
      σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) →
      ∀ (q : Fin 2 → ℤ) (j : ℤ),
      (ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i))⁻¹ •
        σ.map (unitTimeMap (cfg.leftTime k s i) (cfg.timeLength k s)))
        {p | rowPositionCode (cfg.N k ^ (-a)) (cfg.clippedIntercept k s i) (cfg.clippedVelocity k s i) p = q ∧
          ⌊cfg.clippedVelocity k s i p.1 / (cfg.N k ^ (-a))⌋ = j} ≤
      ENNReal.ofReal (cfg.N k ^ η * (cfg.N k ^ (-a)) ^ 2) *
        cfg.π k (Ico ((j : ℝ) * cfg.N k ^ (-a)) (((j : ℝ) + 1) * cfg.N k ^ (-a))) := by
  filter_upwards [h.eventually_normalized_label_joint_cap s a η hs ha hη] with k hk
  intro lev i σ hσ q j
  let ξ := cfg.N k ^ (-a)
  let H := cfg.timeLength k s
  let t₀ := cfg.leftTime k s i
  let Z₀ := cfg.horizontalOrigin k s i
  let W := H * (cfg.ν k).real (cfg.A k s i)
  let E := {p : α × ℝ | rowPositionCode ξ (cfg.clippedIntercept k s i) (cfg.clippedVelocity k s i) p = q ∧
    ⌊cfg.clippedVelocity k s i p.1 / ξ⌋ = j}
  let E₀ := cfg.normalizedRowCell k H t₀ Z₀ ξ q j
  have hE : MeasurableSet E := measurableSet_rowPositionCode_cell ξ _ _
    (lev.clipped_measurable h i).1 (lev.clipped_measurable h i).2 q j
  have hE₀ : MeasurableSet E₀ := cfg.measurableSet_normalizedRowCell k (h.basic k).1 H t₀ Z₀ ξ q j
  have heq : σ ((unitTimeMap t₀ H) ⁻¹' E) = σ ((unitTimeMap t₀ H) ⁻¹' E₀) := by
    apply measure_congr
    filter_upwards [lev.clipped_coordinates_ae h i σ hσ] with p hp
    simp only [E, rowPositionCode_cell_eq, E₀, normalizedRowCell, mem_preimage,
      unitTimeMap, mem_ofPred_eq, hp.1, hp.2, t₀, Z₀, H]
  have hσμ := hσ.trans (Measure.restrict_mono_measure (h.basic k).2.2.2.2.1
    (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)))
  have hcap := hk lev i σ hσμ t₀ Z₀ q j
  change (ENNReal.ofReal W⁻¹ • σ.map (unitTimeMap t₀ H)) E₀ ≤ _ at hcap
  rw [original_continuous_normalized_apply σ t₀ H W E₀ hE₀] at hcap
  change (ENNReal.ofReal W⁻¹ • σ.map (unitTimeMap t₀ H)) E ≤ _
  rw [original_continuous_normalized_apply σ t₀ H W E hE, heq]
  exact hcap

end Data

end

end Submission.Obl.k4_critical_conditional_row_preparation
