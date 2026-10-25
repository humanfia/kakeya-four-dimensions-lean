import Submission.Obl.k4_conditional_common_affine_field.VelocityWitnesses
import Submission.Obl.k4_critical_conditional_row_preparation.Pruning

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarCoreTools.Finalization
open Submission.Obl.k4_critical_conditional_row_preparation

/-- Forgetting the fine state gives an unconditional ceiling against the same
palette and the original total mass. -/
theorem unconditional_code_palette {Ω Q V : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (code : Ω → V) (hc : Measurable code) (π : Measure V) (C : ℝ≥0∞)
    (hcap : ∀ q j, μ {p | state p=q ∧ code p=j} ≤ C*μ {p | state p=q}*π {j}) :
    μ.map code ≤ (C*μ univ) • π := by
  have hrect := rectangular_palette_caps_of_atoms μ state hs code hc π C hcap
  have hglobal := coarsen_palette_cap μ state hs code hc π
    (fun _ => (0 : Fin 1)) measurable_const C hrect (0 : Fin 1)
  refine Measure.le_iff.mpr ?_
  intro A hA
  rw [Measure.map_apply hc hA,Measure.smul_apply,smul_eq_mul]
  simpa only [Set.preimage,true_and,Set.ofPred_true] using hglobal A hA

/-- The old conditional palette bound controls thin neighborhoods of every axis
even after later fiber and anchor selections. -/
theorem original_velocity_pencil_cap {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (v : Ω → ℝ) (hv : Measurable v) (π : Measure ℝ)
    (δ r K S : ℝ) (hδ : 0 < δ) (hδr : δ ≤ r) (hr1 : 4*r ≤ 1) (hK : 0 ≤ K)
    (hpalette : ∀ x s : ℝ, δ ≤ s → s ≤ 1 →
      π (Icc (x-s) (x+s)) ≤ ENNReal.ofReal (K*s^S))
    (hcap : ∀ q j, μ {p | state p=q ∧ ⌊v p/δ⌋=j} ≤
      ENNReal.ofReal K*μ {p | state p=q}*
        π (Ico ((j : ℝ)*δ) (((j : ℝ)+1)*δ))) :
    ∀ w : ℝ, μ {p | |v p-w| < r} ≤ ENNReal.ofReal (K^2*(4*r)^S)*μ univ := by
  let code : Ω → ℤ := fun p => ⌊v p/δ⌋
  have hc : Measurable code := (hv.div_const δ).floor
  let center : ℤ → ℝ := fun j => δ*(j : ℝ)
  have hcenter : Measurable center := measurable_of_countable _
  let πc := π.map (fun x : ℝ => ⌊x/δ⌋)
  have hπm : Measurable (fun x : ℝ => ⌊x/δ⌋) := (measurable_id.div_const δ).floor
  have hπc (j : ℤ) : πc {j} = π (Ico ((j : ℝ)*δ) (((j : ℝ)+1)*δ)) := by
    change π.map (fun x : ℝ => ⌊x/δ⌋) {j} = _
    rw [Measure.map_apply hπm (measurableSet_singleton j)]
    exact congrArg π (floor_bin_eq_Ico δ j hδ)
  have hdom := unconditional_code_palette μ state hs code hc πc (ENNReal.ofReal K)
    (fun q j => by simpa only [hπc] using hcap q j)
  have hround := Measure.map_mono hdom hcenter
  rw [Measure.map_smul _ hcenter.aemeasurable,Measure.map_map hcenter hc] at hround
  intro w
  let B : Set ℝ := {z | |z-w| < 2*r}
  have hB : MeasurableSet B :=
    measurableSet_lt (measurable_id.sub_const w).abs measurable_const
  have hsub : {p | |v p-w| < r} ⊆ (center ∘ code) ⁻¹' B := by
    intro p hp
    have hnear : |center (code p)-v p| ≤ δ := by
      simpa only [center,code,abs_sub_comm] using floor_scaled_error hδ (v p)
    have h := (abs_sub_le (center (code p)) (v p) w).trans (add_le_add hnear hp.le)
    change |center (code p)-w| < 2*r
    have hstrict := (abs_sub_le (center (code p)) (v p) w).trans_lt
      (add_lt_add_of_le_of_lt hnear hp)
    linarith
  have hthin : (πc.map center) B ≤ ENNReal.ofReal (K*(4*r)^S) := by
    have h := rounded_palette_thin π δ (2*r) K S hδ (by linarith)
      (by nlinarith only [hr1]) hpalette w
    simpa only [show 2*(2*r)=4*r by ring] using h
  calc
    _ ≤ μ ((center ∘ code) ⁻¹' B) := measure_mono hsub
    _ = (μ.map (center ∘ code)) B := (Measure.map_apply (hcenter.comp hc) hB).symm
    _ ≤ (ENNReal.ofReal K*μ univ)*((πc.map center) B) := hround B
    _ ≤ (ENNReal.ofReal K*μ univ)*ENNReal.ofReal (K*(4*r)^S) := mul_le_mul' le_rfl hthin
    _ = _ := by
      rw [mul_right_comm,← ENNReal.ofReal_mul hK]
      congr 2
      ring

end Submission.Obl.k4_conditional_common_affine_field
