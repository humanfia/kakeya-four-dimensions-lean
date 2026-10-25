/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeMarkedComparison.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeCellCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeJitterAgreement
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeFrameSupport
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMeshWindow
import Submission.Obl.k4_horizontal_strict_parameter_step.MarkedPredictorPair

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

theorem sum_measurableSingletonClass {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ] :
    MeasurableSingletonClass (β ⊕ γ) := by
  refine ⟨fun x => ?_⟩
  cases x with
  | inl b =>
    have hh : MeasurableSet (Sum.inl '' ({b} : Set β) : Set (β ⊕ γ)) :=
      (measurableSet_singleton b).inl_image
    simpa only [Set.image_singleton] using hh
  | inr c =>
    have hh : MeasurableSet (Sum.inr '' ({c} : Set γ) : Set (β ⊕ γ)) :=
      (measurableSet_singleton c).inr_image
    simpa only [Set.image_singleton] using hh

attribute [local instance] sum_measurableSingletonClass

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The actual continuously distributed matching input, obtained from the
original incidence law and its observed finite labels. The same shared cell
point is used for both sheets and the original palette remains unchanged. -/
def nativeMarkedComparison {k : ℕ} [IsFiniteMeasure (cfg.π k)]
    {s ε D a χ M R re A : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)} [IsFiniteMeasure σ]
    (S : NativeComparisonSupport cfg k s σ AH)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    (hb : Measurable (cfg.b k)) (hdom : σ ≤ cfg.μ k)
    (caps : OriginalWidthCapsAt (cfg.N k) (cfg.K k) cfg.d R (cfg.μ k) (cfg.π k) (cfg.b k))
    (hre : R⁻¹ ≤ re) (hre' : re ≤ R)
    (he₀ : R⁻¹ ≤ cfg.e₀) (he₀' : cfg.e₀ ≤ R)
    (hA : cfg.N k ^ (-R) ≤ A) (hA1 : A ≤ 1)
    (L : Fin (cfg.n k s) → Fin 4 → ℝ) (hL : ∀ i (e : Fin 3), |L i e.succ| ≤ M)
    (hfit : ∀ i l, l ∈ cfg.B k s i → ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
      |cfg.b k l 2 + t * cfg.b k l 5 -
        (L i 0 + L i 1 * t + L i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
          L i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * a)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hM : 0 ≤ M)
    (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχeq : χ = cfg.N k ^ (-cfg.e₀))
    (hδ1 : cfg.N k ^ (-re) ≤ 1) (hδq : cfg.N k ^ (-re) ≤ cfg.timeLength k s)
    (hroom : 2 * χ + (3 * (3 * cfg.K k) + 4) * cfg.N k ^ (-re) ≤ D)
    (hsource : cfg.N k ^ ε * a ≤ A) (hwitness : cfg.K k * a + 2 * M * χ ≤ A)
    (hroundCell : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
      2 * (4 * B) * cfg.N k ^ (-re) + (6 * (4 * B) / D) *
        (χ + (3 * cfg.K k + 1) * cfg.N k ^ (-re)) ≤ A)
    (hroundJitter : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
      2 * B * cfg.N k ^ (-re) + (8 * B / D) *
        (3 * χ + (4 * (3 * cfg.K k) + 5) * cfg.N k ^ (-re)) ≤ A) :
    MarkedComparison (α × ℝ) (Fin S.table.count)
      (S.table.Index group (cfg.j k s)) ((Fin 3 → ℤ) × Fin (2 ^ cfg.T k s)) := by
  classical
  let T := S.table
  let frame : (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s) → ComparisonFrame :=
    fun l => nativeComparisonFrame χ (cfg.timeLength k s) D l.1 (l.2 : ℕ)
  have hframe (g : Fin 3 → ℤ) (j : Fin (2 ^ cfg.T k s)) :
      (frame (g, j)).velocity = χ * (g 0 : ℝ) := rfl
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have htpos l : 0 < (frame l).timeScale := by
    change 0 < 16 * cfg.timeLength k s
    positivity
  have hdpos l : 0 < (frame l).parameterScale := by
    change 0 < 16 * D
    positivity
  have hδ : 0 < cfg.N k ^ (-re) := Real.rpow_pos_of_pos hN _
  have hAp : 0 < A := (Real.rpow_pos_of_pos hN _).trans_le hA
  have hcontact : ∀ p ∈ S.event, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ := by
    simpa only [hχeq] using S.contact
  let win := exists_physical_mesh_window (cfg.b k) S.event hK hδ S.unit S.coefficients
  let F := Classical.choose win
  have hF := Classical.choose_spec win
  refine {
    original := σ
    finite := inferInstance
    mark := T.mark
    mark_measurable := T.mark_measurable
    base := fun p => physicalBase (cfg.b k p.1) p.2
    base_measurable := ?_
    mesh := cfg.N k ^ (-re)
    mesh_pos := hδ
    cells := F
    cells_cover := S.conull.mono (fun p hp => hF p hp)
    source := T.source group (cfg.j k s)
    witness := T.witness group (cfg.j k s)
    colour := T.colour group (cfg.j k s)
    same_colour := T.colour_source_eq_witness group (cfg.j k s)
    frame := frame
    time_pos := htpos
    parameter_pos := hdpos
    coefficients := T.comparisonPredictors group (cfg.j k s) frame hH L
    error := 4 * A
    error_pos := by positivity
    ceiling := fun l => 7 * (cfg.K k * A ^ cfg.d * binWeight (cfg.π k) χ (l.1 0))
    ceiling_nonneg := fun l => mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hAp.le _))
        (binWeight_nonneg _ _ _))
    source_cells := ?_
    witness_cells := ?_
    cell_good := ?_ }
  · apply Measurable.of_eval
    intro e
    fin_cases e
    · exact measurable_snd
    · exact (((measurable_pi_apply 0).comp hb).comp measurable_fst).add
        (measurable_snd.mul (((measurable_pi_apply 3).comp hb).comp measurable_fst))
    · exact (((measurable_pi_apply 1).comp hb).comp measurable_fst).add
        (measurable_snd.mul (((measurable_pi_apply 4).comp hb).comp measurable_fst))
  · intro i q hqF
    exact cfg.observed_tag_base_cell_cap S H hdom caps hre hre' he₀ he₀' hA hA1
      frame hframe L hL hN hK hM hD hD1 hχ hχ1 hχeq
      (T.source group (cfg.j k s)) (fun r => rfl)
      (fun p hp => (cfg.observed_source_fit H T frame L S.unit p hp).trans hsource)
      hroundCell i q
  · intro i q hqF
    exact cfg.observed_tag_base_cell_cap S H hdom caps hre hre' he₀ he₀' hA hA1
      frame hframe L hL hN hK hM hD hD1 hχ hχ1 hχeq
      (T.witness group (cfg.j k s))
      (fun r => (T.colour_source_eq_witness group (cfg.j k s) r).symm)
      (fun p hp => (cfg.observed_witness_fit H T frame hframe hχ hχeq L hL hfit
        S.unit hcontact p hp).trans hwitness) hroundCell i q
  · filter_upwards [S.conull] with p hp z hz
    have href := cfg.observed_reference_bounds H T hK hD hD1 hχ hχ1 hχeq S.coefficients
    have hg := (H.2.2.1 (T.old (T.mark p))).1 p.1 (T.decode_old p hp).1
    have hg' : ⌊cfg.b k p.1 3 / χ⌋ = group (T.old (T.mark p)) 0 ∧
        ⌊cfg.b k p.1 0 / D⌋ = group (T.old (T.mark p)) 1 ∧
        ⌊cfg.b k p.1 1 / D⌋ = group (T.old (T.mark p)) 2 := by
      simpa only [hχeq] using hg
    have hblock : p.2 ∈ Icc
        (((cfg.j k s (T.native (T.mark p)) : ℕ) : ℝ) * cfg.timeLength k s)
        ((((cfg.j k s (T.native (T.mark p)) : ℕ) : ℝ) + 1) * cfg.timeLength k s) := by
      simpa only [Data.I, Data.timeLength, div_eq_mul_inv] using (T.decode_native p hp).2
    refine ⟨nativeComparisonFrame_jitter hχ hχ1 hq hD hδ hδ1 hδq hroom
      (S.unit p hp) hblock hg' (hcontact p hp)
      ((S.coefficients p hp 0).trans (by linarith))
      ((href (T.source group (cfg.j k s) (T.mark p))).1) hz, ?_⟩
    exact cfg.observed_pair_jitter_agreement H T frame hframe (fun g j => htpos (g, j)) (fun g j => hdpos (g, j)) L hL hfit
      hN hK hM hD hD1 hχ hχ1 hχeq hδ hδ1 hsource hwitness hroundJitter
      S.unit S.coefficients hcontact p hp z hz

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
