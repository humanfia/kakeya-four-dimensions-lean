/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/MatchingBand.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SheetBridge

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set Metric

/-- A measurable real extension of a matching sheet's trace on the half ball. -/
noncomputable def realSheetExtension (φ : EuclideanSpace ℂ (Fin 3) → ℂ) :
    EuclideanSpace ℝ (Fin 3) → ℝ := by
  classical
  exact (closedBall 0 (1 / 2)).piecewise (fun z => (φ (emb z)).re) (fun _ => 0)

theorem measurable_realSheetExtension {φ : EuclideanSpace ℂ (Fin 3) → ℂ}
    (hφ : IsMatchSheet φ) : Measurable (realSheetExtension φ) := by
  classical
  exact (Complex.continuous_re.comp_continuousOn (continuousOn_sheet_emb hφ)).measurable_piecewise
    continuous_const.continuousOn measurableSet_closedBall

theorem norm_sub_realSheetExtension {φ : EuclideanSpace ℂ (Fin 3) → ℂ}
    (hφ : IsMatchSheet φ) {z : EuclideanSpace ℝ (Fin 3)} (hz : ‖z‖ ≤ 1 / 2)
    (w : ℝ) : ‖φ (emb z) - (w : ℂ)‖ = |realSheetExtension φ z - w| := by
  classical
  have hzmem : z ∈ closedBall 0 (1 / 2) := mem_closedBall_zero_iff.mpr hz
  have hreal := hφ.2.2 z (by linarith)
  have heq : φ (emb z) - (w : ℂ) = (((φ (emb z)).re - w : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, realSheetExtension,
    piecewise_eq_of_mem _ _ _ hzmem]

namespace PairTests

variable {En Fr Ω : Type*} [Fintype En] [MeasurableSpace Ω]
  (T : PairTests En Fr Ω)

/-- A band in matching coordinates is charged to the same original frame law.
Only the volume of one grid ball is paid; no count of sheet labels appears. -/
theorem matching_band_bound
    (cap : Fr → ℝ → ℝ)
    (hband : ∀ (f : Fr) (ρ : ℝ) (U : Set (EuclideanSpace ℝ (Fin 3)))
      (g : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < ρ → MeasurableSet U → Measurable g →
      T.Pm {p | T.frameOf (T.src p) = f ∧ T.z p ∈ U ∧ |T.w p - g (T.z p)| ≤ ρ} ≤
        ENNReal.ofReal (cap f ρ) * volume U)
    (i : En × ↥(gridBox T.h (1 / 8)) × Bool) {ρ : ℝ} (hρ : 0 < ρ) :
    T.Pm {p | T.toDiscSetup.lab (T.toDiscSetup.src p) = T.toDiscSetup.lab i ∧
      ‖T.toDiscSetup.φ i (emb (T.toDiscSetup.x p)) - (T.toDiscSetup.w p : ℂ)‖ ≤ ρ} ≤
      ENNReal.ofReal (cap (T.frameOf i.1) ρ) *
        volume (closedBall (gridCenter T.h i.2.1.1) T.h) := by
  let c := gridCenter T.h i.2.1.1
  let g : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun z => realSheetExtension (T.sheet i) ((2 * T.r)⁻¹ • (z - c))
  have hsheet : IsMatchSheet (T.sheet i) := T.toDiscSetup.sheet i
  have hg : Measurable g := (measurable_realSheetExtension hsheet).comp (by fun_prop)
  refine (measure_mono ?_).trans (hband (T.frameOf i.1) ρ (closedBall c T.h) g hρ
    measurableSet_closedBall hg)
  rintro p ⟨hlab, hnear⟩
  change (T.frameOf (T.src p), (T.cell p).val) = (T.frameOf i.1, i.2.1.val) at hlab
  have hf := congrArg Prod.fst hlab
  have hcell := congrArg Prod.snd hlab
  have hcenter : T.center p = c := congrArg (gridCenter T.h) hcell
  refine ⟨hf, ?_, ?_⟩
  · rw [mem_closedBall_iff_norm, ← hcenter]
    exact T.norm_z_sub_center p
  · have hx : T.xm p = (2 * T.r)⁻¹ • (T.z p - c) := by
      simp only [xm, hcenter]
    change ‖T.sheet i (emb (T.xm p)) - (T.w p : ℂ)‖ ≤ ρ at hnear
    rw [norm_sub_realSheetExtension hsheet (z := T.xm p) (T.toDiscSetup.x_mem p)
      (T.w p)] at hnear
    simpa only [g, ← hx, abs_sub_comm] using hnear

end PairTests

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
