/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeChildCalibration.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeChildWitness
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeCalibration

/-! Calibrate differences of genuine original ancestor and child entries. The
full original fourth-power witness floor and density contain the same hidden
factor, so the calibration loss is inverse-subpower. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

theorem exists_original_child_calibration :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (α : Type) [MeasurableSpace α] (cfg : Data α) (h : cfg.Prepared)
        (k : ℕ) (s₀ s : ℝ) (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
        (ip : Fin (cfg.n k s₀)) (ic : Fin (cfg.n k s)),
      cfg.A k s ic ⊆ cfg.A k s₀ ip →
      I (cfg.T k s) (cfg.j k s ic) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip) →
      ∀ δ σ B : ℝ, 0 < δ → 0 < σ → σ ≤ cfg.K k ^ 2 → 1 ≤ B →
      let q := cfg.timeLength k s
      let a := cfg.N k ^ (-s)
      let m := q ^ 4 * a ^ cfg.d / cfg.K k ^ 3
      let β := 27 * ((4 * cfg.K k + 6) * (cfg.K k * a ^ cfg.d)) * q ^ 4
      108 * cfg.K k ^ 4 * δ ≤ a →
      (∀ j n, cfg.μ k {p | baseMesh δ (originalBase (cfg.b k p.1) p.2) = j ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / a⌋ = n} ≤
          ENNReal.ofReal ((cfg.K k * a ^ cfg.d) * δ ^ 3)) →
      (∀ e, (∑ j, |nativeFrameMatrix q (cfg.c k s ic 1)
        (-cfg.c k s ic 3 - cfg.c k s ic 4 * cfg.c k s ic 1) (cfg.c k s ic 4) e j| * δ) ≤ σ) →
      L * nativeCalibrationLoss C (cfg.K k ^ 2) m β * σ ≤ 1 / 2 →
      ∀ z : Fin 3 → ℝ,
        (∀ e, |atlasFrame q (cfg.nativeMidpoint k s ic) (cfg.c k s ic) z e| ≤ B) →
        |affineField (child.L ic - parent.L ip) z| ≤
          8 * B * nativeCalibrationLoss C (cfg.K k ^ 2) m β *
            (cfg.K k * (a + cfg.N k ^ (-s₀))) := by
  obtain ⟨C, L, hC, hL, hcal⟩ := exists_native_affine_comparison
  refine ⟨C, L, hC, hL, ?_⟩
  intro α _ cfg h k s₀ s parent child ip ic hA hI δ σ B hδ hσ hσH hB
  dsimp only
  intro hmesh hcap hresolve hsmall z hz
  let q := cfg.timeLength k s
  let a := cfg.N k ^ (-s)
  let m := q ^ 4 * a ^ cfg.d / cfg.K k ^ 3
  let β := 27 * ((4 * cfg.K k + 6) * (cfg.K k * a ^ cfg.d)) * q ^ 4
  let W := cfg.B k s ic ×ˢ I (cfg.T k s) (cfg.j k s ic)
  let μ := (cfg.μ k).restrict W
  let x := fun p : α × ℝ => originalBase (cfg.b k p.1) p.2
  let E := cfg.K k * (a + cfg.N k ^ (-s₀))
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hNp : 0 < cfg.N k := by linarith [h.scale k]
  have hq : 0 < q := by dsimp [q, timeLength]; positivity
  have ha : 0 < a := Real.rpow_pos_of_pos (by linarith [h.scale k]) _
  have hA₀ : 0 < cfg.N k ^ (-s₀) := Real.rpow_pos_of_pos hNp _
  have had : 0 < a ^ cfg.d := Real.rpow_pos_of_pos ha _
  have hm : 0 < m := by dsimp [m]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hKsq : 1 ≤ cfg.K k ^ 2 := one_le_pow₀ hK
  have hmβ : m ≤ β * (8 * cfg.K k ^ 2) ^ 3 := by
    have hK3 : 1 ≤ cfg.K k ^ 3 := one_le_pow₀ hK
    have hqad : 0 ≤ q ^ 4 * a ^ cfg.d := by positivity
    have hB0 : 1 ≤ 27 * (4 * cfg.K k + 6) * cfg.K k := by nlinarith
    have hβ' : q ^ 4 * a ^ cfg.d ≤ β := by
      have hh := le_mul_of_one_le_left hqad hB0
      convert hh using 1 <;> dsimp [β] <;> ring
    calc
      m ≤ q ^ 4 * a ^ cfg.d := div_le_self hqad hK3
      _ ≤ β := hβ'
      _ ≤ β * (8 * cfg.K k ^ 2) ^ 3 :=
        le_mul_of_one_le_right hβ.le (one_le_pow₀ (by linarith : 1 ≤ 8 * cfg.K k ^ 2))
  have hmass : ENNReal.ofReal m ≤ μ univ := by
    simpa only [μ, W, Measure.restrict_apply_univ] using child.witness_floor ic
  have hcells (j : Fin 3 → ℤ) :
      μ {p | (fun e => ⌊nativeFrame q (cfg.nativeMidpoint k s ic)
        (cfg.c k s ic 0) (cfg.c k s ic 2 + cfg.c k s ic 4 * cfg.c k s ic 0)
        (cfg.c k s ic 1) (-cfg.c k s ic 3 - cfg.c k s ic 4 * cfg.c k s ic 1)
        (cfg.c k s ic 4) (x p) e / σ⌋) = j} ≤ ENNReal.ofReal (β * σ ^ 3) := by
    exact child.normalized_cell_cap h hδ hσ (by positivity : 0 ≤ cfg.K k * a ^ cfg.d)
      hmesh hcap ic hresolve j
  have hW : MeasurableSet W := (child.fitted_measurable ic).prod measurableSet_Icc
  have hgood : ∀ᵐ p ∂μ,
      (∀ e, |nativeFrame q (cfg.nativeMidpoint k s ic)
        (cfg.c k s ic 0) (cfg.c k s ic 2 + cfg.c k s ic 4 * cfg.c k s ic 0)
        (cfg.c k s ic 1) (-cfg.c k s ic 3 - cfg.c k s ic 4 * cfg.c k s ic 1)
        (cfg.c k s ic 4) (x p) e| ≤ cfg.K k ^ 2) ∧
      |affineField (child.L ic - parent.L ip) (x p)| ≤ E := by
    filter_upwards [ae_restrict_mem hW,
      Data.NativeLevel.child_parent_difference_ae h parent child ip ic hA hI]
      with p hp hdiff
    exact ⟨h.native_frame_bound child.assignments ic p.1
      (child.assignments.fitted_subset ic hp.1) hp.2, hdiff⟩
  exact hcal (α × ℝ) μ x (child.L ic - parent.L ip) q (cfg.nativeMidpoint k s ic)
    (cfg.c k s ic 0) (cfg.c k s ic 2 + cfg.c k s ic 4 * cfg.c k s ic 0)
    (cfg.c k s ic 1) (-cfg.c k s ic 3 - cfg.c k s ic 4 * cfg.c k s ic 1)
    (cfg.c k s ic 4) (cfg.K k ^ 2) σ m β E B
    hq hKsq hσ hσH hm hβ hmβ (by dsimp [E]; positivity) hB
    hmass hcells hgood hsmall z hz

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
