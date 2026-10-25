import Submission.Lib.K4MovingMeshBoxes.Geometry
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Variation

set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A moving signal window costs an absolute number of signal bins per fine
base cell. The fine mesh resolves the motion, so no bound on the absolute
size of the frame velocity enters the resulting constant. -/
theorem measure_resolved_moving_slab
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (signal : Ω → ℝ)
    (background : (Fin 3 → ℝ) → ℝ) (condition : Ω → Prop) (E : Set Ω)
    {δ Δ radius L C : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hdr : δ ≤ radius) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (time offset : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, δ ≤ width i)
    (hmove : ∀ i, L * δ ≤ width i)
    (hbox : ∀ p ∈ E, point p ∈
      Submission.Lib.K4MovingMeshBoxes.movingBox time radius center velocity width)
    (hcondition : ∀ p ∈ E, condition p)
    (hwindow : ∀ p ∈ E, |signal p - background (point p) - offset| ≤ Δ)
    (hbackground : ∀ p ∈ E, ∀ y : Fin 3 → ℝ,
      (∀ i, |point p i - y i| ≤ δ) →
      |background (point p) - background y| ≤ Δ)
    (weight : ℝ≥0∞)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | (fun i => ⌊point p i / δ⌋) = q ∧
        ⌊signal p / Δ⌋ = j ∧ condition p} ≤
          ENNReal.ofReal (C * δ ^ 3) * weight) :
    μ E ≤ ENNReal.ofReal (4200 * C * radius * width 0 * width 1) * weight := by
  classical
  obtain ⟨Q, hQ, hcover⟩ :=
    Submission.Lib.K4MovingMeshBoxes.movingBox_mesh_volume hδ hdr hL
      time center velocity width hv hdw hmove
  let corner : (Fin 3 → ℤ) → Fin 3 → ℝ := fun q i => (q i : ℝ) * δ
  let bins (q : Fin 3 → ℤ) : Finset ℤ :=
    (Finset.Icc (-3 : ℤ) 3).image
      (fun j => ⌊(background (corner q) + offset) / Δ⌋ + j)
  have hbins (q : Fin 3 → ℤ) : (bins q).card ≤ 7 := by
    exact Finset.card_image_le.trans (by norm_num)
  have hmem (p : Ω) (hp : p ∈ E) :
      ⌊signal p / Δ⌋ ∈ bins (fun i => ⌊point p i / δ⌋) := by
    have hcorner (i : Fin 3) :
        |point p i - corner (fun i => ⌊point p i / δ⌋) i| ≤ δ := by
      have hlo := (le_div_iff₀ hδ).mp (Int.floor_le (point p i / δ))
      have hhi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (point p i / δ))
      simp only [corner, abs_le]
      constructor <;> nlinarith only [hlo, hhi]
    have hbg := hbackground p hp _ hcorner
    have hs : |signal p - (background (corner (fun i => ⌊point p i / δ⌋)) + offset)| ≤
        2 * Δ := by
      calc
        _ = |(signal p - background (point p) - offset) +
            (background (point p) -
              background (corner (fun i => ⌊point p i / δ⌋)))| := by congr 1; ring
        _ ≤ |signal p - background (point p) - offset| +
            |background (point p) -
              background (corner (fun i => ⌊point p i / δ⌋))| := abs_add_le _ _
        _ ≤ Δ + Δ := add_le_add (hwindow p hp) hbg
        _ = _ := by ring
    have hoff := Submission.Obl.k4_fixed_budget_quadratic_recovery.floor_offset_mem hΔ hs
    norm_num at hoff
    exact Finset.mem_image.mpr
      ⟨⌊signal p / Δ⌋ - ⌊(background (corner (fun i => ⌊point p i / δ⌋)) + offset) / Δ⌋,
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  let cell (q : Fin 3 → ℤ) (j : ℤ) : Set Ω :=
    {p | (fun i => ⌊point p i / δ⌋) = q ∧ ⌊signal p / Δ⌋ = j ∧ condition p}
  have hsub : E ⊆ ⋃ q ∈ Q, ⋃ j ∈ bins q, cell q j := by
    intro p hp
    apply mem_iUnion₂.mpr
    refine ⟨_, hcover _ (hbox p hp), mem_iUnion₂.mpr ?_⟩
    exact ⟨_, hmem p hp, rfl, rfl, hcondition p hp⟩
  have hsum (q : Fin 3 → ℤ) :
      μ (⋃ j ∈ bins q, cell q j) ≤
        (7 : ℝ≥0∞) * (ENNReal.ofReal (C * δ ^ 3) * weight) := by
    calc
      _ ≤ ∑ j ∈ bins q, μ (cell q j) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ bins q, ENNReal.ofReal (C * δ ^ 3) * weight :=
        Finset.sum_le_sum (fun j _ => hcap q j)
      _ = ((bins q).card : ℝ≥0∞) *
          (ENNReal.ofReal (C * δ ^ 3) * weight) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul' (by exact_mod_cast hbins q) le_rfl
  have hscalar : (Q.card : ℝ) * (7 * (C * δ ^ 3)) ≤
      4200 * C * radius * width 0 * width 1 := by
    have hm := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 7 * C)
    nlinarith only [hm]
  calc
    μ E ≤ μ (⋃ q ∈ Q, ⋃ j ∈ bins q, cell q j) := measure_mono hsub
    _ ≤ ∑ q ∈ Q, μ (⋃ j ∈ bins q, cell q j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ Q, (7 : ℝ≥0∞) * (ENNReal.ofReal (C * δ ^ 3) * weight) :=
      Finset.sum_le_sum (fun q _ => hsum q)
    _ = ENNReal.ofReal ((Q.card : ℝ) * (7 * (C * δ ^ 3))) * weight := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        show (7 : ℝ≥0∞) = ENNReal.ofReal 7 by norm_num,
        ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hscalar) le_rfl

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
