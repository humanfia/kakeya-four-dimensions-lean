/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/OffsetCaps.lean`. Original attributions are retained below. -/
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-! Original finite-mesh signal caps with a moving offset. An arbitrary original
palette weight is retained as an ENNReal factor; no marginal law is replaced. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4MovingMeshBoxes

/-- A bounded signal interval meets finitely many native bins, with its original
cell budget unchanged for every bin. The event need not be measurable. -/
theorem signal_interval_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Q) (value : Ω → ℝ) (condition : Ω → Prop)
    (q : Q) (E : Set Ω) {w radius center : ℝ} (hw : 0 < w) (hr : 0 ≤ radius)
    (B : ℝ≥0∞)
    (hcap : ∀ j : ℤ,
      μ {p | code p = q ∧ ⌊value p / w⌋ = j ∧ condition p} ≤ B)
    (hE : ∀ p ∈ E, code p = q ∧ condition p ∧ |value p - center| ≤ radius) :
    μ E ≤ ENNReal.ofReal (4 * radius / w + 2) * B := by
  classical
  obtain ⟨F, hF, hcover⟩ := interval_mesh_cover hw hr center
  have hsub : E ⊆ ⋃ j ∈ F, {p | code p = q ∧ ⌊value p / w⌋ = j ∧ condition p} := by
    intro p hp
    obtain ⟨hq, hc, hv⟩ := hE p hp
    exact mem_iUnion₂.mpr ⟨⌊value p / w⌋, hcover (value p) hv, hq, rfl, hc⟩
  calc
    μ E ≤ μ (⋃ j ∈ F, {p | code p = q ∧ ⌊value p / w⌋ = j ∧ condition p}) :=
      measure_mono hsub
    _ ≤ ∑ j ∈ F, μ {p | code p = q ∧ ⌊value p / w⌋ = j ∧ condition p} :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ _j ∈ F, B := Finset.sum_le_sum (fun j _ => hcap j)
    _ = ENNReal.ofReal (F.card : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (4 * radius / w + 2) * B :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hF) le_rfl

/-- Subtracting an offset that oscillates by at most one signal width in a
native base cell costs only ten original signal-bin budgets. -/
theorem shifted_signal_cell_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Q) (value offset : Ω → ℝ)
    (condition : Ω → Prop) (q : Q) (j : ℤ) {w c : ℝ} (hw : 0 < w)
    (B : ℝ≥0∞)
    (hcap : ∀ n : ℤ,
      μ {p | code p = q ∧ ⌊value p / w⌋ = n ∧ condition p} ≤ B)
    (hosc : ∀ p, code p = q → condition p → |offset p - c| ≤ w) :
    μ {p | code p = q ∧ ⌊(value p - offset p) / w⌋ = j ∧ condition p} ≤ 10 * B := by
  have hc : 4 * (2 * w) / w + 2 = 10 := by field_simp; ring
  have h := signal_interval_cap μ code value condition q
    {p | code p = q ∧ ⌊(value p - offset p) / w⌋ = j ∧ condition p}
    hw (show 0 ≤ 2 * w by positivity) B hcap (center := (j : ℝ) * w + c) ?_
  · simpa only [hc, ENNReal.ofReal_ofNat] using h
  · intro p hp
    refine ⟨hp.1, hp.2.2, ?_⟩
    have hlo := Int.floor_le ((value p - offset p) / w)
    have hhi := Int.lt_floor_add_one ((value p - offset p) / w)
    rw [hp.2.1] at hlo hhi
    have hlow := (le_div_iff₀ hw).mp hlo
    have hhigh := (div_lt_iff₀ hw).mp hhi
    have hv : |value p - offset p - (j : ℝ) * w| ≤ w := by
      rw [abs_le]
      constructor <;> linarith
    calc
      _ = |(value p - offset p - (j : ℝ) * w) + (offset p - c)| := by congr 1; ring
      _ ≤ |value p - offset p - (j : ℝ) * w| + |offset p - c| := abs_add_le _ _
      _ ≤ 2 * w := by linarith [hosc p hp.1 hp.2.2]

/-- An original band about a resolved offset gives a pure base-cell cap. This
is used on whole native witnesses when their retained signal width changes. -/
theorem offset_band_cell_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Q) (value offset : Ω → ℝ)
    (condition : Ω → Prop) (q : Q) {w c L : ℝ} (hw : 0 < w) (hL : 0 ≤ L)
    (B : ℝ≥0∞)
    (hcap : ∀ n : ℤ,
      μ {p | code p = q ∧ ⌊value p / w⌋ = n ∧ condition p} ≤ B)
    (hosc : ∀ p, code p = q → condition p → |offset p - c| ≤ w) :
    μ {p | code p = q ∧ |value p - offset p| ≤ L * w ∧ condition p} ≤
      ENNReal.ofReal (4 * L + 6) * B := by
  have hc : 4 * ((L + 1) * w) / w + 2 = 4 * L + 6 := by field_simp; ring
  have h := signal_interval_cap μ code value condition q
    {p | code p = q ∧ |value p - offset p| ≤ L * w ∧ condition p}
    hw (show 0 ≤ (L + 1) * w by positivity) B hcap (center := c) ?_
  · simpa only [hc] using h
  · intro p hp
    refine ⟨hp.1, hp.2.2, ?_⟩
    calc
      _ ≤ |value p - offset p| + |offset p - c| := abs_sub_le _ _ _
      _ ≤ L * w + w := add_le_add hp.2.1 (hosc p hp.1 hp.2.2)
      _ = (L + 1) * w := by ring

end Submission.Obl.k4_subcritical_corrected_scalar_charts
