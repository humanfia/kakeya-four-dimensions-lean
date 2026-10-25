/- Adapted from this LOT tree, obligation o201, session x0697, commit d395b4346c32,
   Submission/Obl/k4_horizontal_critical_rate_candidates/NativeCellCaps.lean.
   Existing source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.ContactCellGeometry
import Submission.Obl.k4_scalar_initial_true_horizon.FiniteCardBound
import Submission.Obl.k4_scalar_initial_true_horizon.InitialCells

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Inherited
open scoped ENNReal

noncomputable section

/-- Finite ORIGINAL base codes in one normalized cell, counted using its
physical contact volume. No axis-aligned enclosing rectangle is charged. -/
theorem finite_native_cell_table {Ω : Type*} (E : Set Ω) (point : Ω → Fin 3 → ℝ)
    (H t₀ z₀ y₀ v₀ K G δ ξ : ℝ) (q₀ : Fin 3 → ℝ)
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hG : 1 ≤ G) (hξ : 0 < ξ)
    (hξt : ξ ≤ H * δ) (hξZ : 2 * G * ξ ≤ H * δ)
    (hξY : 3 * G * ξ ≤ (K + 2) * H ^ 2 * δ)
    (ht₀ : |q₀ 0| ≤ 1) (hz₀ : |q₀ 1| ≤ K)
    (hm : |horizontalUnframe H t₀ z₀ y₀ v₀ q₀ 0| ≤ 1)
    (hv : |v₀| ≤ G) (hposition : |horizontalUnframe H t₀ z₀ y₀ v₀ q₀ 1| ≤ G)
    (hgap : ∀ p ∈ E, ∀ i, |point p i - q₀ i| ≤ δ) :
    ∃ F : Finset (Fin 3 → ℤ),
      (∀ j, j ∈ F ↔ ∃ p ∈ E,
        (fun i => ⌊horizontalUnframe H t₀ z₀ y₀ v₀ (point p) i / ξ⌋) = j) ∧
      (F.card : ℝ) * ξ ^ 3 ≤ 64 * (K + 2) * H ^ 4 * δ ^ 3 := by
  classical
  let code (p : Ω) : Fin 3 → ℤ :=
    fun i => ⌊horizontalUnframe H t₀ z₀ y₀ v₀ (point p) i / ξ⌋
  let C := 64 * (K + 2) * H ^ 4 * δ ^ 3
  have hcount (F : Finset (Fin 3 → ℤ)) (hF : (↑F : Set _) ⊆ code '' E) :
      (F.card : ℝ) * ξ ^ 3 ≤ C := by
    apply original_grid_count_normalized_cell H t₀ z₀ y₀ v₀ K G δ ξ q₀
      hH hK hδ hG hξ hξt hξZ hξY ht₀ hz₀ hm hv hposition F
    intro j hj
    obtain ⟨p, hp, hcode⟩ := hF hj
    exact ⟨point p, hgap p hp, fun i => congrFun hcode i⟩
  have hfinite : (code '' E).Finite :=
    Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
      (code '' E) (C / ξ ^ 3) (fun F hF => (le_div_iff₀ (by positivity)).mpr (hcount F hF))
  refine ⟨hfinite.toFinset, ?_, hcount hfinite.toFinset ?_⟩
  · intro j
    simp only [Set.Finite.mem_toFinset, Set.mem_image]
    rfl
  · intro j hj
    change j ∈ hfinite.toFinset at hj
    simpa only [Set.Finite.mem_toFinset] using hj

/-- A short ORIGINAL hidden interval needs at most 2*D+2 original bins,
independently of where the interval is centered. -/
theorem scalar_interval_bin_cover (center a D : ℝ) (ha : 0 < a) (hD : 0 ≤ D) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ 2 * D + 2 ∧
      ∀ y : ℝ, |y - center| ≤ D * a → ⌊y / a⌋ ∈ J := by
  let l := (center - D * a) / a
  let u := (center + D * a) / a
  have hlu : l ≤ u := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hD ha.le]) ha.le
  refine ⟨Finset.Icc ⌊l⌋ ⌊u⌋, ?_, ?_⟩
  · have hc := Submission.Obl.k4_scalar_initial_true_horizon.card_Icc_floor_le hlu
    convert hc using 1
    dsimp [l, u]
    field_simp
    ring
  · intro y hy
    apply Finset.mem_Icc.mpr
    have hy' := abs_le.mp hy
    constructor
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) ha.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) ha.le)

/-- Integrate the frozen ORIGINAL joint mesh caps over one normalized contact
cell and one short ORIGINAL native hidden interval. The velocity palette
factor is kept, and the physical volume is H^4*delta^3. -/
theorem native_joint_cap_normalized_cell
    {Ω Pal : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (point : Ω → Fin 3 → ℝ) (value : Ω → ℝ)
    (Z : Ω → Pal) (π : Pal → ℝ≥0∞)
    (H t₀ z₀ y₀ v₀ K G δ ξ a d center D C : ℝ) (q₀ : Fin 3 → ℝ)
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hG : 1 ≤ G) (hξ : 0 < ξ)
    (ha : 0 < a) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hξt : ξ ≤ H * δ) (hξZ : 2 * G * ξ ≤ H * δ)
    (hξY : 3 * G * ξ ≤ (K + 2) * H ^ 2 * δ)
    (ht₀ : |q₀ 0| ≤ 1) (hz₀ : |q₀ 1| ≤ K)
    (hm : |horizontalUnframe H t₀ z₀ y₀ v₀ q₀ 0| ≤ 1)
    (hv : |v₀| ≤ G) (hposition : |horizontalUnframe H t₀ z₀ y₀ v₀ q₀ 1| ≤ G)
    (hgap : ∀ p ∈ E, ∀ i, |point p i - q₀ i| ≤ δ)
    (hvalue : ∀ p ∈ E, |value p - center| ≤ D * a)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ) (z : Pal),
      μ {p | (fun i => ⌊horizontalUnframe H t₀ z₀ y₀ v₀ (point p) i / ξ⌋) = q ∧
        ⌊value p / a⌋ = j ∧ Z p = z} ≤ ENNReal.ofReal (C * ξ ^ 3 * a ^ d) * π z) :
    ∀ z : Pal, μ {p | p ∈ E ∧ Z p = z} ≤
      ENNReal.ofReal (128 * C * (K + 2) * (D + 1) * H ^ 4 * δ ^ 3 * a ^ d) * π z := by
  classical
  obtain ⟨F, hF, hFcount⟩ := finite_native_cell_table E point H t₀ z₀ y₀ v₀ K G δ ξ q₀
    hH hK hδ hG hξ hξt hξZ hξY ht₀ hz₀ hm hv hposition hgap
  obtain ⟨J, hJcount, hJcover⟩ := scalar_interval_bin_cover center a D ha hD
  let code (p : Ω) : Fin 3 → ℤ :=
    fun i => ⌊horizontalUnframe H t₀ z₀ y₀ v₀ (point p) i / ξ⌋
  intro z
  let B (q : Fin 3 → ℤ) (j : ℤ) := {p | code p = q ∧ ⌊value p / a⌋ = j ∧ Z p = z}
  have hsub : {p | p ∈ E ∧ Z p = z} ⊆ ⋃ q ∈ F, ⋃ j ∈ J, B q j := by
    intro p hp
    refine Set.mem_iUnion₂.mpr ⟨code p, (hF _).mpr ⟨p, hp.1, rfl⟩, ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨⌊value p / a⌋, hJcover _ (hvalue p hp.1), rfl, rfl, hp.2⟩
  have hsum : μ {p | p ∈ E ∧ Z p = z} ≤
      (F.card : ℝ≥0∞) * (J.card : ℝ≥0∞) * (ENNReal.ofReal (C * ξ ^ 3 * a ^ d) * π z) := by
    calc
      _ ≤ μ (⋃ q ∈ F, ⋃ j ∈ J, B q j) := measure_mono hsub
      _ ≤ ∑ q ∈ F, μ (⋃ j ∈ J, B q j) := measure_biUnion_finset_le _ _
      _ ≤ ∑ q ∈ F, ∑ j ∈ J, μ (B q j) :=
        Finset.sum_le_sum (fun q _ => measure_biUnion_finset_le _ _)
      _ ≤ ∑ _q ∈ F, ∑ _j ∈ J, ENNReal.ofReal (C * ξ ^ 3 * a ^ d) * π z :=
        Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun j _ => hcap q j z))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hreal : (F.card : ℝ) * (J.card : ℝ) * C * ξ ^ 3 * a ^ d ≤
      128 * C * (K + 2) * (D + 1) * H ^ 4 * δ ^ 3 * a ^ d := by
    calc
      _ = (C * a ^ d) * ((F.card : ℝ) * ξ ^ 3) * (J.card : ℝ) := by ring
      _ ≤ (C * a ^ d) * (64 * (K + 2) * H ^ 4 * δ ^ 3) * (2 * D + 2) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hFcount (mul_nonneg hC (Real.rpow_nonneg ha.le _)))
          hJcount (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have heq : ENNReal.ofReal ((F.card : ℝ) * (J.card : ℝ) * C * ξ ^ 3 * a ^ d) =
      (F.card : ℝ≥0∞) * (J.card : ℝ≥0∞) * ENNReal.ofReal (C * ξ ^ 3 * a ^ d) := by
    rw [show (F.card : ℝ) * (J.card : ℝ) * C * ξ ^ 3 * a ^ d =
      ((F.card : ℝ) * (J.card : ℝ)) * (C * ξ ^ 3 * a ^ d) by ring,
      ENNReal.ofReal_mul (by positivity : 0 ≤ (F.card : ℝ) * (J.card : ℝ)),
      ENNReal.ofReal_mul (Nat.cast_nonneg F.card)]
    simp only [ENNReal.ofReal_natCast]
  calc
    _ ≤ (F.card : ℝ≥0∞) * (J.card : ℝ≥0∞) * (ENNReal.ofReal (C * ξ ^ 3 * a ^ d) * π z) := hsum
    _ = ENNReal.ofReal ((F.card : ℝ) * (J.card : ℝ) * C * ξ ^ 3 * a ^ d) * π z := by rw [heq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) zero_le

end

end Submission.Obl.k4_critical_switching_state_preparation
