/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, GroupBandGrid.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.JointGrid

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Finset MeasureTheory
open scoped ENNReal

abbrev GroupBaseIndex := (Σ _ : ℤ, ℤ × ℤ)
abbrev GroupJointIndex := (Σ _ : GroupBaseIndex, ℤ)

def groupGridPoint (δ : ℝ) (q : GroupBaseIndex) : Fin 3 → ℝ :=
  ![δ * q.1, δ * q.2.1, δ * q.2.2]

def groupBaseIndex (δ : ℝ) (p : Fin 3 → ℝ) : GroupBaseIndex :=
  ⟨⌊p 0 / δ⌋, (⌊p 1 / δ⌋, ⌊p 2 / δ⌋)⟩

def groupJointIndex (δ r : ℝ) (p : Fin 3 → ℝ) (value : ℝ) : GroupJointIndex :=
  ⟨groupBaseIndex δ p, ⌊value / r⌋⟩

def groupBaseCover (δ H D K t₀ : ℝ) (p : Fin 3 → ℝ) : Finset GroupBaseIndex :=
  (Icc ⌊t₀ / δ⌋ ⌊(t₀ + H) / δ⌋).sigma (fun it =>
    (floorBand δ (p 0 + (δ * it) * p 2) (2 * D + K * δ)) ×ˢ
    (floorBand δ (p 1 - (δ * it) * p 0) (3 * D + K * δ)))

def groupJointCover (δ r H D K t₀ : ℝ) (p : Fin 3 → ℝ) (L : Fin 4 → ℝ) : Finset GroupJointIndex :=
  (groupBaseCover δ H D K t₀ p).sigma (fun q =>
    floorBand r (affineBaseValue L (groupGridPoint δ q)) (2 * K * r))

/-- A group of original initial positions and velocities has base volume
H*D^2 on a time window of length H, including its grid enlargement. -/
theorem groupJointCover_card
    (δ r H D K t₀ : ℝ) (p : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (hδ : 0 < δ) (hr : 0 < r) (hK : 1 ≤ K) (hδH : δ ≤ H) (hδD : K * δ ≤ D) :
    ((groupJointCover δ r H D K t₀ p L).card : ℝ) ≤ 1440 * K * H * D ^ 2 / δ ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hδD' : δ ≤ D := (le_mul_of_one_le_left hδ.le hK).trans hδD
  have hD : 0 < D := hδ.trans_le hδD'
  have hH : 0 < H := hδ.trans_le hδH
  have ht : ((Icc ⌊t₀ / δ⌋ ⌊(t₀ + H) / δ⌋).card : ℝ) ≤ 3 * H / δ := by
    have hc := Submission.Obl.k4_scalar_initial_true_horizon.card_Icc_floor_le
      (show t₀ / δ ≤ (t₀ + H) / δ by gcongr; linarith)
    have heq : (t₀ + H) / δ - t₀ / δ + 2 = H / δ + 2 := by ring
    rw [heq] at hc
    apply hc.trans
    apply (le_div_iff₀ hδ).mpr
    have heq' : (H / δ + 2) * δ = H + 2 * δ := by field_simp
    rw [heq']
    linarith
  have hZ (it : ℤ) : ((floorBand δ (p 0 + (δ * it) * p 2) (2 * D + K * δ)).card : ℝ) ≤ 8 * D / δ := by
    apply (floorBand_card hδ (by positivity)).trans
    apply (le_div_iff₀ hδ).mpr
    have heq : (2 * (2 * D + K * δ) / δ + 2) * δ = 4 * D + 2 * K * δ + 2 * δ := by field_simp; ring
    rw [heq]
    linarith
  have hY (it : ℤ) : ((floorBand δ (p 1 - (δ * it) * p 0) (3 * D + K * δ)).card : ℝ) ≤ 10 * D / δ := by
    apply (floorBand_card hδ (by positivity)).trans
    apply (le_div_iff₀ hδ).mpr
    have heq : (2 * (3 * D + K * δ) / δ + 2) * δ = 6 * D + 2 * K * δ + 2 * δ := by field_simp; ring
    rw [heq]
    linarith
  have hbase : ((groupBaseCover δ H D K t₀ p).card : ℝ) ≤ (3 * H / δ) * ((8 * D / δ) * (10 * D / δ)) := by
    unfold groupBaseCover
    rw [card_sigma]
    push_cast
    calc
      _ ≤ ∑ _it ∈ Icc ⌊t₀ / δ⌋ ⌊(t₀ + H) / δ⌋, ((8 * D / δ) * (10 * D / δ)) := by
        apply sum_le_sum
        intro it _
        simp only [card_product, Nat.cast_mul]
        exact mul_le_mul (hZ it) (hY it) (Nat.cast_nonneg _) (by positivity)
      _ = ((Icc ⌊t₀ / δ⌋ ⌊(t₀ + H) / δ⌋).card : ℝ) * ((8 * D / δ) * (10 * D / δ)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (by positivity)
  have hh (q : GroupBaseIndex) :
      ((floorBand r (affineBaseValue L (groupGridPoint δ q)) (2 * K * r)).card : ℝ) ≤ 6 * K := by
    apply (floorBand_card hr (by positivity)).trans
    have heq : 2 * (2 * K * r) / r + 2 = 4 * K + 2 := by field_simp; ring
    rw [heq]
    linarith
  unfold groupJointCover
  rw [card_sigma]
  push_cast
  calc
    _ ≤ ∑ _q ∈ groupBaseCover δ H D K t₀ p, (6 * K) := sum_le_sum (fun q _ => hh q)
    _ = ((groupBaseCover δ H D K t₀ p).card : ℝ) * (6 * K) := by simp
    _ ≤ ((3 * H / δ) * ((8 * D / δ) * (10 * D / δ))) * (6 * K) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = _ := by field_simp; ring

theorem mem_groupJointCover
    (δ r H D K t₀ : ℝ) (p q : Fin 3 → ℝ) (L : Fin 4 → ℝ) (value : ℝ)
    (hδ : 0 < δ) (hr : 0 < r) (hK : 0 ≤ K) (hmesh : 3 * δ ≤ r)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K) (hL : ∀ e : Fin 3, |L e.succ| ≤ K)
    (ht : q 0 ∈ Set.Icc t₀ (t₀ + H))
    (hZ : |q 1 - p 0 - q 0 * p 2| ≤ 2 * D)
    (hY : |q 2 - p 1 + q 0 * p 0| ≤ 3 * D)
    (hfit : |value - affineBaseValue L q| ≤ K * r) :
    groupJointIndex δ r q value ∈ groupJointCover δ r H D K t₀ p L := by
  have hround : |q 0 - δ * (⌊q 0 / δ⌋ : ℝ)| ≤ δ :=
    Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hδ _
  have hm (e : Fin 3) (he : |p e| ≤ K) : |(q 0 - δ * (⌊q 0 / δ⌋ : ℝ)) * p e| ≤ K * δ := by
    rw [abs_mul]
    exact (mul_le_mul hround he (abs_nonneg _) hδ.le).trans_eq (mul_comm _ _)
  have hZgrid : |q 1 - (p 0 + (δ * (⌊q 0 / δ⌋ : ℝ)) * p 2)| ≤ 2 * D + K * δ := by
    calc
      _ = |(q 1 - p 0 - q 0 * p 2) + (q 0 - δ * (⌊q 0 / δ⌋ : ℝ)) * p 2| := by congr 1; ring
      _ ≤ |q 1 - p 0 - q 0 * p 2| + |(q 0 - δ * (⌊q 0 / δ⌋ : ℝ)) * p 2| := abs_add_le _ _
      _ ≤ _ := add_le_add hZ (hm 2 hp₂)
  have hYgrid : |q 2 - (p 1 - (δ * (⌊q 0 / δ⌋ : ℝ)) * p 0)| ≤ 3 * D + K * δ := by
    calc
      _ = |(q 2 - p 1 + q 0 * p 0) - (q 0 - δ * (⌊q 0 / δ⌋ : ℝ)) * p 0| := by congr 1; ring
      _ ≤ |q 2 - p 1 + q 0 * p 0| + |(q 0 - δ * (⌊q 0 / δ⌋ : ℝ)) * p 0| := abs_sub _ _
      _ ≤ _ := add_le_add hY (hm 0 hp₀)
  have hhidden : |value - affineBaseValue L (groupGridPoint δ (groupBaseIndex δ q))| ≤ 2 * K * r := by
    have hg := affineBaseValue_grid_error δ K L q hδ hK hL
    have hdist := abs_sub_le value (affineBaseValue L q) (affineBaseValue L (gridPoint δ (baseGridIndex δ q)))
    have heq : groupGridPoint δ (groupBaseIndex δ q) = gridPoint δ (baseGridIndex δ q) := rfl
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hmesh hK
    linarith
  apply mem_sigma.mpr
  refine ⟨?_, mem_floorBand hr hhidden⟩
  apply mem_sigma.mpr
  refine ⟨mem_Icc.mpr ?_, mem_product.mpr ⟨mem_floorBand hδ hZgrid, mem_floorBand hδ hYgrid⟩⟩
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right ht.1 hδ.le),
    Int.floor_mono (div_le_div_of_nonneg_right ht.2 hδ.le)⟩

/-- The original joint caps integrate over a moving initial-position group
and an affine scalar band with the original external palette factor. -/
theorem original_group_band_joint_cap
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (U : Set Y)
    (point : Y → Fin 3 → ℝ) (value : Y → ℝ) (velocity : Y → ℤ) (j : ℤ)
    (δ r H D K t₀ C Z : ℝ) (palette : ℝ≥0∞) (p : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (hδ : 0 < δ) (hr : 0 < r) (hK : 1 ≤ K) (hC : 0 ≤ C) (hZ : 0 ≤ Z)
    (hδH : δ ≤ H) (hδD : K * δ ≤ D) (hmesh : 3 * δ ≤ r)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K) (hL : ∀ e : Fin 3, |L e.succ| ≤ K)
    (ht : ∀ y ∈ U, point y 0 ∈ Set.Icc t₀ (t₀ + H))
    (hpos : ∀ y ∈ U, |point y 1 - p 0 - point y 0 * p 2| ≤ 2 * D)
    (htrans : ∀ y ∈ U, |point y 2 - p 1 + point y 0 * p 0| ≤ 3 * D)
    (hfit : ∀ y ∈ U, |value y - affineBaseValue L (point y)| ≤ K * r)
    (hvel : ∀ y ∈ U, velocity y = j)
    (hcap : ∀ (q : Fin 3 → ℤ) (n : ℤ),
      μ {y | (fun e => ⌊point y e / δ⌋) = q ∧ ⌊value y / r⌋ = n ∧ velocity y = j} ≤
        ENNReal.ofReal (C * δ ^ 3 * Z) * palette) :
    μ U ≤ ENNReal.ofReal (1440 * C * K * H * D ^ 2 * Z) * palette := by
  let F := groupJointCover δ r H D K t₀ p L
  let cell := fun q : GroupJointIndex =>
    {y | groupJointIndex δ r (point y) (value y) = q ∧ velocity y = j}
  have hcell (q : GroupJointIndex) : μ (cell q) ≤ ENNReal.ofReal (C * δ ^ 3 * Z) * palette := by
    let q₀ : Fin 3 → ℤ := ![q.1.1, q.1.2.1, q.1.2.2]
    apply le_trans (measure_mono ?_) (hcap q₀ q.2)
    intro y hy
    refine ⟨?_, congrArg (fun z : GroupJointIndex => z.2) hy.1, hy.2⟩
    funext e
    fin_cases e
    · exact congrArg (fun z : GroupJointIndex => z.1.1) hy.1
    · exact congrArg (fun z : GroupJointIndex => z.1.2.1) hy.1
    · exact congrArg (fun z : GroupJointIndex => z.1.2.2) hy.1
  have hcover : U ⊆ ⋃ q ∈ F, cell q := by
    intro y hy
    refine Set.mem_iUnion₂.mpr ⟨groupJointIndex δ r (point y) (value y), ?_, rfl, hvel y hy⟩
    exact mem_groupJointCover δ r H D K t₀ p (point y) L (value y)
      hδ hr (by linarith) hmesh hp₀ hp₂ hL (ht y hy) (hpos y hy) (htrans y hy) (hfit y hy)
  have hcount := groupJointCover_card δ r H D K t₀ p L hδ hr hK hδH hδD
  have hscalar : (F.card : ℝ) * (C * δ ^ 3 * Z) ≤ 1440 * C * K * H * D ^ 2 * Z := by
    have hc := (le_div_iff₀ (pow_pos hδ 3)).mp hcount
    have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg hC hZ)
    convert hm using 1 <;> ring
  calc
    _ ≤ μ (⋃ q ∈ F, cell q) := measure_mono hcover
    _ ≤ ∑ q ∈ F, μ (cell q) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ F, ENNReal.ofReal (C * δ ^ 3 * Z) * palette := sum_le_sum (fun q _ => hcell q)
    _ = ENNReal.ofReal ((F.card : ℝ) * (C * δ ^ 3 * Z)) * palette := by
      simp only [sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hscalar) zero_le

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
