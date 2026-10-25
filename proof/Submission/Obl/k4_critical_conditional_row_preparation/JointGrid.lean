/- Adapted from our LOT tree o211, session x0736, commit fb9fb2638e83e4e42cdf985859ec4b5deb228222,
`Submission/Obl/k4_critical_affine_derivative_preparation/JointGrid.lean`.
Earlier provenance comments in that file are retained below. -/

import Submission.Obl.k4_scalar_initial_true_horizon.InitialCells
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

open Finset MeasureTheory
open scoped ENNReal

abbrev BaseGridIndex := (Σ _ : ℤ × ℤ, ℤ)
abbrev JointGridIndex := (Σ _ : BaseGridIndex, ℤ)

def gridPoint (δ : ℝ) (q : BaseGridIndex) : Fin 3 → ℝ :=
  ![δ * q.1.1, δ * q.1.2, δ * q.2]

def affineBaseValue (L : Fin 4 → ℝ) (p : Fin 3 → ℝ) : ℝ :=
  L 0 + ∑ i : Fin 3, L i.succ * p i

def baseGridIndex (δ : ℝ) (p : Fin 3 → ℝ) : BaseGridIndex :=
  ⟨(⌊p 0 / δ⌋, ⌊p 1 / δ⌋), ⌊p 2 / δ⌋⟩

def jointGridIndex (δ a : ℝ) (p : Fin 3 → ℝ) (w : ℝ) : JointGridIndex :=
  ⟨baseGridIndex δ p, ⌊w / a⌋⟩

def floorBand (δ center radius : ℝ) : Finset ℤ :=
  Icc ⌊(center - radius) / δ⌋ ⌊(center + radius) / δ⌋

theorem mem_floorBand {δ x center radius : ℝ} (hδ : 0 < δ)
    (h : |x - center| ≤ radius) : ⌊x / δ⌋ ∈ floorBand δ center radius := by
  apply mem_Icc.mpr
  have hh := abs_le.mp h
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (by linarith : center - radius ≤ x) hδ.le),
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith : x ≤ center + radius) hδ.le)⟩

theorem floorBand_card {δ center radius : ℝ} (hδ : 0 < δ) (hr : 0 ≤ radius) :
    ((floorBand δ center radius).card : ℝ) ≤ 2 * radius / δ + 2 := by
  have hc := Submission.Obl.k4_scalar_initial_true_horizon.card_Icc_floor_le
    (show (center - radius) / δ ≤ (center + radius) / δ by gcongr; linarith)
  calc
    _ ≤ (center + radius) / δ - (center - radius) / δ + 2 := hc
    _ = _ := by ring

def rectangleBaseCover (δ w B K t₀ Z₀ : ℝ) (c : Fin 3 → ℝ) : Finset BaseGridIndex :=
  ((Icc ⌊t₀ / δ⌋ ⌊(t₀ + w) / δ⌋) ×ˢ
    (Icc ⌊Z₀ / δ⌋ ⌊(Z₀ + w) / δ⌋)).sigma (fun q =>
      floorBand δ (c 0 + c 1 * (δ * q.1) + c 2 * (δ * q.2)) (B + 2 * K * δ))

def rectangleJointCover (δ a w B K t₀ Z₀ : ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ) :
    Finset JointGridIndex :=
  (rectangleBaseCover δ w B K t₀ Z₀ c).sigma
    (fun q => floorBand a (affineBaseValue L (gridPoint δ q)) (2 * K * a))

/-- An anisotropic rectangle and affine hidden band occupy only their
three-dimensional base volume times a fixed loss worth of joint cells. -/
theorem rectangleJointCover_card
    (δ a w B K t₀ Z₀ : ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (hδ : 0 < δ) (ha : 0 < a) (hK : 1 ≤ K) (hδw : δ ≤ w) (hδB : δ ≤ B) :
    ((rectangleJointCover δ a w B K t₀ Z₀ c L).card : ℝ) ≤
      432 * K ^ 2 * w ^ 2 * B / δ ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hw : 0 < w := hδ.trans_le hδw
  have hB : 0 < B := hδ.trans_le hδB
  have hKB : B ≤ K * B := le_mul_of_one_le_left hB.le hK
  have hKδ : K * δ ≤ K * B := mul_le_mul_of_nonneg_left hδB hK0
  have htime (x : ℝ) : ((Icc ⌊x / δ⌋ ⌊(x + w) / δ⌋).card : ℝ) ≤ 3 * w / δ := by
    have hc := Submission.Obl.k4_scalar_initial_true_horizon.card_Icc_floor_le
      (show x / δ ≤ (x + w) / δ by gcongr; linarith)
    have heq : (x + w) / δ - x / δ + 2 = w / δ + 2 := by ring
    rw [heq] at hc
    apply hc.trans
    apply (le_div_iff₀ hδ).mpr
    have heq' : (w / δ + 2) * δ = w + 2 * δ := by field_simp
    rw [heq']
    linarith
  have hy (q : ℤ × ℤ) :
      ((floorBand δ (c 0 + c 1 * (δ * q.1) + c 2 * (δ * q.2)) (B + 2 * K * δ)).card : ℝ) ≤
        8 * K * B / δ := by
    apply (floorBand_card hδ (by positivity)).trans
    apply (le_div_iff₀ hδ).mpr
    have heq : (2 * (B + 2 * K * δ) / δ + 2) * δ = 2 * B + 4 * K * δ + 2 * δ := by field_simp; ring
    rw [heq]
    linarith
  have hh (q : BaseGridIndex) :
      ((floorBand a (affineBaseValue L (gridPoint δ q)) (2 * K * a)).card : ℝ) ≤ 6 * K := by
    apply (floorBand_card ha (by positivity)).trans
    have heq : 2 * (2 * K * a) / a + 2 = 4 * K + 2 := by field_simp; ring
    rw [heq]
    linarith
  have hbase : ((rectangleBaseCover δ w B K t₀ Z₀ c).card : ℝ) ≤
      (3 * w / δ) ^ 2 * (8 * K * B / δ) := by
    unfold rectangleBaseCover
    rw [card_sigma]
    push_cast
    calc
      _ ≤ ∑ _q ∈ ((Icc ⌊t₀ / δ⌋ ⌊(t₀ + w) / δ⌋) ×ˢ
          (Icc ⌊Z₀ / δ⌋ ⌊(Z₀ + w) / δ⌋)), (8 * K * B / δ) :=
        sum_le_sum (fun q _ => hy q)
      _ = ((Icc ⌊t₀ / δ⌋ ⌊(t₀ + w) / δ⌋).card : ℝ) *
          ((Icc ⌊Z₀ / δ⌋ ⌊(Z₀ + w) / δ⌋).card : ℝ) * (8 * K * B / δ) := by simp [mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [pow_two]
        exact mul_le_mul (htime t₀) (htime Z₀) (Nat.cast_nonneg _) (by positivity)
  unfold rectangleJointCover
  rw [card_sigma]
  push_cast
  calc
    _ ≤ ∑ _q ∈ rectangleBaseCover δ w B K t₀ Z₀ c, (6 * K) := sum_le_sum (fun q _ => hh q)
    _ = ((rectangleBaseCover δ w B K t₀ Z₀ c).card : ℝ) * (6 * K) := by simp
    _ ≤ ((3 * w / δ) ^ 2 * (8 * K * B / δ)) * (6 * K) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = _ := by field_simp; ring

/-- A bounded affine predictor changes by at most 3K times the base mesh
when all three coordinates are replaced by their lower grid corners. -/
theorem affineBaseValue_grid_error
    (δ K : ℝ) (L : Fin 4 → ℝ) (p : Fin 3 → ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hL : ∀ i : Fin 3, |L i.succ| ≤ K) :
    |affineBaseValue L p - affineBaseValue L (gridPoint δ (baseGridIndex δ p))| ≤ 3 * K * δ := by
  have hg : ∀ i : Fin 3, |p i - gridPoint δ (baseGridIndex δ p) i| ≤ δ := by
    intro i
    fin_cases i <;> exact Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hδ _
  have heq : affineBaseValue L p - affineBaseValue L (gridPoint δ (baseGridIndex δ p)) =
      ∑ i : Fin 3, L i.succ * (p i - gridPoint δ (baseGridIndex δ p) i) := by
    unfold affineBaseValue
    rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 3, |L i.succ * (p i - gridPoint δ (baseGridIndex δ p) i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, K * δ := sum_le_sum (fun i _ => by
      rw [abs_mul]; exact mul_le_mul (hL i) (hg i) (abs_nonneg _) hK)
    _ = _ := by simp; ring

theorem mem_rectangleJointCover
    (δ a w B K t₀ Z₀ : ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (p : Fin 3 → ℝ) (value : ℝ) (hδ : 0 < δ) (ha : 0 < a) (hK : 0 ≤ K)
    (hmesh : 3 * δ ≤ a) (hc₁ : |c 1| ≤ K) (hc₂ : |c 2| ≤ K)
    (hL : ∀ i : Fin 3, |L i.succ| ≤ K)
    (ht : p 0 ∈ Set.Icc t₀ (t₀ + w)) (hZ : p 1 ∈ Set.Icc Z₀ (Z₀ + w))
    (hY : |p 2 - c 0 - c 1 * p 0 - c 2 * p 1| ≤ B)
    (hfit : |value - affineBaseValue L p| ≤ K * a) :
    jointGridIndex δ a p value ∈ rectangleJointCover δ a w B K t₀ Z₀ c L := by
  have hround (i : Fin 3) : |p i - δ * (⌊p i / δ⌋ : ℝ)| ≤ δ :=
    Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hδ _
  have hYgrid : |p 2 - (c 0 + c 1 * (δ * (⌊p 0 / δ⌋ : ℝ)) +
      c 2 * (δ * (⌊p 1 / δ⌋ : ℝ)))| ≤ B + 2 * K * δ := by
    have hmul₁ : |c 1 * (p 0 - δ * (⌊p 0 / δ⌋ : ℝ))| ≤ K * δ := by
      rw [abs_mul]; exact mul_le_mul hc₁ (hround 0) (abs_nonneg _) hK
    have hmul₂ : |c 2 * (p 1 - δ * (⌊p 1 / δ⌋ : ℝ))| ≤ K * δ := by
      rw [abs_mul]; exact mul_le_mul hc₂ (hround 1) (abs_nonneg _) hK
    calc
      _ = |(p 2 - c 0 - c 1 * p 0 - c 2 * p 1) +
          c 1 * (p 0 - δ * (⌊p 0 / δ⌋ : ℝ)) + c 2 * (p 1 - δ * (⌊p 1 / δ⌋ : ℝ))| := by congr 1; ring
      _ ≤ |p 2 - c 0 - c 1 * p 0 - c 2 * p 1| +
          |c 1 * (p 0 - δ * (⌊p 0 / δ⌋ : ℝ))| + |c 2 * (p 1 - δ * (⌊p 1 / δ⌋ : ℝ))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ B + K * δ + K * δ := add_le_add (add_le_add hY hmul₁) hmul₂
      _ = _ := by ring
  have hhidden : |value - affineBaseValue L (gridPoint δ (baseGridIndex δ p))| ≤ 2 * K * a := by
    have hg := affineBaseValue_grid_error δ K L p hδ hK hL
    have hm := mul_le_mul_of_nonneg_left hmesh hK
    have ht := abs_sub_le value (affineBaseValue L p) (affineBaseValue L (gridPoint δ (baseGridIndex δ p)))
    linarith
  apply mem_sigma.mpr
  refine ⟨?_, mem_floorBand ha hhidden⟩
  apply mem_sigma.mpr
  refine ⟨mem_product.mpr ⟨mem_Icc.mpr ?_, mem_Icc.mpr ?_⟩, mem_floorBand hδ hYgrid⟩
  · exact ⟨Int.floor_mono (div_le_div_of_nonneg_right ht.1 hδ.le),
      Int.floor_mono (div_le_div_of_nonneg_right ht.2 hδ.le)⟩
  · exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hZ.1 hδ.le),
      Int.floor_mono (div_le_div_of_nonneg_right hZ.2 hδ.le)⟩

/-- Integrating original fine joint caps over the actual transverse range
retains their unchanged external palette factor. No representative-time
measure or pure base density hypothesis is used. -/
theorem original_joint_cap_rectangle
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (U : Set Y)
    (point : Y → Fin 3 → ℝ) (value : Y → ℝ) (velocity : Y → ℤ) (j : ℤ)
    (δ a w B K t₀ Z₀ C Z : ℝ) (palette : ℝ≥0∞)
    (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (hδ : 0 < δ) (ha : 0 < a) (hK : 1 ≤ K) (hC : 0 ≤ C) (hZ : 0 ≤ Z)
    (hδw : δ ≤ w) (hδB : δ ≤ B) (hmesh : 3 * δ ≤ a)
    (hc₁ : |c 1| ≤ K) (hc₂ : |c 2| ≤ K) (hL : ∀ i : Fin 3, |L i.succ| ≤ K)
    (ht : ∀ y ∈ U, point y 0 ∈ Set.Icc t₀ (t₀ + w))
    (hpos : ∀ y ∈ U, point y 1 ∈ Set.Icc Z₀ (Z₀ + w))
    (htrans : ∀ y ∈ U, |point y 2 - c 0 - c 1 * point y 0 - c 2 * point y 1| ≤ B)
    (hfit : ∀ y ∈ U, |value y - affineBaseValue L (point y)| ≤ K * a)
    (hvel : ∀ y ∈ U, velocity y = j)
    (hcap : ∀ q : JointGridIndex,
      μ {y | jointGridIndex δ a (point y) (value y) = q ∧ velocity y = j} ≤
        ENNReal.ofReal (C * δ ^ 3 * Z) * palette) :
    μ U ≤ ENNReal.ofReal (432 * C * K ^ 2 * w ^ 2 * B * Z) * palette := by
  let F := rectangleJointCover δ a w B K t₀ Z₀ c L
  let cell := fun q : JointGridIndex =>
    {y | jointGridIndex δ a (point y) (value y) = q ∧ velocity y = j}
  have hcover : U ⊆ ⋃ q ∈ F, cell q := by
    intro y hy
    refine Set.mem_iUnion₂.mpr ⟨jointGridIndex δ a (point y) (value y), ?_, rfl, hvel y hy⟩
    exact mem_rectangleJointCover δ a w B K t₀ Z₀ c L (point y) (value y)
      hδ ha (by linarith) hmesh hc₁ hc₂ hL (ht y hy) (hpos y hy) (htrans y hy) (hfit y hy)
  have hcount := rectangleJointCover_card δ a w B K t₀ Z₀ c L hδ ha hK hδw hδB
  have hδpow : 0 < δ ^ 3 := pow_pos hδ _
  have hscalar : (F.card : ℝ) * (C * δ ^ 3 * Z) ≤ 432 * C * K ^ 2 * w ^ 2 * B * Z := by
    have hc := (le_div_iff₀ hδpow).mp hcount
    have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg hC hZ)
    convert hm using 1 <;> ring
  calc
    _ ≤ μ (⋃ q ∈ F, cell q) := measure_mono hcover
    _ ≤ ∑ q ∈ F, μ (cell q) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ F, ENNReal.ofReal (C * δ ^ 3 * Z) * palette := sum_le_sum (fun q _ => hcap q)
    _ = ENNReal.ofReal ((F.card : ℝ) * (C * δ ^ 3 * Z)) * palette := by
      simp only [sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hscalar) (zero_le : 0 ≤ palette)

/-- The same integration theorem accepts the exact three-coordinate base
cells and scalar bins appearing in the frozen original joint cap. -/
theorem original_native_joint_cap_rectangle
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (U : Set Y)
    (point : Y → Fin 3 → ℝ) (value : Y → ℝ) (velocity : Y → ℤ) (j : ℤ)
    (δ a w B K t₀ Z₀ C Z : ℝ) (palette : ℝ≥0∞)
    (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (hδ : 0 < δ) (ha : 0 < a) (hK : 1 ≤ K) (hC : 0 ≤ C) (hZ : 0 ≤ Z)
    (hδw : δ ≤ w) (hδB : δ ≤ B) (hmesh : 3 * δ ≤ a)
    (hc₁ : |c 1| ≤ K) (hc₂ : |c 2| ≤ K) (hL : ∀ i : Fin 3, |L i.succ| ≤ K)
    (ht : ∀ y ∈ U, point y 0 ∈ Set.Icc t₀ (t₀ + w))
    (hpos : ∀ y ∈ U, point y 1 ∈ Set.Icc Z₀ (Z₀ + w))
    (htrans : ∀ y ∈ U, |point y 2 - c 0 - c 1 * point y 0 - c 2 * point y 1| ≤ B)
    (hfit : ∀ y ∈ U, |value y - affineBaseValue L (point y)| ≤ K * a)
    (hvel : ∀ y ∈ U, velocity y = j)
    (hcap : ∀ (q : Fin 3 → ℤ) (b : ℤ),
      μ {y | (fun e => ⌊point y e / δ⌋) = q ∧ ⌊value y / a⌋ = b ∧ velocity y = j} ≤
        ENNReal.ofReal (C * δ ^ 3 * Z) * palette) :
    μ U ≤ ENNReal.ofReal (432 * C * K ^ 2 * w ^ 2 * B * Z) * palette := by
  apply original_joint_cap_rectangle μ U point value velocity j δ a w B K t₀ Z₀ C Z palette c L
    hδ ha hK hC hZ hδw hδB hmesh hc₁ hc₂ hL ht hpos htrans hfit hvel
  intro q
  let q₀ : Fin 3 → ℤ := ![q.1.1.1, q.1.1.2, q.1.2]
  apply le_trans (measure_mono ?_) (hcap q₀ q.2)
  intro y hy
  refine ⟨?_, congrArg (fun z : JointGridIndex => z.2) hy.1, hy.2⟩
  funext e
  fin_cases e
  · exact congrArg (fun z : JointGridIndex => z.1.1.1) hy.1
  · exact congrArg (fun z : JointGridIndex => z.1.1.2) hy.1
  · exact congrArg (fun z : JointGridIndex => z.1.2) hy.1

end

end Submission.Obl.k4_critical_conditional_row_preparation
