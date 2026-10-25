import Mathlib
import Submission.Obl.k4_oss_collision_cauchy_schwarz
import Submission.Obl.k4_oss_weighted_level_transfer.Interface

/-!
# Discretization half of o043

Round the probability law `α` on `[-1, 1]` to the grid `δ ℤ`: the cells are
`[x, x + δ)` for `x` in `grid δ`, with masses `cellMass α δ x`.  The cell data
satisfy all finite hypotheses of `FiniteTransfer`, and the projected collision
of `α` at window `4 δ` is dominated by the finite collision sum at window `7 δ`
(`collision_le_collisionSum`).  Hence `FiniteTransfer s γ` implies the frozen
conclusion of o043 (`conclusion_of_finiteTransfer`).

The square-sum bound uses `cell_energy_le_collision` of the accepted o023.
-/

open MeasureTheory Set

namespace Submission.Obl.k4_oss_weighted_level_transfer

/-- Indices of the grid cells `[δ j, δ j + δ)` that meet `[-1, 1]` (and a few more). -/
noncomputable def gridIdx (δ : ℝ) : Finset ℤ := Finset.Icc (-⌊1 / δ⌋ - 1) ⌊1 / δ⌋

/-- Left corners of the grid cells. -/
noncomputable def grid (δ : ℝ) : Finset ℝ := (gridIdx δ).image (fun j : ℤ => δ * j)

/-- The `α`-mass of the cell `[x, x + δ)`. -/
noncomputable def cellMass (α : Measure ℝ) (δ x : ℝ) : ℝ := (α (Ico x (x + δ))).toReal

theorem grid_injective {δ : ℝ} (hδ : 0 < δ) :
    Function.Injective (fun j : ℤ => δ * (j : ℝ)) := by
  intro i j h
  have := mul_left_cancel₀ hδ.ne' h
  exact_mod_cast this

theorem floor_mem_gridIdx {δ y : ℝ} (hδ : 0 < δ) (hy : y ∈ Icc (-1 : ℝ) 1) :
    ⌊y / δ⌋ ∈ gridIdx δ := by
  rw [gridIdx, Finset.mem_Icc]
  constructor
  · have h1 : -(1 / δ) ≤ y / δ := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right hy.1 hδ.le
    have h3 : (1 / δ) < ⌊1 / δ⌋ + 1 := Int.lt_floor_add_one _
    have h4 : y / δ - 1 < ⌊y / δ⌋ := Int.sub_one_lt_floor _
    have : ((-⌊1 / δ⌋ - 2 : ℤ) : ℝ) < ⌊y / δ⌋ := by push_cast; linarith
    have := Int.cast_lt.mp this
    omega
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right hy.2 hδ.le)

theorem mem_cell_floor {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    y ∈ Ico (δ * (⌊y / δ⌋ : ℝ)) (δ * (⌊y / δ⌋ : ℝ) + δ) := by
  have h1 : (⌊y / δ⌋ : ℝ) ≤ y / δ := Int.floor_le _
  have h2 : y / δ < ⌊y / δ⌋ + 1 := Int.lt_floor_add_one _
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hδ.le
    rwa [mul_div_cancel₀ _ hδ.ne'] at this
  · have := mul_lt_mul_of_pos_left h2 hδ
    rw [mul_div_cancel₀ _ hδ.ne'] at this
    linarith

/-- Every point of `[-1, 1]` lies in a grid cell. -/
theorem exists_grid_cell {δ y : ℝ} (hδ : 0 < δ) (hy : y ∈ Icc (-1 : ℝ) 1) :
    ∃ x ∈ grid δ, y ∈ Ico x (x + δ) :=
  ⟨δ * (⌊y / δ⌋ : ℝ), Finset.mem_image_of_mem _ (floor_mem_gridIdx hδ hy), mem_cell_floor hδ y⟩

theorem grid_sep {δ : ℝ} (hδ : 0 < δ) :
    ∀ x ∈ grid δ, ∀ y ∈ grid δ, x ≠ y → δ ≤ dist x y := by
  intro x hx y hy hxy
  simp only [grid, Finset.mem_image] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨j, -, rfl⟩ := hy
  have hij : i ≠ j := fun h => hxy (by rw [h])
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hδ]
  have : (1 : ℝ) ≤ |(i : ℝ) - j| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
  nlinarith

theorem grid_abs_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : ∀ x ∈ grid δ, |x| ≤ 2 := by
  intro x hx
  simp only [grid, Finset.mem_image, gridIdx, Finset.mem_Icc] at hx
  obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hx
  have hf : (⌊1 / δ⌋ : ℝ) ≤ 1 / δ := Int.floor_le _
  have hj1' : (-⌊1 / δ⌋ - 1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hj2' : (j : ℝ) ≤ ⌊1 / δ⌋ := by exact_mod_cast hj2
  have hd : δ * (1 / δ) = 1 := by field_simp
  rw [abs_le]
  constructor <;> nlinarith

theorem grid_card_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : ((grid δ).card : ℝ) ≤ 4 / δ := by
  have h1 : (grid δ).card ≤ (gridIdx δ).card := Finset.card_image_le
  have h2 : ((gridIdx δ).card : ℝ) = 2 * ⌊1 / δ⌋ + 2 := by
    rw [gridIdx, Int.card_Icc]
    have h0 : (0 : ℤ) ≤ ⌊1 / δ⌋ := Int.floor_nonneg.mpr (by positivity)
    rw [show ⌊1 / δ⌋ + 1 - (-⌊1 / δ⌋ - 1) = 2 * ⌊1 / δ⌋ + 2 by ring]
    have : (0 : ℤ) ≤ 2 * ⌊1 / δ⌋ + 2 := by omega
    rw [show ((2 * ⌊1 / δ⌋ + 2).toNat : ℝ) = ((2 * ⌊1 / δ⌋ + 2 : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg this]
    push_cast; ring
  have hf : (⌊1 / δ⌋ : ℝ) ≤ 1 / δ := Int.floor_le _
  have h3 : 2 * (1 / δ) + 2 ≤ 4 / δ := by
    have h1d : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have : 4 / δ = 4 * (1 / δ) := by ring
    rw [this]; linarith
  calc ((grid δ).card : ℝ) ≤ (gridIdx δ).card := by exact_mod_cast h1
    _ = 2 * ⌊1 / δ⌋ + 2 := h2
    _ ≤ 2 * (1 / δ) + 2 := by linarith
    _ ≤ 4 / δ := h3


theorem cells_pairwiseDisjoint {δ : ℝ} (hδ : 0 < δ) :
    (grid δ : Set ℝ).PairwiseDisjoint (fun x => Ico x (x + δ)) := by
  intro x hx y hy hxy
  have h := grid_sep hδ x hx y hy hxy
  rw [Function.onFun, Set.disjoint_left]
  intro z hz1 hz2
  rw [Real.dist_eq] at h
  rcases le_total x y with hle | hle
  · rw [abs_of_nonpos (by linarith)] at h; linarith [hz1.2, hz2.1]
  · rw [abs_of_nonneg (by linarith)] at h; linarith [hz1.1, hz2.2]

theorem sum_cell_measure {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) (F : Finset ℝ)
    (hF : F ⊆ grid δ) :
    ∑ x ∈ F, α (Ico x (x + δ)) = α (⋃ x ∈ F, Ico x (x + δ)) := by
  rw [measure_biUnion_finset]
  · exact (cells_pairwiseDisjoint hδ).subset (by exact_mod_cast hF)
  · intro x _; exact measurableSet_Ico

theorem sum_cellMass_eq {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) [IsFiniteMeasure α]
    (F : Finset ℝ) (hF : F ⊆ grid δ) :
    ∑ x ∈ F, cellMass α δ x = (α (⋃ x ∈ F, Ico x (x + δ))).toReal := by
  rw [← sum_cell_measure hδ α F hF, ENNReal.toReal_sum]
  · rfl
  · intro x _; exact measure_ne_top _ _

theorem sum_cellMass_le_one {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) [IsProbabilityMeasure α] :
    ∑ x ∈ grid δ, cellMass α δ x ≤ 1 := by
  rw [sum_cellMass_eq hδ α _ subset_rfl]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem cellMass_nonneg (α : Measure ℝ) (δ x : ℝ) : 0 ≤ cellMass α δ x := ENNReal.toReal_nonneg

/-- The interval cap of the cell masses, from the Frostman bound of `α`. -/
theorem cellMass_cap {δ ε s : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hs : 0 < s) (hs1 : s ≤ 1)
    (α : Measure ℝ) [IsProbabilityMeasure α]
    (hαF : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      α (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s))
    (z u : ℝ) (hu : δ ≤ u) (hu1 : u ≤ 1) :
    ∑ x ∈ (grid δ).filter (fun x => dist x z ≤ u), cellMass α δ x ≤ 2 * δ ^ (-ε) * u ^ s := by
  rw [sum_cellMass_eq hδ α _ (Finset.filter_subset _ _)]
  have hsub : (⋃ x ∈ (grid δ).filter (fun x => dist x z ≤ u), Ico x (x + δ)) ⊆
      Icc ((z + δ / 2) - (u + δ / 2)) ((z + δ / 2) + (u + δ / 2)) := by
    intro y hy
    simp only [mem_iUnion, Finset.mem_filter, exists_prop] at hy
    obtain ⟨x, ⟨-, hx⟩, hy⟩ := hy
    rw [Real.dist_eq, abs_le] at hx
    constructor <;> linarith [hy.1, hy.2]
  have hm := measure_mono (μ := α) hsub
  have hδ1 : δ ≤ 1 := hu.trans hu1
  have hpow : 1 ≤ δ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hus : 0 < u ^ s := Real.rpow_pos_of_pos (by linarith) _
  rcases le_or_gt (u + δ / 2) 1 with hv | hv
  · have h1 := hm.trans (hαF _ _ (by linarith) hv)
    have h2 : (α (⋃ x ∈ (grid δ).filter (fun x => dist x z ≤ u), Ico x (x + δ))).toReal ≤
        δ ^ (-ε) * (u + δ / 2) ^ s :=
      ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg (by linarith) _)) h1
    have h3 : (u + δ / 2) ^ s ≤ (2 * u) ^ s :=
      Real.rpow_le_rpow (by linarith) (by linarith) hs.le
    have h4 : (2 * u) ^ s = 2 ^ s * u ^ s := Real.mul_rpow (by norm_num) (by linarith)
    have h5 : (2 : ℝ) ^ s ≤ 2 := by
      calc (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
        _ = 2 := Real.rpow_one 2
    calc _ ≤ δ ^ (-ε) * (u + δ / 2) ^ s := h2
      _ ≤ δ ^ (-ε) * (2 ^ s * u ^ s) := by
          rw [← h4]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ δ ^ (-ε) * (2 * u ^ s) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 hus.le) (by positivity)
      _ = 2 * δ ^ (-ε) * u ^ s := by ring
  · have h1 : (α (⋃ x ∈ (grid δ).filter (fun x => dist x z ≤ u), Ico x (x + δ))).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hu2 : 1 / 2 ≤ u := by linarith
    have h2 : (1 / 2 : ℝ) ≤ u ^ s := by
      calc (1 / 2 : ℝ) = (1 / 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 2) ^ s := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hs1
        _ ≤ u ^ s := Real.rpow_le_rpow (by norm_num) hu2 hs.le
    calc _ ≤ 1 := h1
      _ ≤ 2 * 1 * u ^ s := by linarith
      _ ≤ 2 * δ ^ (-ε) * u ^ s := by gcongr

theorem Ico_eq_cell {δ : ℝ} (hδ : 0 < δ) (j : ℤ) :
    Ico (δ * (j : ℝ)) (δ * (j : ℝ) + δ) = Submission.Obl.k4_oss_collision_cauchy_schwarz.cell δ j := by
  ext y
  simp only [Submission.Obl.k4_oss_collision_cauchy_schwarz.cell, mem_Ico, mem_ofPred_eq,
    Int.floor_eq_iff]
  rw [le_div_iff₀ hδ, div_lt_iff₀ hδ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The square sum of the cell masses is at most the collision probability. -/
theorem sum_cellMass_sq_le {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) [IsProbabilityMeasure α] :
    ∑ x ∈ grid δ, cellMass α δ x ^ 2 ≤
      ((α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal := by
  have hQ := Submission.Obl.k4_oss_collision_cauchy_schwarz.cell_energy_le_collision α hδ
  have h1 : ∑ x ∈ grid δ, cellMass α δ x ^ 2 =
      (∑ j ∈ gridIdx δ, α (Submission.Obl.k4_oss_collision_cauchy_schwarz.cell δ j) *
        α (Submission.Obl.k4_oss_collision_cauchy_schwarz.cell δ j)).toReal := by
    rw [grid, Finset.sum_image (fun i _ j _ h => grid_injective hδ h), ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [cellMass, Ico_eq_cell hδ, ENNReal.toReal_mul, sq]
    · intro j _; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [h1]
  exact ENNReal.toReal_mono (measure_ne_top _ _) ((ENNReal.sum_le_tsum _).trans hQ)


/-- Rounding to the grid: the window `4 δ` becomes at most `7 δ`. -/
theorem round_window {δ t q₁ q₂ q₃ q₄ x₁ x₂ x₃ x₄ : ℝ} (ht : |t| ≤ 1)
    (h₁ : q₁ ∈ Ico x₁ (x₁ + δ)) (h₂ : q₂ ∈ Ico x₂ (x₂ + δ))
    (h₃ : q₃ ∈ Ico x₃ (x₃ + δ)) (h₄ : q₄ ∈ Ico x₄ (x₄ + δ))
    (hq : |(q₁ - q₂) - 2 * t * (q₃ - q₄)| ≤ 4 * δ) :
    |(x₁ - x₂) - 2 * t * (x₃ - x₄)| ≤ 7 * δ := by
  have hid : (x₁ - x₂) - 2 * t * (x₃ - x₄) = ((q₁ - q₂) - 2 * t * (q₃ - q₄)) -
      ((q₁ - x₁) - (q₂ - x₂)) + 2 * (t * ((q₃ - x₃) - (q₄ - x₄))) := by ring
  have hC : |t * ((q₃ - x₃) - (q₄ - x₄))| ≤ δ := by
    rw [abs_mul]
    have : |(q₃ - x₃) - (q₄ - x₄)| ≤ δ := by
      rw [abs_le]; constructor <;> linarith [h₃.1, h₃.2, h₄.1, h₄.2]
    calc |t| * |(q₃ - x₃) - (q₄ - x₄)| ≤ 1 * δ :=
          mul_le_mul ht this (abs_nonneg _) zero_le_one
      _ = δ := one_mul δ
  rw [hid]
  rw [abs_le] at hq hC ⊢
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, hq.1, hq.2, hC.1, hC.2]

/-- The projected collision of `α` is dominated by the finite collision sum of
its cell masses. -/
theorem collision_le_collisionSum {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ 1)
    (α : Measure ℝ) [IsProbabilityMeasure α] (hα : α (Icc (-1 : ℝ) 1)ᶜ = 0) :
    ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) |
        |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ} ≤
      ENNReal.ofReal (collisionSum (grid δ) (cellMass α δ) δ t) := by
  set μ := (α.prod α).prod (α.prod α) with hμ
  set S := grid δ
  set K : Set ℝ := Icc (-1 : ℝ) 1
  set Box : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (K ×ˢ K) ×ˢ (K ×ˢ K)
  set I := ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter (fun x : (ℝ × ℝ) × (ℝ × ℝ) =>
    |(x.1.1 - x.1.2) - 2 * t * (x.2.1 - x.2.2)| ≤ 7 * δ)
  let cellBox : (ℝ × ℝ) × (ℝ × ℝ) → Set ((ℝ × ℝ) × (ℝ × ℝ)) := fun x =>
    (Ico x.1.1 (x.1.1 + δ) ×ˢ Ico x.1.2 (x.1.2 + δ)) ×ˢ
      (Ico x.2.1 (x.2.1 + δ) ×ˢ Ico x.2.2 (x.2.2 + δ))
  have hsub : {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ} ⊆
      Boxᶜ ∪ ⋃ x ∈ I, cellBox x := by
    intro q hq
    by_cases hB : q ∈ Box
    · right
      obtain ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ := hB
      obtain ⟨x₁, hx₁, h₁⟩ := exists_grid_cell hδ hq1
      obtain ⟨x₂, hx₂, h₂⟩ := exists_grid_cell hδ hq2
      obtain ⟨x₃, hx₃, h₃⟩ := exists_grid_cell hδ hq3
      obtain ⟨x₄, hx₄, h₄⟩ := exists_grid_cell hδ hq4
      simp only [mem_iUnion, exists_prop]
      refine ⟨((x₁, x₂), (x₃, x₄)), ?_, ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩⟩
      simp only [I, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨⟨hx₁, hx₂⟩, ⟨hx₃, hx₄⟩⟩, round_window ht h₁ h₂ h₃ h₄ hq⟩
    · exact Or.inl hB
  have hK : α K = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).mp hα
  have hBox : μ Boxᶜ = 0 := by
    have hBm : MeasurableSet Box :=
      (measurableSet_Icc.prod measurableSet_Icc).prod (measurableSet_Icc.prod measurableSet_Icc)
    rw [prob_compl_eq_zero_iff hBm, hμ]
    simp only [Box, Measure.prod_prod, hK, mul_one]
  have hnn : ∀ x ∈ I, 0 ≤ cellMass α δ x.1.1 * cellMass α δ x.1.2 *
      (cellMass α δ x.2.1 * cellMass α δ x.2.2) := fun x _ => by
    unfold cellMass; positivity
  calc μ {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ}
      ≤ μ (Boxᶜ ∪ ⋃ x ∈ I, cellBox x) := measure_mono hsub
    _ ≤ μ Boxᶜ + μ (⋃ x ∈ I, cellBox x) := measure_union_le _ _
    _ = μ (⋃ x ∈ I, cellBox x) := by rw [hBox, zero_add]
    _ ≤ ∑ x ∈ I, μ (cellBox x) := measure_biUnion_finset_le _ _
    _ = ∑ x ∈ I, ENNReal.ofReal (cellMass α δ x.1.1 * cellMass α δ x.1.2 *
          (cellMass α δ x.2.1 * cellMass α δ x.2.2)) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [cellBox, hμ, Measure.prod_prod, cellMass]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = ENNReal.ofReal (∑ x ∈ I, cellMass α δ x.1.1 * cellMass α δ x.1.2 *
          (cellMass α δ x.2.1 * cellMass α δ x.2.2)) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
    _ = ENNReal.ofReal (collisionSum S (cellMass α δ) δ t) := by
        congr 1
        simp only [I, collisionSum, Finset.sum_filter, Finset.sum_product]
        apply Finset.sum_congr rfl; intro x₁ _
        apply Finset.sum_congr rfl; intro x₂ _
        apply Finset.sum_congr rfl; intro x₃ _
        apply Finset.sum_congr rfl; intro x₄ _
        split_ifs <;> ring


/-- The discretization half of o043: the finite transfer gives the frozen conclusion. -/
theorem conclusion_of_finiteTransfer (s γ : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hT : FiniteTransfer s γ) :
    ∃ c ε r : ℝ, 0 < c ∧ 0 < ε ∧ 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ α ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure ν → α (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → α (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ (s))) → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (4 * δ ^ (-ε) * u ^ (s))) → ENNReal.ofReal (δ ^ (1 - γ)) ≤ (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} → MeasureTheory.lintegral ν (fun t : ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ}) ≤ ENNReal.ofReal (δ ^ c) * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
  obtain ⟨c, ε, r, hc, hε, hr, hr1, hT⟩ := hT
  refine ⟨c, ε, r, hc, hε, hr, hr1, ?_⟩
  intro δ hδ hδr α ν hα hν hαs hνs hαF hνF hQ
  have hδ1 : δ ≤ 1 := by linarith
  have hQtop : (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≠ ⊤ := measure_ne_top _ _
  have key := hT δ hδ hδr (grid δ) (cellMass α δ)
    ((α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal (cellMass_nonneg α δ) (grid_sep hδ)
    (grid_abs_le hδ hδ1) (grid_card_le hδ hδ1) (sum_cellMass_le_one hδ α)
    (cellMass_cap hδ hε hs hs1 α hαF) (sum_cellMass_sq_le hδ α)
    ((ENNReal.ofReal_le_iff_le_toReal hQtop).mp hQ) ν hν hνs hνF
  have hae : ∀ᵐ t ∂ν, t ∈ Icc (1 / 4 : ℝ) 1 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνs] with t ht
    simpa using ht
  calc MeasureTheory.lintegral ν (fun t : ℝ => ((α.prod α).prod (α.prod α))
        {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ})
      ≤ ∫⁻ t, ENNReal.ofReal (collisionSum (grid δ) (cellMass α δ) δ t) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hae] with t ht
        have ht' : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        exact collision_le_collisionSum hδ ht' α hαs
    _ ≤ ENNReal.ofReal (δ ^ c * ((α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal) := key
    _ = ENNReal.ofReal (δ ^ c) * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ENNReal.ofReal_toReal hQtop]

end Submission.Obl.k4_oss_weighted_level_transfer
