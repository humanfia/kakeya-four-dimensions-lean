-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.CellCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.StickyBranch

/-!
# Counting cells

* `card_subcells_le`: inside one cell of size `m s`, the members of a set occupy at most `m⁶`
  cells of size `s` (the grids nest; each of the six coordinates has `m` refinements).
* `card_cells_le`: tubes whose foot lies in the closed unit ball occupy at most
  `(2/s + 2)⁶` cells of size `s`.

These turn balanced populations into the step bounds of the cell-count profile
(`Profile.profile_dichotomy`).
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- The integers `k` with `k / m = K` (integer division, `m > 0`) are the `m` integers
`K m, …, K m + m - 1`. -/
lemma int_div_eq_mem {m : ℕ} (hm : 0 < m) {k K : ℤ} (h : k / (m : ℤ) = K) :
    k ∈ Finset.Ico (K * m) (K * m + m) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  rw [Finset.mem_Ico]
  constructor
  · rw [← h]; exact Int.ediv_mul_le k hm'.ne'
  · rw [← h]
    have := Int.lt_ediv_add_one_mul_self k hm'
    linarith

/-- Inside one cell of size `m s`, the members of `S` occupy at most `m⁶` cells of size `s`. -/
theorem card_subcells_le {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m) {n : ℕ} (x v : Fin n → Sp)
    (S : Finset (Fin n)) (K : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    ((S.filter (fun i => lineCell ((m : ℝ) * s) (x i) (v i) = K)).image
      (fun i => lineCell s (x i) (v i))).card ≤ m ^ 6 := by
  classical
  -- the fine cells lie in a box of `m⁶` index vectors
  let box : Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
    (Fintype.piFinset fun c => Finset.Ico (K.1 c * m) (K.1 c * m + m)) ×ˢ
      (Fintype.piFinset fun c => Finset.Ico (K.2 c * m) (K.2 c * m + m))
  have hsub : (S.filter (fun i => lineCell ((m : ℝ) * s) (x i) (v i) = K)).image
      (fun i => lineCell s (x i) (v i)) ⊆ box := by
    intro κ hκ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hκ
    have hK := (Finset.mem_filter.1 hi).2
    have hcoord : ∀ (y : Sp) (c : Fin 3), cellIdx ((m : ℝ) * s) y c = cellIdx s y c / (m : ℤ) := by
      intro y c
      unfold cellIdx
      have e : y c / ((m : ℝ) * s) = (y c / s) / (m : ℝ) := by field_simp
      rw [e, Int.floor_div_natCast]
    simp only [box, Finset.mem_product, Fintype.mem_piFinset]
    unfold lineCell at hK ⊢
    constructor
    · intro c
      apply int_div_eq_mem hm
      rw [← hcoord]
      exact congrFun (congrArg Prod.fst hK) c
    · intro c
      apply int_div_eq_mem hm
      rw [← hcoord]
      exact congrFun (congrArg Prod.snd hK) c
  calc _ ≤ box.card := Finset.card_le_card hsub
    _ = m ^ 6 := by
        simp only [box, Finset.card_product, Fintype.card_piFinset, Int.card_Ico,
          add_sub_cancel_left, Int.toNat_natCast, Fin.prod_const]
        ring

/-- Integers `⌊a / s⌋` with `|a| ≤ 1` lie in an interval of at most `2/s + 2` integers. -/
lemma floor_mem_Icc {s a : ℝ} (hs : 0 < s) (ha : |a| ≤ 1) :
    ⌊a / s⌋ ∈ Finset.Icc ⌊-1 / s⌋ ⌊1 / s⌋ := by
  rw [Finset.mem_Icc]
  rw [abs_le] at ha
  constructor
  · exact Int.floor_mono (div_le_div_of_nonneg_right ha.1 hs.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right ha.2 hs.le)

lemma card_Icc_floor_le {s : ℝ} (hs : 0 < s) :
    ((Finset.Icc ⌊-1 / s⌋ ⌊1 / s⌋).card : ℝ) ≤ 2 / s + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le (1 / s)
  have h2 := Int.lt_floor_add_one (-1 / s)
  have hnn : (0 : ℤ) ≤ ⌊1 / s⌋ + 1 - ⌊-1 / s⌋ := by
    have : ⌊-1 / s⌋ ≤ ⌊1 / s⌋ := Int.floor_mono (by
      rw [div_le_div_iff_of_pos_right hs]; norm_num)
    omega
  have e1 : (((⌊1 / s⌋ + 1 - ⌊-1 / s⌋).toNat : ℕ) : ℝ) = ((⌊1 / s⌋ + 1 - ⌊-1 / s⌋ : ℤ) : ℝ) := by
    have := Int.toNat_of_nonneg hnn
    exact_mod_cast this
  rw [e1]
  push_cast
  have e : (-1 : ℝ) / s = -(1 / s) := by ring
  have e2 : (2 : ℝ) / s = 2 * (1 / s) := by ring
  linarith

/-- Tubes whose foot lies in the closed unit ball and whose direction is a unit vector occupy at
most `(2/s + 2)⁶` cells of size `s`. -/
theorem card_cells_le {s : ℝ} (hs : 0 < s) {n : ℕ} (x v : Fin n → Sp) (S : Finset (Fin n))
    (hfoot : ∀ i ∈ S, ‖foot (x i) (v i)‖ ≤ 1) (hv : ∀ i ∈ S, ‖v i‖ = 1) :
    ((S.image (fun i => lineCell s (x i) (v i))).card : ℝ) ≤ (2 / s + 2) ^ 6 := by
  classical
  let I := Finset.Icc ⌊-1 / s⌋ ⌊1 / s⌋
  let box : Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
    (Fintype.piFinset fun _ => I) ×ˢ (Fintype.piFinset fun _ => I)
  have hcoord : ∀ y : Sp, ‖y‖ ≤ 1 → ∀ c, |y c| ≤ 1 := by
    intro y hy c
    have := PiLp.norm_apply_le y c
    rw [Real.norm_eq_abs] at this
    linarith
  have hsub : S.image (fun i => lineCell s (x i) (v i)) ⊆ box := by
    intro κ hκ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hκ
    simp only [box, Finset.mem_product, Fintype.mem_piFinset]
    unfold lineCell cellIdx
    exact ⟨fun c => floor_mem_Icc hs (hcoord _ (hfoot i hi) c),
      fun c => floor_mem_Icc hs (hcoord _ (le_of_eq (hv i hi)) c)⟩
  have hbox : (box.card : ℝ) = (I.card : ℝ) ^ 6 := by
    simp only [box, Finset.card_product, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  calc ((S.image (fun i => lineCell s (x i) (v i))).card : ℝ) ≤ box.card := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (I.card : ℝ) ^ 6 := hbox
    _ ≤ (2 / s + 2) ^ 6 := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _) (card_Icc_floor_le hs)

/-- The population of a coarse cell is at least that of any of its fine cells. -/
lemma pop_fine_le_pop_coarse {ι α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset ι)
    (κf : ι → α) (κc : ι → β) (hnest : ∀ i i', κf i = κf i' → κc i = κc i') (i : ι) :
    pop S κf i ≤ pop S κc i := by
  unfold pop
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hjS, hji⟩ := Finset.mem_filter.1 hj
  exact Finset.mem_filter.2 ⟨hjS, hnest j i hji⟩

/-- The population of a coarse cell is the sum of the populations of its fine cells; with at most
`M` fine cells each of population below `P`, it is below `M P`. -/
lemma pop_coarse_le {ι α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset ι)
    (κf : ι → α) (κc : ι → β) (i : ι) (M P : ℕ)
    (hM : ((S.filter (fun j => κc j = κc i)).image κf).card ≤ M)
    (hP : ∀ j ∈ S, pop S κf j ≤ P) :
    pop S κc i ≤ M * P := by
  classical
  unfold pop
  set C := S.filter (fun j => κc j = κc i) with hC
  rw [Finset.card_eq_sum_card_fiberwise (f := κf) (t := C.image κf)
    (fun j hj => Finset.mem_image_of_mem κf hj)]
  calc ∑ c ∈ C.image κf, (C.filter (fun j => κf j = c)).card
      ≤ ∑ _c ∈ C.image κf, P := by
        apply Finset.sum_le_sum
        intro c hc
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
        calc (C.filter (fun j' => κf j' = κf j)).card ≤ (S.filter (fun j' => κf j' = κf j)).card := by
              apply Finset.card_le_card
              intro j' hj'
              obtain ⟨hj'C, hj'f⟩ := Finset.mem_filter.1 hj'
              exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj'C).1, hj'f⟩
          _ ≤ P := hP j (Finset.mem_filter.1 hj).1
    _ = (C.image κf).card * P := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ M * P := Nat.mul_le_mul_right _ hM

/-- Profile steps for nested grids of ratio `m`: if the populations at the fine and the coarse
level lie in `[2^a, 2^(a+1))` and `[2^b, 2^(b+1))`, then `2^a < 2^(b+1)` and `2^b < m⁶ 2^(a+1)`. -/
theorem profile_step {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m) {n : ℕ} (x v : Fin n → Sp)
    (S : Finset (Fin n)) (hS : S.Nonempty) (a b : ℕ)
    (hfine : ∀ i ∈ S, 2 ^ a ≤ pop S (fun i => lineCell s (x i) (v i)) i ∧
      pop S (fun i => lineCell s (x i) (v i)) i < 2 ^ (a + 1))
    (hcoarse : ∀ i ∈ S, 2 ^ b ≤ pop S (fun i => lineCell ((m : ℝ) * s) (x i) (v i)) i ∧
      pop S (fun i => lineCell ((m : ℝ) * s) (x i) (v i)) i < 2 ^ (b + 1)) :
    2 ^ a < 2 ^ (b + 1) ∧ 2 ^ b < m ^ 6 * 2 ^ (a + 1) := by
  obtain ⟨i, hi⟩ := hS
  have hnest : ∀ j j', lineCell s (x j) (v j) = lineCell s (x j') (v j') →
      lineCell ((m : ℝ) * s) (x j) (v j) = lineCell ((m : ℝ) * s) (x j') (v j') :=
    fun j j' h => lineCell_nest hs hm h
  constructor
  · calc 2 ^ a ≤ pop S (fun i => lineCell s (x i) (v i)) i := (hfine i hi).1
      _ ≤ pop S (fun i => lineCell ((m : ℝ) * s) (x i) (v i)) i :=
          pop_fine_le_pop_coarse S _ _ hnest i
      _ < 2 ^ (b + 1) := (hcoarse i hi).2
  · have hsub := card_subcells_le hs hm x v S (lineCell ((m : ℝ) * s) (x i) (v i))
    have hle := pop_coarse_le S (fun i => lineCell s (x i) (v i))
      (fun i => lineCell ((m : ℝ) * s) (x i) (v i)) i (m ^ 6) (2 ^ (a + 1) - 1) hsub
      (fun j hj => Nat.le_sub_one_of_lt (hfine j hj).2)
    have hpos : 0 < 2 ^ (a + 1) := by positivity
    have hm6 : 0 < m ^ 6 := by positivity
    calc 2 ^ b ≤ pop S (fun i => lineCell ((m : ℝ) * s) (x i) (v i)) i := (hcoarse i hi).1
      _ ≤ m ^ 6 * (2 ^ (a + 1) - 1) := hle
      _ < m ^ 6 * 2 ^ (a + 1) := by
          apply Nat.mul_lt_mul_of_pos_left (by omega) hm6

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
