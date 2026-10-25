-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_whitney_rich_reduction.WhitneySum.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_whitney_rich_reduction.WhitneyCover

/-!
# Counting facts for the Whitney reduction (x0284)

* `card_le_of_katzTao`: `‖q i‖ ≤ 10` and the unit-scale coefficient count give
  `n ≤ 41^3 δ^(-η) / δ`;
* `ncard_ball_le_of_katzTao`: the coefficient count then holds at every radius `r ≥ δ` with
  constant `41^3 δ^(-η)` (also for `r > 1`);
* `biRichSet_eq_empty`: at scales `D ≤ 100 δ` cubes are singletons, so bi-rich sets at a level
  `μ > 1` are empty;
* `sum_sum_whitney_card_le`: summing `#A + #B` over all scales and Whitney pairs gives at most
  `L * 2 * 801^3 * n`.
-/

namespace WangZahlLot.Obl.wz_jet_whitney_rich_reduction

open Finset MeasureTheory

noncomputable section

variable {n : ℕ}

lemma abs_coord_le_of_norm_le {x : EuclideanSpace ℝ (Fin 3)} {R : ℝ} (h : ‖x‖ ≤ R) (m : Fin 3) :
    |x m| ≤ R := by
  have := PiLp.norm_apply_le x m
  rw [Real.norm_eq_abs] at this
  linarith

/-- Coefficients of norm `≤ 10` occupy at most `41^3` cubes of side `1/2`. -/
lemma card_occCubes_half_le (q : Fin n → EuclideanSpace ℝ (Fin 3)) (hq : ∀ i, ‖q i‖ ≤ 10) :
    (occCubes q (1 / 2)).card ≤ 41 ^ 3 := by
  have hbox : occCubes q (1 / 2) ⊆ Fintype.piFinset (fun _ : Fin 3 => Icc (-20 : ℤ) 20) := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    rw [Fintype.mem_piFinset]
    intro m
    have hx := abs_coord_le_of_norm_le (hq i) m
    rw [abs_le] at hx
    rw [Finset.mem_Icc]
    simp only [cubeIdx]
    constructor
    · rw [Int.le_floor]
      push_cast
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    · rw [Int.floor_le_iff]
      push_cast
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
  calc (occCubes q (1 / 2)).card ≤ (Fintype.piFinset (fun _ : Fin 3 => Icc (-20 : ℤ) 20)).card :=
        Finset.card_le_card hbox
    _ = 41 ^ 3 := by
        rw [Fintype.card_piFinset]
        simp [Int.card_Icc]

/-- A cube of side `1/2` lies in the open unit ball around any of its members. -/
lemma card_cubeSet_half_le (q : Fin n → EuclideanSpace ℝ (Fin 3)) {δ η : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1)
    (hKT : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
      (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ))
    (k : Fin 3 → ℤ) : ((cubeSet q (1 / 2) k).card : ℝ) ≤ δ ^ (-η) * (1 / δ) := by
  classical
  rcases (cubeSet q (1 / 2) k).eq_empty_or_nonempty with he | ⟨i0, hi0⟩
  · rw [he, Finset.card_empty, Nat.cast_zero]; positivity
  · have hsub : (cubeSet q (1 / 2) k : Set (Fin n)) ⊆ {i | q i ∈ Metric.ball (q i0) 1} := by
      intro i hi
      rw [Finset.mem_coe] at hi
      rw [Set.mem_ofPred_eq, Metric.mem_ball]
      have h1 := mem_cubeSet.mp hi
      have h2 := mem_cubeSet.mp hi0
      have := dist_lt_of_cubeIdx_eq (by norm_num : (0 : ℝ) < 1 / 2) (h1.trans h2.symm)
      linarith
    have hfin : ({i | q i ∈ Metric.ball (q i0) 1} : Set (Fin n)).Finite := Set.toFinite _
    calc ((cubeSet q (1 / 2) k).card : ℝ) = (Set.ncard (cubeSet q (1 / 2) k : Set (Fin n)) : ℝ) := by
          rw [Set.ncard_coe_finset]
      _ ≤ (Set.ncard {i | q i ∈ Metric.ball (q i0) 1} : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub hfin
      _ ≤ δ ^ (-η) * (1 / δ) := hKT (q i0) 1 hδ1 le_rfl

/-- Total count: `n ≤ 41^3 δ^(-η) / δ`. -/
theorem card_le_of_katzTao (q : Fin n → EuclideanSpace ℝ (Fin 3)) (hq : ∀ i, ‖q i‖ ≤ 10)
    {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hKT : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
      (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) :
    (n : ℝ) ≤ 41 ^ 3 * δ ^ (-η) / δ := by
  have hsum := sum_card_inter_cubeSet q (1 / 2) univ
  simp only [Finset.univ_inter] at hsum
  have hn : (n : ℝ) = ∑ k ∈ occCubes q (1 / 2), ((cubeSet q (1 / 2) k).card : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    exact_mod_cast hsum.symm
  rw [hn]
  calc ∑ k ∈ occCubes q (1 / 2), ((cubeSet q (1 / 2) k).card : ℝ)
      ≤ ∑ _k ∈ occCubes q (1 / 2), δ ^ (-η) * (1 / δ) :=
        Finset.sum_le_sum (fun k _ => card_cubeSet_half_le q hδ hδ1 hKT k)
    _ = (occCubes q (1 / 2)).card * (δ ^ (-η) * (1 / δ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 41 ^ 3 * (δ ^ (-η) * (1 / δ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_occCubes_half_le q hq
    _ = 41 ^ 3 * δ ^ (-η) / δ := by ring

/-- The coefficient count at every radius `r ≥ δ`, with constant `41^3 δ^(-η)`. -/
theorem ncard_ball_le_of_katzTao (q : Fin n → EuclideanSpace ℝ (Fin 3)) (hq : ∀ i, ‖q i‖ ≤ 10)
    {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hKT : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
      (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ))
    (P : Fin n → Prop) (q0 : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : δ ≤ r) :
    (Set.ncard {i | P i ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤ 41 ^ 3 * δ ^ (-η) * (r / δ) := by
  have hpos : 0 ≤ δ ^ (-η) * (r / δ) := by
    have : 0 < r := hδ.trans_le hr
    positivity
  have hsub : {i | P i ∧ q i ∈ Metric.ball q0 r} ⊆ {i | q i ∈ Metric.ball q0 r} :=
    fun i hi => hi.2
  have h1 : (Set.ncard {i | P i ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤
      (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
  rcases le_or_gt r 1 with hr1 | hr1
  · calc _ ≤ (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) := h1
      _ ≤ δ ^ (-η) * (r / δ) := hKT q0 r hr hr1
      _ ≤ 41 ^ 3 * δ ^ (-η) * (r / δ) := by
          rw [mul_assoc]; linarith
  · have hall : (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ n := by
      have := Set.ncard_le_ncard (Set.subset_univ {i | q i ∈ Metric.ball q0 r}) (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      exact_mod_cast this
    have hn := card_le_of_katzTao q hq hδ hδ1 hKT
    have hη : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ _
    calc _ ≤ (n : ℝ) := h1.trans hall
      _ ≤ 41 ^ 3 * δ ^ (-η) / δ := hn
      _ = 41 ^ 3 * δ ^ (-η) * (1 / δ) := by ring
      _ ≤ 41 ^ 3 * δ ^ (-η) * (r / δ) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr1.le hδ.le) (by positivity)

/-- At scales `D ≤ 100 δ` the cubes are singletons, so bi-rich sets at a level `μ > 1` are
empty. -/
theorem biRichSet_eq_empty (q : Fin n → EuclideanSpace ℝ (Fin 3)) (S : Fin n → Set (ℝ × ℝ))
    {δ D μ : ℝ} (hD : 0 < D) (hDδ : D ≤ 100 * δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) (hμ : 1 < μ)
    (kk : (Fin 3 → ℤ) × (Fin 3 → ℤ)) : biRichSet q S D μ kk = ∅ := by
  classical
  have hle : ∀ k, (cubeSet q (D / 200) k).card ≤ 1 := by
    intro k
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    have h1 := dist_lt_of_mem_cubeSet hD hi hj
    have h2 := hsep i j hij
    linarith
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have h1 := hp.1
  rw [multOn_eq_card] at h1
  have hc : ((cubeSet q (D / 200) kk.1).filter (fun i => p ∈ S i)).card ≤ 1 :=
    (Finset.card_filter_le _ _).trans (hle _)
  have : ENNReal.ofReal μ ≤ 1 := h1.trans (by exact_mod_cast hc)
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at this
  linarith

/-- Summing `#A + #B` over the scales and Whitney pairs. -/
theorem sum_sum_whitney_card_le (q : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 < δ)
    (L : ℕ) :
    ∑ m ∈ range L, ∑ kk ∈ whitneyPairs q (whitneyScale δ m),
      (((cubeSet q (whitneyScale δ m / 200) kk.1).card : ℝ) +
        (cubeSet q (whitneyScale δ m / 200) kk.2).card) ≤ (L : ℝ) * (2 * 801 ^ 3 * (n : ℝ)) := by
  calc _ ≤ ∑ _m ∈ range L, (2 * 801 ^ 3 * (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro m _
        have := sum_whitney_card_le q (whitneyScale_pos hδ m) univ
        simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at this
        exact this
    _ = (L : ℝ) * (2 * 801 ^ 3 * (n : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end WangZahlLot.Obl.wz_jet_whitney_rich_reduction
