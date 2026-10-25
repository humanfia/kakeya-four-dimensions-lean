-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.RootPartition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.CoarseDensity

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A coarse parameter cell, together with the relative Frostman count it supplies. -/
def CoarseClass {n : ℕ} (x v : Fin n → Space) (δ a s : ℝ) (L : ℕ)
    (Q : Finset (Fin n)) : Prop :=
  ∃ j, 3 ≤ j ∧ j ≤ L ∧ δ ^ a < ((2 : ℝ) ^ j)⁻¹ ∧ ∃ i₀ ∈ Q,
    (∀ i ∈ Q, dyadicLabel j (parameters (x i) (v i)) =
      dyadicLabel j (parameters (x i₀) (v i₀))) ∧
    ∀ k, j ≤ k → k ≤ L → ∀ l : Fin 3 → ℤ,
      ((Q.filter (fun i => dyadicLabel k (parameters (x i) (v i)) = l)).card : ℝ) ≤
        (Q.card : ℝ) * ((((2 : ℝ) ^ k)⁻¹ / ((2 : ℝ) ^ j)⁻¹) ^ s)

/-- A thin-slice root partitions into good coarse classes, except for a controlled
number of remaining tubes. This construction preserves arbitrary shading weights. -/
theorem root_coarse_partition {η δ c a b s : ℝ} (hδ : 0 < δ)
    {n L : ℕ} (hn : 0 < n) (hL : 3 ≤ L)
    (x v : Fin n → Space) (U : Finset (Fin n))
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (hthin : ∀ i ∈ U, |slope (v i) 0 - c| ≤ δ)
    (hroot : ∀ i ∈ U, ∀ i' ∈ U, dyadicLabel 3 (parameters (x i) (v i)) =
      dyadicLabel 3 (parameters (x i') (v i')))
    (hδL : δ ≤ ((2 : ℝ) ^ L)⁻¹) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (hsmall : 2080000 * δ ^ (a * (2 - s) - η - b) < 1) :
    ∃ F : Finset (Finset (Fin n)),
      (∀ Q ∈ F, Q ⊆ U ∧ Q.Nonempty ∧ CoarseClass x v δ a s L Q) ∧
      (F : Set (Finset (Fin n))).PairwiseDisjoint id ∧
      ((U \ F.biUnion id).card : ℝ) ≤ δ ^ b * (n : ℝ) := by
  apply disjoint_selection_partition U (CoarseClass x v δ a s L) (by positivity)
  intro S hSU hS
  obtain ⟨j, hj3, hjL, hcoarse, i₀, hi₀, hQ, hcount⟩ :=
    exists_coarse_density_cell hδ hn hL x v S hv htrans hball hF
      (fun i hi => hthin i (hSU hi))
      (fun i hi i' hi' => hroot i (hSU hi) i' (hSU hi')) hδL hs hs2 hsmall hS.le
  refine ⟨S.filter (fun i => dyadicLabel j (parameters (x i) (v i)) =
    dyadicLabel j (parameters (x i₀) (v i₀))), Finset.filter_subset _ _, hQ, ?_⟩
  exact ⟨j, hj3, hjL, hcoarse, i₀, Finset.mem_filter.mpr ⟨hi₀, rfl⟩,
    fun i hi => (Finset.mem_filter.mp hi).2, hcount⟩

/-- A root consists of a delta-width slope slice and a fixed coarse parameter cube. -/
def parameterRootLabel (δ c : ℝ) (p : Space) : ℤ × (Fin 3 → ℤ) :=
  (⌊c / δ⌋, dyadicLabel 3 p)

lemma root_slope_near {δ c : ℝ} (hδ : 0 < δ) :
    |c - δ * (⌊c / δ⌋ : ℝ)| ≤ δ := by
  have hlo := Int.floor_le (c / δ)
  have hhi := Int.lt_floor_add_one (c / δ)
  have hlow : δ * (⌊c / δ⌋ : ℝ) ≤ c := by
    have hh := (le_div_iff₀ hδ).mp hlo
    nlinarith
  have hhigh : c < δ * ((⌊c / δ⌋ : ℝ) + 1) := by
    have hh := (div_lt_iff₀ hδ).mp hhi
    nlinarith
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The number of root cells has the expected inverse-delta bound. -/
theorem parameter_root_count {α : Type*} [DecidableEq α]
    (U : Finset α) (p : α → Space) (c : α → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hp : ∀ i ∈ U, ‖p i‖ ≤ 5) (hc : ∀ i ∈ U, |c i| ≤ 2) :
    ((U.image (fun i => parameterRootLabel δ (c i) (p i))).card : ℝ) * δ ≤ 6 * 81 ^ 3 := by
  classical
  let C := Finset.Icc ⌊(-2 : ℝ) / δ⌋ ⌊(2 : ℝ) / δ⌋
  let B := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-40 : ℤ) 40)
  have hsub : U.image (fun i => parameterRootLabel δ (c i) (p i)) ⊆ C ×ˢ B := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      obtain ⟨hlo, hhi⟩ := abs_le.mp (hc i hi)
      exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hlo hδ.le),
        Int.floor_mono (div_le_div_of_nonneg_right hhi hδ.le)⟩
    · change dyadicLabel 3 (p i) ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-40 : ℤ) 40)
      rw [Fintype.mem_piFinset]
      intro k
      have hb := (abs_coordinate_le_norm (p i) k).trans (hp i hi)
      have hlo := Int.floor_mono (show (-40 : ℝ) ≤ (2 : ℝ) ^ 3 * p i k by
        obtain ⟨hlo, hhi⟩ := abs_le.mp hb
        norm_num
        linarith)
      have hhi := Int.floor_mono (show (2 : ℝ) ^ 3 * p i k ≤ 40 by
        obtain ⟨hlo, hhi⟩ := abs_le.mp hb
        norm_num
        linarith)
      apply Finset.mem_Icc.mpr
      norm_num [dyadicLabel] at hlo hhi ⊢
      exact ⟨hlo, hhi⟩
  have hC : (C.card : ℝ) * δ ≤ 6 := by
    have hab : ⌊(-2 : ℝ) / δ⌋ ≤ ⌊(2 : ℝ) / δ⌋ :=
      Int.floor_mono (div_le_div_of_nonneg_right (by norm_num) hδ.le)
    have hcard : (C.card : ℝ) = (⌊(2 : ℝ) / δ⌋ : ℝ) - (⌊(-2 : ℝ) / δ⌋ : ℝ) + 1 := by
      have he : (C.card : ℤ) = ⌊(2 : ℝ) / δ⌋ - ⌊(-2 : ℝ) / δ⌋ + 1 := by
        rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
        ring
      exact_mod_cast he
    rw [hcard]
    have hlo := Int.lt_floor_add_one ((-2 : ℝ) / δ)
    have hhi := Int.floor_le ((2 : ℝ) / δ)
    have hlo' := (div_lt_iff₀ hδ).mp hlo
    have hhi' := (le_div_iff₀ hδ).mp hhi
    nlinarith
  have hB : B.card = 81 ^ 3 := by simp [B, Fintype.card_piFinset, Int.card_Icc]
  have hcard : ((U.image (fun i => parameterRootLabel δ (c i) (p i))).card : ℝ) ≤
      (C.card : ℝ) * (81 : ℝ) ^ 3 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product, hB] at hh
    exact_mod_cast hh
  calc
    _ ≤ ((C.card : ℝ) * (81 : ℝ) ^ 3) * δ := mul_le_mul_of_nonneg_right hcard hδ.le
    _ = ((C.card : ℝ) * δ) * (81 : ℝ) ^ 3 := by ring
    _ ≤ 6 * 81 ^ 3 := mul_le_mul_of_nonneg_right hC (by positivity)

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
