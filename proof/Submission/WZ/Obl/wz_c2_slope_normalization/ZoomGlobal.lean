-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomGlobal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomCenter

/-!
# The global convex count and the cover at unit scale

The separated cover at scale one has a single coarse tube, because every tenfold dilate of a
unit coarse tube containing a fine tube contains the unit ball.  Its Frostman count is the
global convex count of the family.  Conversely a family of unit tubes in the unit ball with a
global convex count has the single unit coarse tube through the origin as a separated cover.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory Finset
open scoped ENNReal RealInnerProductSpace Classical

noncomputable section

/-- A tenfold dilate of a unit coarse tube meeting the unit ball contains the unit ball. -/
theorem ball_subset_dilate_one {z w q : Space} (hq : q ∈ Tube 1 z w)
    (hq1 : ‖q‖ < 1) : ball (0 : Space) 1 ⊆ Dilate 1 z w := by
  obtain ⟨t, ht, hqt⟩ := exists_param_of_mem_tube' hq
  intro p hp
  rw [mem_ball, dist_zero_right] at hp
  apply mem_thickening_iff.mpr
  refine ⟨z + t • w, ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨(t + 9 / 2) / 10, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simp only
    module
  · rw [dist_eq_norm]
    calc ‖p - (z + t • w)‖ ≤ ‖p‖ + ‖q‖ + ‖q - (z + t • w)‖ := by
          have he : p - (z + t • w) = p - q + (q - (z + t • w)) := by abel
          rw [he]
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ < 10 * 1 := by linarith

/-- The separated covers give the global convex count. -/
theorem global_frostman {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) (hS : Strong η δ n x v)
    (W : Set Space) (hW : Convex ℝ W) :
    ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * n) * volume W := by
  obtain ⟨ρ, hρ1, hρ1', -, k, hk, z, w, hcov, hsep⟩ := hS 1 hδ1 le_rfl
  have hρ : ρ = 1 := le_antisymm hρ1' hρ1
  subst hρ
  obtain ⟨hw, -, huniq, hfull, -, hfrost⟩ := hcov
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : {i : Fin 0 | Tube δ (x i) (v i) ⊆ W} = ∅ := by ext i; exact i.elim0
    rw [this, ncard_empty, Nat.cast_zero, ENNReal.ofReal_zero]
    exact bot_le
  -- every fine tube lies in every tenfold dilate, so all coarse tubes coincide
  have hdil : ∀ i j, Tube δ (x i) (v i) ⊆ Dilate 1 (z j) (w j) := by
    intro i j
    obtain ⟨i₀, hi₀⟩ := hfull j
    have hq : x i₀ ∈ Tube 1 (z j) (w j) :=
      hi₀ (self_subset_thickening hδ _ (left_mem_segment ℝ _ _))
    have hq1 : ‖x i₀‖ < 1 := by
      simpa using hball i₀ (self_subset_thickening hδ _ (left_mem_segment ℝ _ _))
    exact (hball i).trans (ball_subset_dilate_one hq hq1)
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨j₀, hj₀, -⟩ := huniq i₀
  have hall : ∀ i, Tube δ (x i) (v i) ⊆ Tube 1 (z j₀) (w j₀) := by
    intro i
    obtain ⟨j, hj, -⟩ := huniq i
    have : j = j₀ := hsep i j j₀ (hdil i j) (hdil i j₀)
    rw [← this]; exact hj
  have h := hfrost j₀ W hW
  have hset1 : {i | Tube δ (x i) (v i) ⊆ Tube 1 (z j₀) (w j₀) ∧ Tube δ (x i) (v i) ⊆ W} =
      {i | Tube δ (x i) (v i) ⊆ W} := by
    ext i
    simp only [mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨hall i, h⟩⟩
  have hset2 : {i | Tube δ (x i) (v i) ⊆ Tube 1 (z j₀) (w j₀)} = Set.univ := by
    ext i
    simp only [mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hall i
  rw [hset1, hset2, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, one_pow,
    mul_one] at h
  exact h

/-- A family of unit tubes in the unit ball with a global convex count has a separated cover at
scale one. -/
theorem single_cover {δ K : ℝ} {m : ℕ} {x v : Fin m → Space} (hm : 0 < m) (hK : 1 ≤ K)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hfrost : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (K * m) * volume W) :
    ∃ z w : Fin 1 → Space, CoverAt δ K 1 x v z w ∧ SeparatedAt δ 1 x v z w := by
  let e₀ : Space := EuclideanSpace.single 0 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have hbig : ball (0 : Space) 1 ⊆ Tube 1 (-((1 / 2 : ℝ) • e₀)) e₀ := by
    intro p hp
    apply mem_thickening_iff.mpr
    refine ⟨0, ?_, by simpa using hp⟩
    rw [segment_eq_image']
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by simp only; module⟩
  have hin : ∀ i, Tube δ (x i) (v i) ⊆ Tube 1 (-((1 / 2 : ℝ) • e₀)) e₀ :=
    fun i => (hball i).trans hbig
  refine ⟨fun _ => -((1 / 2 : ℝ) • e₀), fun _ => e₀, ⟨fun _ => he₀, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j j' hjj'
    exact absurd (Subsingleton.elim j j') hjj'
  · intro i
    exact ⟨0, hin i, fun j _ => Subsingleton.elim j 0⟩
  · intro j
    exact ⟨⟨0, hm⟩, hin _⟩
  · intro j j'
    have h0 : (0 : ℝ) ≤ (ncard {i | Tube δ (x i) (v i) ⊆ Tube 1 (-((1 / 2 : ℝ) • e₀)) e₀} : ℝ) :=
      Nat.cast_nonneg _
    nlinarith
  · intro j W hW
    have hset1 : {i | Tube δ (x i) (v i) ⊆ Tube 1 (-((1 / 2 : ℝ) • e₀)) e₀ ∧
        Tube δ (x i) (v i) ⊆ W} = {i | Tube δ (x i) (v i) ⊆ W} := by
      ext i
      simp only [mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hin i, h⟩⟩
    have hset2 : {i | Tube δ (x i) (v i) ⊆ Tube 1 (-((1 / 2 : ℝ) • e₀)) e₀} = Set.univ := by
      ext i
      simp only [mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hin i
    rw [hset1, hset2, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, one_pow, mul_one]
    exact hfrost W hW
  · intro i j j' _ _
    exact Subsingleton.elim j j'

/-- The global convex count of the zoomed pieces, from the global count of the old family. -/
theorem zoom_global_frostman {n : ℕ} {r δ A : ℝ} {c : Space} (hr : 16 ≤ r) (hδ : 0 < δ)
    (hrδ : r * δ ≤ 1 / 8) {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1) (hA : 0 < A)
    (hold : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤ ENNReal.ofReal A * volume W)
    (Q : Finset (Fin n)) (hQ : ∀ i ∈ Q, FNear r c (x i) (v i))
    (W : Set Space) (hW : Convex ℝ W) :
    ENNReal.ofReal (ncard {a | Tube (r * δ) (pieceBase r c (x (enumerate Q a)) (v (enumerate Q a)))
        (v (enumerate Q a)) ⊆ W} : ℝ) ≤ ENNReal.ofReal (432 * 512 * A) * volume W := by
  set e := enumerate Q
  have hemem : ∀ a, e a ∈ Q := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_mem Q
  set S := {a | Tube (r * δ) (pieceBase r c (x (e a)) (v (e a))) (v (e a)) ⊆ W}
  rcases S.eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
  · rw [hS, ncard_empty, Nat.cast_zero, ENNReal.ofReal_zero]
    exact bot_le
  by_cases hWtop : volume W = ⊤
  · rw [hWtop, ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
    exact le_top
  obtain ⟨B, hBconv, hBvol, hBsub⟩ := old_tubes_in_box hr hδ hrδ hW hWtop (hv (e a₀))
    (hQ _ (hemem a₀)) ha₀
  have hSO : ncard S ≤ ncard {i | Tube δ (x i) (v i) ⊆ B} := by
    apply Set.ncard_le_ncard_of_injOn e
    · intro a ha
      exact hBsub _ _ (hv _) (hQ _ (hemem a)) ha
    · intro a _ a' _ h
      exact WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_injective Q h
  calc ENNReal.ofReal (ncard S : ℝ) ≤ ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ B} : ℝ) :=
        ENNReal.ofReal_le_ofReal (by exact_mod_cast hSO)
    _ ≤ ENNReal.ofReal A * volume B := hold B hBconv
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (432 * 512) * volume W) := by gcongr
    _ = ENNReal.ofReal (432 * 512 * A) * volume W := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le, mul_comm A]

end

end WangZahlLot.Obl.wz_c2_slope_normalization
