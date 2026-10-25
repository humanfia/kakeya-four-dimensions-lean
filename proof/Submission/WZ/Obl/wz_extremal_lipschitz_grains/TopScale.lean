-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TopScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Counting

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

lemma start_mem_tube {δ : ℝ} (hδ : 0 < δ) (x v : Space) : x ∈ tube δ x v :=
  self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))

lemma start_mem_dilated_segment (z w : Space) :
    z ∈ segment ℝ (z - (9 / 2 : ℝ) • w) (z + (11 / 2 : ℝ) • w) := by
  rw [segment_eq_image']
  refine ⟨9 / 20, by norm_num, ?_⟩
  module

lemma norm_start_lt_three {z w p : Space} (hw : ‖w‖ = 1)
    (hp : p ∈ ball (0 : Space) 1) (ht : p ∈ tube 1 z w) : ‖z‖ < 3 := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp ht
  rw [segment_eq_image'] at hq
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hqz : dist (z + t • (z + w - z)) z ≤ 1 := by
    simp only [add_sub_cancel_left, dist_self_add_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht0, hw, mul_one]
    exact ht1
  have hp0 : ‖p‖ < 1 := by simpa using hp
  calc
    ‖z‖ ≤ ‖z - p‖ + ‖p‖ := by simpa only [add_comm] using norm_le_insert' z p
    _ = dist p z + ‖p‖ := by rw [← dist_eq_norm, dist_comm]
    _ ≤ dist p (z + t • (z + w - z)) +
        dist (z + t • (z + w - z)) z + ‖p‖ := by
      gcongr
      exact dist_triangle _ _ _
    _ < 3 := by linarith

lemma ball_subset_dilated_of_meets {z w : Space} (hw : ‖w‖ = 1)
    (hmeet : (ball (0 : Space) 1 ∩ tube 1 z w).Nonempty) :
    ball (0 : Space) 1 ⊆ dilatedTube 1 z w := by
  obtain ⟨p, hp, ht⟩ := hmeet
  have hz := norm_start_lt_three hw hp ht
  intro q hq
  apply mem_thickening_iff.mpr
  refine ⟨z, start_mem_dilated_segment z w, ?_⟩
  have hq0 : ‖q‖ < 1 := by simpa using hq
  have hd : dist q z ≤ ‖q‖ + ‖z‖ := by
    rw [dist_eq_norm]
    exact norm_sub_le _ _
  linarith

/-- Separation forces every top-scale coarse tube to be the same tube index. -/
theorem top_cover_subsingleton {δ : ℝ} (hδ : 0 < δ)
    {n k : ℕ} (hn : 0 < n) {x v : Fin n → Space} {z w : Fin k → Space}
    (hball : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1)
    (hw : ∀ j, ‖w j‖ = 1)
    (hmeet : ∀ j, ∃ i, tube δ (x i) (v i) ⊆ tube 1 (z j) (w j))
    (hsep : ∀ i j j', tube δ (x i) (v i) ⊆ dilatedTube 1 (z j) (w j) →
      tube δ (x i) (v i) ⊆ dilatedTube 1 (z j') (w j') → j = j') :
    ∀ j j' : Fin k, j = j' := by
  have hB : ∀ j, ball (0 : Space) 1 ⊆ dilatedTube 1 (z j) (w j) := by
    intro j
    obtain ⟨i, hi⟩ := hmeet j
    exact ball_subset_dilated_of_meets (hw j)
      ⟨x i, hball i (start_mem_tube hδ _ _), hi (start_mem_tube hδ _ _)⟩
  intro j j'
  let i : Fin n := ⟨0, hn⟩
  exact hsep i j j' ((hball i).trans (hB j)) ((hball i).trans (hB j'))

/-- The top-scale local convex count is a global relative Frostman count. -/
theorem Separated.global_frostman {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hS : Separated η δ n x v) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 0 < n) (hball : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1) :
    ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W := by
  obtain ⟨ρ, h1ρ, hρ1, hρ, k, hk, z, w, hw, hd, hc, ho, hb, hf, hs⟩ :=
    hS 1 hδ1 le_rfl
  have hρeq : ρ = 1 := le_antisymm hρ1 h1ρ
  subst ρ
  have hsub := top_cover_subsingleton hδ hn hball hw ho hs
  let j : Fin k := ⟨0, hk⟩
  have hcontains : ∀ i, tube δ (x i) (v i) ⊆ tube 1 (z j) (w j) := by
    intro i
    obtain ⟨j', hj', _⟩ := hc i
    simpa only [hsub j' j] using hj'
  intro W hW
  have h := hf j W hW
  simpa only [hcontains, true_and, one_pow, mul_one, Set.ofPred_true,
    Set.ncard_univ, Nat.card_fin] using h

/-- A fixed numerical enlargement ensures that the absolute counting constant is at least one. -/
theorem counting_constant_ge_one {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1)
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W) :
    1 ≤ 56 * δ ^ (-η) * (n : ℝ) * δ ^ 2 := by
  let i : Fin n := ⟨0, hn⟩
  let W := thickening δ (segment ℝ (x i) (x i + (6 : ℝ) • v i))
  have hTW : tube δ (x i) (v i) ⊆ W := by
    apply thickening_subset_of_subset
    apply (convex_segment (x i) (x i + (6 : ℝ) • v i)).segment_subset
    · exact left_mem_segment _ _ _
    · rw [segment_eq_image']
      refine ⟨1 / 6, by norm_num, ?_⟩
      module
  have hc : (1 : ℝ) ≤ ({j | tube δ (x j) (v j) ⊆ W}.ncard : ℝ) := by
    exact_mod_cast (Set.ncard_pos (by toFinite_tac)).mpr ⟨i, hTW⟩
  have hW : volume W ≤ ENNReal.ofReal (56 * δ ^ 2) := by
    apply (WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.cylinder_volume_le
      (hv i) (x i) hδ.le).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg δ]
  have hh := (ENNReal.ofReal_le_ofReal hc).trans
    ((hF W ((convex_segment _ _).thickening _)).trans (mul_le_mul' le_rfl hW))
  rw [← ENNReal.ofReal_mul (by positivity)] at hh
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  nlinarith only [hr]

lemma slab_convex (u : Space) (t r : ℝ) :
    Convex ℝ (ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r}) := by
  apply (convex_ball _ _).inter
  intro p hp q hq a b ha hb hab
  change |inner ℝ u (a • p + b • q) - t| ≤ r
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  change |inner ℝ u p - t| ≤ r at hp
  change |inner ℝ u q - t| ≤ r at hq
  rw [abs_le] at hp hq ⊢
  constructor <;> nlinarith [congrArg (fun z : ℝ => z * t) hab,
    congrArg (fun z : ℝ => z * r) hab, mul_nonneg ha (sub_nonneg.mpr hp.2),
    mul_nonneg hb (sub_nonneg.mpr hq.2), mul_nonneg ha (sub_nonneg.mpr hp.1),
    mul_nonneg hb (sub_nonneg.mpr hq.1)]

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
