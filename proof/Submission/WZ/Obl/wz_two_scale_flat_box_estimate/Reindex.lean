-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Reindex.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Fibers
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.SlabTransport
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.DoubledBodies
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.ConvexComposition

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (count_subfamily)

lemma convexCount_subfamily {δ m : ℝ} {n q : ℕ} (x v : Fin n → Space)
    (h : WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount δ m n x v)
    (j : Fin q → Fin n) (hj : Function.Injective j) :
    WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount δ m q (x ∘ j) (v ∘ j) := by
  intro W hW
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (count_subfamily j hj (fun i => Tube δ (x i) (v i) ⊆ W)))
    (sq_nonneg δ))).trans (h W hW)

lemma bodyConvexCount_subfamily {w m : ℝ} (hw : 0 ≤ w) {n q : ℕ}
    (U : Fin n → Set Space)
    (h : WangZahlLot.Obl.wz_flat_factored_improvement.BodyConvexCount U w m)
    (j : Fin q → Fin n) (hj : Function.Injective j) :
    WangZahlLot.Obl.wz_flat_factored_improvement.BodyConvexCount (U ∘ j) w m := by
  intro W hW
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (count_subfamily j hj (fun i => U i ⊆ W))) hw)).trans (h W hW)

lemma belowSlab_subfamily {δ ρ L F : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    {n N m M : ℕ} (x v : Fin n → Space) (y w : Fin N → Space)
    (f : Fin n → Fin N)
    (hbelow : BelowSlab δ ρ L n N x v .univ y w f)
    (hcontain : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i)))
    (hF : ∀ k, (Set.ncard {i | f i = k} : ℝ) ≤ F)
    (j : Fin m → Fin n) (hj : Function.Injective j)
    (k : Fin M → Fin N) (h : Fin m → Fin M) (hh : ∀ i, f (j i) = k (h i)) :
    ∀ l (u : Space) (s r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | h i = l ∧ Tube δ (x (j i)) (v (j i)) ⊆
        {p | |inner ℝ u p - s| ≤ r}} : ℝ) *
        volume (Tube (2 * ρ) (y (k l) - (1 / 2 : ℝ) • w (k l)) (2 • w (k l))) ≤
      ENNReal.ofReal (L * F) * volume
        (Tube (2 * ρ) (y (k l) - (1 / 2 : ℝ) • w (k l)) (2 • w (k l)) ∩
          {p | |inner ℝ u p - s| ≤ r}) := by
  intro l
  apply local_slab_enlargement (j := j) hL (P := fun i => f i = k l)
    (T := fun i => Tube δ (x i) (v i)) (Q := fun i => h i = l)
    (V := fun i => Tube δ (x (j i)) (v (j i)))
  · simpa only [BelowSlab, Finset.mem_univ, true_and] using hbelow (k l)
  · exact hj
  · intro i hi
    rw [hh, hi]
  · intro i
    exact Subset.rfl
  · intro i hi
    exact (hcontain i).trans (by rw [hi]; exact tube_subset_doubled hρ _ _)
  · exact Subset.rfl
  · rfl
  · exact hF (k l)

lemma box_fiber_raw_count {δ η ρ a b c : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {N L : ℕ} (y w : Fin N → Space) (z : Fin L → Space)
    (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L)
    (h : BoxCover δ η ρ a b c N L y w z e g) (j : Fin L) :
    ∀ W, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {k | Tube ρ (y (fiberIndex g j k)) (w (fiberIndex g j k)) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * fiberSize g j / (a * b * c)) * volume W := by
  have hh := relative_convex_count (fun k => Tube ρ (y k) (w k)) (fun k => g k = j)
    (Box a b c (z j) (e j)) (by positivity : 0 < a * b * c)
    (Real.rpow_nonneg hδ.le _) (box_volume ha.le hb.le hc.le _ _)
    (fun k hk => by simpa only [hk] using h.1 k) (h.2.2.2.2 j)
    (fiberIndex g j) (fiberIndex_injective g j) (fiberIndex_spec g j)
  simpa only [fiberSize_eq] using hh

lemma assigned_parents_meet_ball {δ ρ : ℝ} (hδ : 0 < δ) {n N : ℕ}
    (x v : Fin n → Space) (y w : Fin N → Space) (f : Fin n → Fin N)
    (hf : Function.Surjective f)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1)
    (hcontain : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i))) :
    ∀ k, (Tube ρ (y k) (w k) ∩ ball (0 : Space) 1).Nonempty := by
  intro k
  obtain ⟨i, rfl⟩ := hf k
  have hx : x i ∈ Tube δ (x i) (v i) := self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
  exact ⟨x i, hcontain i hx, hball i hx⟩

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
