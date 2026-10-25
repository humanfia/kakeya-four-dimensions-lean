-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

namespace WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable abbrev Vol (S : Set Space) : ℝ := (volume S).toReal

abbrev ConvexCount (δ m : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal ((ncard {i : Fin n | Tube δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal m * volume W

abbrev SlabCount (δ m : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal (ncard {i : Fin n | Tube δ (x i) (v i) ⊆ Slab u t r} : ℝ) ≤
      ENNReal.ofReal (m * (n : ℝ)) * volume (Slab u t r)

lemma finite_volume_of_subset_ball {S : Set Space} (hS : S ⊆ ball 0 1) :
    volume S ≠ ⊤ := ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hS)

lemma union_subset_ball {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, Y i ⊆ ball 0 1) : (⋃ i, Y i) ⊆ ball 0 1 :=
  iUnion_subset hY

lemma density_union_lower {n : ℕ} (hn : 0 < n) {Y : Fin n → Set Space}
    (hfin : volume (⋃ i, Y i) ≠ ⊤) {a : ℝ}
    (hd : ENNReal.ofReal (a * (n : ℝ)) ≤ ∑ i, volume (Y i)) :
    a ≤ Vol (⋃ i, Y i) := by
  have hf : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hfin (measure_mono (subset_iUnion Y i))
  have hd' := (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.sum_ne_top.mpr (fun i _ => hf i))).mp hd
  rw [ENNReal.toReal_sum (fun i _ => hf i)] at hd'
  have hs : ∑ i, Vol (Y i) ≤ (n : ℝ) * Vol (⋃ i, Y i) := by
    calc
      ∑ i, Vol (Y i) ≤ ∑ _ : Fin n, Vol (⋃ i, Y i) :=
        Finset.sum_le_sum (fun i _ => ENNReal.toReal_mono hfin
          (measure_mono (subset_iUnion Y i)))
      _ = _ := by simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

lemma disjoint_sum_le {J : ℕ} {E : Fin J → Set Space} {U : Set Space}
    (hfin : volume U ≠ ⊤) (hm : ∀ j, MeasurableSet (E j))
    (hd : Pairwise (fun j j' => Disjoint (E j) (E j')))
    (hs : ∀ j, E j ⊆ U) :
    ∑ j, Vol (E j) ≤ Vol U := by
  have hf : ∀ j, volume (E j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top hfin (measure_mono (hs j))
  have hh := measure_mono (μ := volume) (iUnion_subset hs)
  rw [measure_iUnion hd hm, tsum_fintype] at hh
  have hh' := ENNReal.toReal_mono hfin hh
  simpa only [ENNReal.toReal_sum (fun j _ => hf j)] using hh'

lemma subfamily_count_le {n k : ℕ} {f : Fin k → Fin n} (hf : Function.Injective f)
    (P : Fin n → Prop) :
    ncard {i : Fin k | P (f i)} ≤ ncard {i : Fin n | P i} :=
  ncard_le_ncard_of_injOn f (fun _ h => h) hf.injOn

lemma all_subfamily_count_le {n k : ℕ} {f : Fin k → Fin n} (hf : Function.Injective f)
    {P : Fin n → Prop} (hP : ∀ i, P (f i)) :
    k ≤ ncard {i : Fin n | P i} := by
  simpa only [hP, Set.ofPred_true, ncard_univ, Nat.card_fin] using subfamily_count_le hf P

lemma convex_count_subfamily {δ m : ℝ} {n k : ℕ} {x v : Fin n → Space}
    (hc : ConvexCount δ m x v) {f : Fin k → Fin n} (hf : Function.Injective f) :
    ConvexCount δ m (fun i => x (f i)) (fun i => v (f i)) := by
  intro W hW
  apply le_trans (b := ENNReal.ofReal
    ((ncard {i : Fin n | Tube δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2)) _ (hc W hW)
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact_mod_cast subfamily_count_le hf (fun i => Tube δ (x i) (v i) ⊆ W)

lemma cylinder_count {δ m C θ : ℝ} (hm : 0 ≤ m) (hC : 0 ≤ C)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {n : ℕ} {x v : Fin n → Space}
    (hc : ConvexCount δ m x v) {z w : Space} (hw : ‖w‖ = 1)
    (ht : ∀ i, Tube δ (x i) (v i) ⊆ Cylinder (C * θ) z w) :
    (n : ℝ) * δ ^ 2 ≤ m * (8 * (6 + C) * C ^ 2) * θ ^ 2 := by
  have hh := hc (Cylinder (C * θ) z w) ((convex_segment z _).thickening _)
  simp only [ht, Set.ofPred_true, ncard_univ, Nat.card_fin] at hh
  have hh' := hh.trans (mul_le_mul' le_rfl (cylinder_scaled_volume_le hw z hC hθ hθ1))
  rw [← ENNReal.ofReal_mul hm] at hh'
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  simpa only [mul_assoc] using hh'

lemma cluster_slab_count {δ m C θ : ℝ} (hm : 0 ≤ m) (hC : 0 < C) (hθ : 0 < θ)
    {n k : ℕ} {x v : Fin n → Space} (hc : SlabCount δ m x v)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    {f : Fin k → Fin n} (hf : Function.Injective f)
    {z w : Space} (hw : ‖w‖ = 1)
    (ht : ∀ i, Tube δ (x (f i)) (v (f i)) ⊆ Cylinder (C * θ) z w) :
    (k : ℝ) ≤ (8 * C) * m * θ * (n : ℝ) := by
  obtain ⟨u, hu, huw⟩ := exists_unit_perp hw
  have hsub : ∀ i, Tube δ (x (f i)) (v (f i)) ⊆ Slab u (inner ℝ u z) (C * θ) :=
    fun i => subset_inter (hball _) ((ht i).trans (cylinder_subset_slab hu huw z _))
  have hk : (k : ℝ) ≤ ncard {i : Fin n |
      Tube δ (x i) (v i) ⊆ Slab u (inner ℝ u z) (C * θ)} := by
    exact_mod_cast all_subfamily_count_le hf hsub
  have hh := (ENNReal.ofReal_le_ofReal hk).trans
    (hc u (inner ℝ u z) (C * θ) hu (mul_pos hC hθ))
  have hh' := hh.trans (mul_le_mul' le_rfl (slab_volume_le hu _ _ (by positivity)))
  rw [← ENNReal.ofReal_mul (by positivity)] at hh'
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh'
  nlinarith

lemma slab_count_lower {δ m : ℝ} (hδ : 0 < δ) (hm : 0 ≤ m)
    {n : ℕ} (hn : 0 < n) {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1)
    (hc : SlabCount δ m x v) (ht : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) :
    1 ≤ 8 * m * (n : ℝ) * δ := by
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨u, hu, huv⟩ := exists_unit_perp (hv i)
  have hi : Tube δ (x i) (v i) ⊆ Slab u (inner ℝ u (x i)) δ :=
    subset_inter (ht i) (tube_subset_slab hu huv _ _)
  have hncard : 1 ≤ ncard {j : Fin n | Tube δ (x j) (v j) ⊆ Slab u (inner ℝ u (x i)) δ} :=
    (Set.ncard_pos (by toFinite_tac)).mpr ⟨i, hi⟩
  have hh : ENNReal.ofReal 1 ≤ ENNReal.ofReal (m * (n : ℝ)) *
      ENNReal.ofReal (8 * δ) :=
    ((ENNReal.ofReal_le_ofReal (by exact_mod_cast hncard)).trans
      (hc u (inner ℝ u (x i)) δ hu hδ)).trans
        (mul_le_mul' le_rfl (slab_volume_le hu _ _ hδ.le))
  rw [← ENNReal.ofReal_mul (by positivity)] at hh
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  nlinarith

lemma global_count {δ m : ℝ} (hm : 0 ≤ m) {n : ℕ} {x v : Fin n → Space}
    (hc : ConvexCount δ m x v) (ht : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) :
    (n : ℝ) * δ ^ 2 ≤ m * Vol (ball 0 1) := by
  have hh := hc (ball 0 1) (convex_ball _ _)
  simp only [ht, Set.ofPred_true, ncard_univ, Nat.card_fin] at hh
  have hh' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    measure_ball_lt_top.ne) hh
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm,
    ENNReal.toReal_ofReal (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity)] using hh'

end WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters
