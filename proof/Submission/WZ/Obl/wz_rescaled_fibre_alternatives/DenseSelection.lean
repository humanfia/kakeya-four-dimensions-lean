-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.DenseSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.DenseNet
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ForwardCounts

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

noncomputable def selectedFraction : ℝ :=
  WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst / (112 * fiberVolume)

lemma selectedFraction_pos : 0 < selectedFraction := by
  exact div_pos WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst_pos (by norm_num)

lemma dense_shadings {s lam : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hlam : 0 < lam)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ tube s (x i) (v i))
    (hden : ENNReal.ofReal (lam * n * s ^ 2) ≤ ∑ i, volume (Y i)) :
    ∃ I : Finset (Fin n), I.Nonempty ∧ (lam / 112) * n ≤ (I.card : ℝ) ∧
      ∀ i ∈ I, ENNReal.ofReal (lam / 2 * s ^ 2) ≤ volume (Y i) := by
  classical
  have hup (i : Fin n) : volume (Y i) ≤ ENNReal.ofReal (56 * s ^ 2) :=
    (measure_mono (hYT i)).trans
      (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hs.le hs1 _ _ (hv i))
  have hfin (i : Fin n) : volume (Y i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup i)
  let f : Fin n → ℝ := fun i => (volume (Y i)).toReal
  have hf : ∀ i, f i ≤ 56 * s ^ 2 := fun i =>
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hup i)
  have he : ENNReal.ofReal (∑ i, f i) = ∑ i, volume (Y i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
    simp only [f, ENNReal.ofReal_toReal (hfin _)]
  have hmass : lam * n * s ^ 2 ≤ ∑ i, f i := by
    rw [← he] at hden
    exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))).mp hden
  let t := lam / 2 * s ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hm : 2 * n * t ≤ ∑ i, f i := by dsimp [t]; nlinarith only [hmass]
  have hI := WangZahlLot.Obl.wz_nonflat_factored_improvement.dense_indices f ht.le hf hm
  let I := Finset.univ.filter (fun i => t ≤ f i)
  have hsize : (lam / 112) * n ≤ (I.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 56 * s ^ 2)).mp
    convert hI.2 using 1 <;> dsimp [t] <;> ring
  have hne : I.Nonempty := by
    apply Finset.card_pos.mp
    exact Nat.cast_pos.mp ((mul_pos (by positivity) (Nat.cast_pos.mpr hn)).trans_le hsize)
  refine ⟨I, hne, hsize, ?_⟩
  intro i hi
  have hh := (Finset.mem_filter.mp hi).2
  calc
    _ ≤ ENNReal.ofReal (f i) := ENNReal.ofReal_le_ofReal hh
    _ = _ := ENNReal.ofReal_toReal (hfin i)

/-- A dense fibre admits an injectively selected, essentially distinct normalized family.
The cardinality loss depends on the convex-count constant, so repetitions are allowed. -/
lemma normalize_dense (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {r s L lam : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) (hsr : s ≤ r) (hL : 0 < L) (hlam : 0 < lam)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hT : ∀ i, tube s (x i) (v i) ⊆ tube r y w)
    (hYT : ∀ i, Y i ⊆ tube s (x i) (v i))
    (hden : ENNReal.ofReal (lam * n * s ^ 2) ≤ ∑ i, volume (Y i))
    (hK : ConvexCount s L (fun _ => True) (fun i => tube s (x i) (v i))) :
    ∃ (M : ℕ) (j : Fin M → Fin n) (z u : Fin M → Space),
      0 < M ∧ Function.Injective j ∧ (∀ i, ‖u i‖ = 1) ∧
      (∀ i, tube (normalizedRadius r s) (z i) (u i) ⊆ ball 0 1) ∧
      (∀ i i', i ≠ i' → volume (tube (normalizedRadius r s) (z i) (u i) ∩
        tube (normalizedRadius r s) (z i') (u i')) ≤
          (1 / 2 : ENNReal) * volume (tube (normalizedRadius r s) (z i) (u i))) ∧
      (∀ i, normalize e y w r hr '' tube s (x (j i)) (v (j i)) ⊆
        tube (normalizedRadius r s) (z i) (u i)) ∧
      (∀ i, z i + (1 / 2 : ℝ) • u i = normalize e y w r hr (x (j i) + (1 / 2 : ℝ) • v (j i))) ∧
      (∀ i, ENNReal.ofReal (lam / 2 * s ^ 2) ≤ volume (Y (j i))) ∧
      (selectedFraction * (lam / L)) * n ≤ (M : ℝ) := by
  obtain ⟨I, hI, hsize, hdenI⟩ := dense_shadings hs (hsr.trans hr1) hlam hn x v Y hv hYT hden
  obtain ⟨M, j, z, u, hM, hj, hjI, hu, hball, hsep, hcover, hmid, hcard⟩ :=
    normalize_net e hew hr hr1 hs hsr hL.le x v hv hT hK I hI
  refine ⟨M, j, z, u, hM, hj, hu, hball, hsep, hcover, hmid, fun i => hdenI _ (hjI i), ?_⟩
  have hc := (mul_le_mul_of_nonneg_left hsize
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst_pos.le).trans hcard
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < fiberVolume * L)).mp
  convert hc using 1
  dsimp [selectedFraction]
  field_simp <;> ring

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
