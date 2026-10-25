-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.DenseNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Normalization

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

lemma card_le_of_container {s L B : ℝ} (hs : 0 < s) (hL : 0 ≤ L) (hB : 0 ≤ B)
    {n : ℕ} {U : Fin n → Set Space} (hK : ConvexCount s L (fun _ => True) U)
    (I : Finset (Fin n)) {W : Set Space} (hW : Convex ℝ W)
    (hvol : volume W ≤ ENNReal.ofReal (B * s ^ 2)) (hI : ∀ i ∈ I, U i ⊆ W) :
    (I.card : ℝ) ≤ B * L := by
  have hc : I.card ≤ {i | U i ⊆ W}.ncard := by
    simpa using (Set.ncard_mono (a := (I : Set (Fin n))) (b := {i | U i ⊆ W})
      (fun i hi => hI i hi))
  have hk := hK W hW
  simp only [true_and] at hk
  have hb : ENNReal.ofReal ((I.card : ℝ) * s ^ 2) ≤ ENNReal.ofReal (B * L * s ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (({i | U i ⊆ W}.ncard : ℝ) * s ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (sq_nonneg s))
      _ ≤ ENNReal.ofReal L * volume W := hk
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (B * s ^ 2) := mul_le_mul_right hvol _
      _ = _ := by rw [← ENNReal.ofReal_mul hL]; congr 1; ring
  have hp : 0 < s ^ 2 := sq_pos_of_pos hs
  have hb' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hB hL) hp.le)).mp hb
  exact (mul_le_mul_iff_left₀ hp).mp hb'

/-- A normalized separated net, using the convex count to control repeated children. -/
lemma normalize_net (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {r s L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) (hsr : s ≤ r) (hL : 0 ≤ L)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, tube s (x i) (v i) ⊆ tube r y w)
    (hK : ConvexCount s L (fun _ => True) (fun i => tube s (x i) (v i)))
    (I : Finset (Fin n)) (hI : I.Nonempty) :
    ∃ (M : ℕ) (j : Fin M → Fin n) (z u : Fin M → Space),
      0 < M ∧ Function.Injective j ∧ (∀ i, j i ∈ I) ∧ (∀ i, ‖u i‖ = 1) ∧
      (∀ i, tube (normalizedRadius r s) (z i) (u i) ⊆ ball 0 1) ∧
      (∀ i i', i ≠ i' → volume (tube (normalizedRadius r s) (z i) (u i) ∩
        tube (normalizedRadius r s) (z i') (u i')) ≤
          (1 / 2 : ENNReal) * volume (tube (normalizedRadius r s) (z i) (u i))) ∧
      (∀ i, normalize e y w r hr '' tube s (x (j i)) (v (j i)) ⊆
        tube (normalizedRadius r s) (z i) (u i)) ∧
      (∀ i, z i + (1 / 2 : ℝ) • u i = normalize e y w r hr (x (j i) + (1 / 2 : ℝ) • v (j i))) ∧
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst * (I.card : ℝ) ≤
        (M : ℝ) * (fiberVolume * L) := by
  classical
  have hdata := fun i => normalize_child_prism e hew hr hr1 hs hsr (x i) (v i) (hv i) (hT i)
  choose b hb hprism using fun i => (hdata i).2
  let c := fun i => normalize e y w r hr (x i + (1 / 2 : ℝ) • v i)
  have hρ : 0 < contraction * r⁻¹ * s := by positivity
  have hρ1 : contraction * r⁻¹ * s ≤ 1 / 1000000 := by
    have h := normalizedRadius_le hr hsr
    dsimp [normalizedRadius, contraction] at h ⊢
    linarith
  obtain ⟨M, k, F, hM, hk, hFI, hFne, hFdisj, hmass, hcover, hsep⟩ :=
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.net_cover I hI hρ.le le_rfl hρ hρ1
      c b (fun i _ => hb i) (fun i _ => (hdata i).1)
  let u : Fin M → Space := fun i => WangZahlLot.Obl.wz_transverse_cell_weighted_cover.axisDir (b (k i))
  let z : Fin M → Space := fun i => c (k i) - (1 / 2 : ℝ) • u i
  have hu : ∀ i, ‖u i‖ = 1 := fun i =>
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.norm_axisDir (hb (k i))
  have hinc : ∀ i a, a ∈ F i → normalize e y w r hr '' tube s (x a) (v a) ⊆
      tube (normalizedRadius r s) (z i) (u i) :=
    fun i a ha => (hprism a).trans (hcover i a ha)
  have hball : ∀ i, tube (normalizedRadius r s) (z i) (u i) ⊆ ball (0 : Space) 1 := by
    intro i
    exact WangZahlLot.Obl.wz_transverse_cell_weighted_cover.cTube_subset_ball
      hρ.le (by linarith) (hb (k i)) ((hdata (k i)).1)
  have hinj : Function.Injective k := by
    intro i i' he
    by_contra hne
    have hover : volume (tube (normalizedRadius r s) (z i) (u i)) ≤
        (1 / 2 : ENNReal) * volume (tube (normalizedRadius r s) (z i) (u i)) := by
      simpa only [z, u, he, WangZahlLot.Obl.wz_transverse_cell_weighted_cover.cTube,
        Set.inter_self, tube, normalizedRadius, WangZahlLot.Obl.wz_transverse_cell_weighted_cover.tube] using hsep i i' hne
    have hpos : volume (tube (normalizedRadius r s) (z i) (u i)) ≠ 0 := by
      exact ne_of_gt (WangZahlLot.Obl.wz_tube_packing_bound.tube_volume_pos
        (normalizedRadius_pos hr hs) _ _)
    have hfin : volume (tube (normalizedRadius r s) (z i) (u i)) ≠ ⊤ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (hball i))
    have hh : (1 : ENNReal) ≤ 1 / 2 := (ENNReal.mul_le_mul_iff_left hpos hfin).mp
      (by simpa only [one_mul] using hover)
    norm_num at hh
  refine ⟨M, k, z, u, hM, hinj, hk, hu, hball, hsep, ?_, ?_, ?_⟩
  · intro i
    exact (hprism (k i)).trans
      (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism_subset_cTube hρ.le le_rfl hρ (hb (k i)))
  · intro i
    simp only [z, sub_add_cancel]
    rfl
  · calc
      _ ≤ ∑ i, ((F i).card : ℝ) := hmass
      _ ≤ ∑ _i : Fin M, fiberVolume * L := by
        apply Finset.sum_le_sum
        intro i _
        exact card_le_of_container hs hL (by norm_num : 0 ≤ fiberVolume) hK (F i)
          ((tube_convex _ _ _).affine_preimage (normalize e y w r hr).toAffineEquiv.toAffineMap)
          (normalize_preimage_tube_volume e y w hr hs hsr (z i) (u i) (hu i))
          (fun a ha p hp => hinc i a ha ⟨p, hp, rfl⟩)
      _ = _ := by simp

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
