-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormCount
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormCenter
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDiff
import Submission.WZ.Obl.wz_separated_cover_refinement.Refinement

/-!
# The zoomed family

For a set `Q` of tubes through the zoom centre, `zx`, `zv`, `zY` are the zoomed unit pieces and
their shadings, indexed by `Fin Q.card`. They form a dense family at scale `lam δ` once `Q` has
no level-zero conflicts and a good mass ratio.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_mem enumerate_injective
  enumerate_surjective enumerate_sum enumerate_count CoverAt)

section

variable {n : ℕ} (c : Space) (lam δ : ℝ) (x v : Fin n → Space) (Y : Fin n → Set Space)
  (Q : Finset (Fin n))

/-- Zoomed piece starts. -/
noncomputable def zx (a : Fin Q.card) : Space :=
  pieceStart c lam (x (enumerate Q a)) (v (enumerate Q a))

/-- Zoomed piece directions. -/
noncomputable def zv (a : Fin Q.card) : Space := v (enumerate Q a)

/-- Zoomed shadings. -/
noncomputable def zY (a : Fin Q.card) : Set Space :=
  zoom c lam '' (Y (enumerate Q a) ∩ subTube c lam δ (x (enumerate Q a)) (v (enumerate Q a)))

end

theorem zoom_image_eq_preimage {c : Space} {lam : ℝ} (hlam : lam ≠ 0) (A : Set Space) :
    zoom c lam '' A = (fun q => c + lam⁻¹ • q) ⁻¹' A := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    show c + lam⁻¹ • (lam • (p - c)) ∈ A
    rwa [smul_smul, inv_mul_cancel₀ hlam, one_smul, add_sub_cancel]
  · intro hq
    refine ⟨c + lam⁻¹ • q, hq, ?_⟩
    simp only [zoom, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam, one_smul]

theorem measurableSet_zoom_image {c : Space} {lam : ℝ} (hlam : lam ≠ 0) {A : Set Space}
    (hA : MeasurableSet A) : MeasurableSet (zoom c lam '' A) := by
  rw [zoom_image_eq_preimage hlam]
  exact (continuous_const.add (continuous_const_smul _)).measurable hA

theorem volume_zoom_image {c : Space} {lam : ℝ} (hlam : 0 < lam) (A : Set Space) :
    volume (zoom c lam '' A) = ENNReal.ofReal (lam ^ 3) * volume A := by
  have he : zoom c lam '' A = (fun y => y + -c) '' (AffineMap.homothety c lam '' A) := by
    rw [image_image]
    congr 1
    funext p
    rw [AffineMap.homothety_apply]
    simp only [zoom, vsub_eq_sub, vadd_eq_add]
    abel
  rw [he, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_image_homothety,
    finrank_euclideanSpace_fin, abs_of_pos (by positivity)]

theorem foot_close_of_mem_through {n : ℕ} {c : Space} {lam : ℝ} {x v : Fin n → Space}
    (hv : ∀ i, ‖v i‖ = 1) {i : Fin n} (hi : i ∈ zoomThrough c lam x v) :
    ‖c - foot c (x i) (v i)‖ ≤ 1 / (4 * lam) := by
  obtain ⟨t, -, ht⟩ := mem_zoomThrough.mp hi
  exact (norm_sub_foot_le (hv i) t).trans ht

theorem param_mem_of_mem_through {n : ℕ} {c : Space} {lam : ℝ} {x v : Fin n → Space}
    (hv : ∀ i, ‖v i‖ = 1) {i : Fin n} (hi : i ∈ zoomThrough c lam x v) :
    inner ℝ (c - x i) (v i) ∈ Icc (-(1 / (4 * lam))) (1 + 1 / (4 * lam)) := by
  obtain ⟨t, ht, hct⟩ := mem_zoomThrough.mp hi
  have h := (abs_param_sub_le (hv i) t).trans hct
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith [ht.1, ht.2]

theorem norm_sub_x_le_of_mem_through {n : ℕ} {c : Space} {lam : ℝ} (hlam : 1 ≤ lam)
    {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1) {i : Fin n} (hi : i ∈ zoomThrough c lam x v) :
    ‖c - x i‖ ≤ 2 := by
  obtain ⟨t, ht, hct⟩ := mem_zoomThrough.mp hi
  have hlam0 : 0 < lam := by linarith
  calc ‖c - x i‖ = ‖(c - (x i + t • v i)) + t • v i‖ := by congr 1; abel
    _ ≤ ‖c - (x i + t • v i)‖ + ‖t • v i‖ := norm_add_le _ _
    _ ≤ 1 / (4 * lam) + 1 := by
        rw [norm_smul, hv i, mul_one, Real.norm_eq_abs, abs_of_nonneg ht.1]
        linarith [ht.2]
    _ ≤ 2 := by
        have : 1 / (4 * lam) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        linarith

/-- The zoomed family is dense. -/
theorem dense_zoom {n : ℕ} {c : Space} {lam δ η₁ : ℝ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} {Q : Finset (Fin n)} (hlam : 1 ≤ lam) (hδ : 0 < δ)
    (hlδ : lam * δ ≤ 1 / 10000) (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hQ : Q ⊆ zoomThrough c lam x v) (hQpos : 0 < Q.card)
    (hdist : ∀ i ∈ Q, ∀ i' ∈ Q, i ≠ i' →
      ¬ conflict c lam (lam * δ) x v (· ∈ zoomThrough c lam x v) i i')
    (hmass : (lam * δ) ^ η₁ * Q.card * (lam * δ) ^ 2 ≤
      lam ^ 3 * ∑ i ∈ Q, (volume (Y i ∩ subTube c lam δ (x i) (v i))).toReal)
    (hfin : ∀ i, volume (Y i ∩ subTube c lam δ (x i) (v i)) ≠ ∞) :
    WangZahlLot.Obl.wz_separated_cover_refinement.Dense η₁ (lam * δ) Q.card (zx c lam x v Q) (zv v Q)
      (zY c lam δ x v Y Q) := by
  have hlam0 : 0 < lam := by linarith
  refine ⟨hQpos, fun a => hv _, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact piece_subset_ball hlam0 (hv _) (foot_close_of_mem_through hv (hQ (enumerate_mem Q a)))
      (by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith) (by linarith)
  · intro a b hab
    have hne : enumerate Q a ≠ enumerate Q b := (enumerate_injective Q).ne hab
    exact half_of_not_conflict (by positivity) hlδ hv (hQ (enumerate_mem Q a))
      (hQ (enumerate_mem Q b)) hne
      (hdist _ (enumerate_mem Q a) _ (enumerate_mem Q b) hne)
  · intro a
    exact measurableSet_zoom_image hlam0.ne' ((hYm _).inter isOpen_thickening.measurableSet)
  · rintro a _ ⟨p, ⟨-, hp⟩, rfl⟩
    exact zoom_mem_piece hlam0 hp
  · have hsum : ∑ a, volume (zY c lam δ x v Y Q a) = ∑ i ∈ Q,
        ENNReal.ofReal (lam ^ 3) * volume (Y i ∩ subTube c lam δ (x i) (v i)) := by
      rw [← enumerate_sum Q (fun i => ENNReal.ofReal (lam ^ 3) *
        volume (Y i ∩ subTube c lam δ (x i) (v i)))]
      refine sum_congr rfl fun a _ => ?_
      exact volume_zoom_image hlam0 _
    rw [hsum, ← mul_sum]
    have hS : ∑ i ∈ Q, volume (Y i ∩ subTube c lam δ (x i) (v i)) =
        ENNReal.ofReal (∑ i ∈ Q, (volume (Y i ∩ subTube c lam δ (x i) (v i))).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
      exact sum_congr rfl fun i _ => (ENNReal.ofReal_toReal (hfin i)).symm
    rw [hS, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hmass

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
