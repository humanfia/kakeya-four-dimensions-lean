-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.ShortMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.PrismNeighborhood
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyTransport
import Submission.WZ.Obl.wz_flat_factored_improvement.Cordoba

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube closedTube_convex closedTube_volume_bounds tube_subset_closedTube slab)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit inner_coords)

noncomputable section

def shortScales (a : ℝ) : Fin 3 → ℝ := ![1 / (64 * a), 1 / 64, 1 / 64]

theorem shortScales_pos {a : ℝ} (ha : 0 < a) : ∀ i, 0 < shortScales a i := by
  intro i; fin_cases i <;> dsimp [shortScales] <;> positivity

def shortMap (e : AffineIsometryEquiv ℝ Space Space) (a : ℝ) (ha : 0 < a) : Space ≃ᵃ[ℝ] Space :=
  coordinateAffine e (shortScales a) (fun i => (shortScales_pos ha i).ne')

theorem shortMap_apply (e : AffineIsometryEquiv ℝ Space Space) {a : ℝ}
    (ha : 0 < a) (p : Space) (i : Fin 3) :
    shortMap e a ha p i = shortScales a i * e.symm p i := rfl

theorem shortMap_volume (e : AffineIsometryEquiv ℝ Space Space) {a : ℝ}
    (ha : 0 < a) (U : Set Space) :
    volume (shortMap e a ha '' U) = ENNReal.ofReal (1 / (262144 * a)) * volume U := by
  rw [shortMap, coordinateAffine_volume e _ (shortScales_pos ha)]
  congr 2
  rw [Fin.prod_univ_three]
  dsimp [shortScales]
  ring

theorem closedTube_isCompact (r : ℝ) (x v : Space) : IsCompact (closedTube r x v) := by
  have hs : IsCompact (segment ℝ x (x + v)) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  exact isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded.thickening.closure

theorem thickTube_subset_dilatedPrism {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (hb2 : b ≤ 2)
    (e : AffineIsometryEquiv ℝ Space Space) {x v : Space}
    (hT : Tube δ x v ⊆ e '' StandardPrism a b) :
    closedTube (3 * a) x v ⊆ e '' dilatedPrism 4 a b := by
  have hseg : segment ℝ x (x + v) ⊆ e '' StandardPrism a b := (self_subset_thickening hδ _).trans hT
  have hh := (thickening_subset_of_subset (3 * a) hseg).trans
    (thickening_prism_subset (by norm_num : (0 : ℝ) ≤ 3) hab hb2 e)
  norm_num only [show (3 : ℝ) + 1 = 4 by norm_num] at hh
  exact closure_minimal hh (e.toHomeomorph.isClosedMap _ (dilatedPrism_closed 4 a b))

theorem shortMap_thickTube_bounded {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb2 : b ≤ 2) (e : AffineIsometryEquiv ℝ Space Space) {x v : Space}
    (hT : Tube δ x v ⊆ e '' StandardPrism a b) :
    shortMap e a ha '' closedTube (3 * a) x v ⊆ closedBall (0 : Space) 1 := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨z, hz, rfl⟩ := thickTube_subset_dilatedPrism hδ hab hb2 e hT hp
  have hi (i : Fin 3) : |shortMap e a ha (e z) i| ≤ 1 / 8 := by
    rw [shortMap_apply, e.symm_apply_apply, abs_mul, abs_of_pos (shortScales_pos ha i)]
    fin_cases i <;> dsimp [shortScales]
    · have hh := mul_le_mul_of_nonneg_left hz.1 (by positivity : 0 ≤ 1 / (64 * a))
      have he : 1 / (64 * a) * (4 * a) = 1 / 16 := by field_simp; norm_num
      rw [he] at hh
      linarith
    · linarith [hz.2.1]
    · linarith [hz.2.2]
  have hh := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le (by norm_num) hi
  exact mem_closedBall_zero_iff.mpr (by linarith)

theorem exists_transverse_coordinate_normal (v : Space) :
    ∃ u : Space, ‖u‖ = 1 ∧ u 0 = 0 ∧ inner ℝ u v = 0 := by
  by_cases hv : v 1 = 0
  · refine ⟨EuclideanSpace.basisFun (Fin 3) ℝ 1, by simp, by simp [EuclideanSpace.basisFun_apply], ?_⟩
    change inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ 1) v = 0
    rw [EuclideanSpace.basisFun_inner]
    exact hv
  · let w : Space := WithLp.toLp 2 ![0, -v 2, v 1]
    have hw : w ≠ 0 := by
      intro hh
      have hi := congrArg (fun p : Space => p 2) hh
      exact hv (by simpa [w] using hi)
    refine ⟨unit w, norm_unit hw, ?_, ?_⟩
    · simp [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit, w]
    · have hh : inner ℝ w v = 0 := by rw [inner_coords]; simp [w]; ring
      simpa [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit, inner_smul_left] using congrArg (fun t => ‖w‖⁻¹ * t) hh

theorem shortMap_inner (e : AffineIsometryEquiv ℝ Space Space) {a : ℝ} (ha : 0 < a)
    {u : Space} (hu0 : u 0 = 0) (p x : Space) :
    inner ℝ u (shortMap e a ha p) - inner ℝ u (shortMap e a ha x) =
      (1 / 64 : ℝ) * (inner ℝ (e.linearIsometryEquiv u) p - inner ℝ (e.linearIsometryEquiv u) x) := by
  have he : e.symm p - e.symm x = e.linearIsometryEquiv.symm (p - x) := by
    change e.symm p - e.symm x = e.symm.linearIsometryEquiv (p - x)
    exact (e.symm.map_vsub p x).symm
  have hi : inner ℝ u (e.symm p - e.symm x) = inner ℝ (e.linearIsometryEquiv u) (p - x) := by
    rw [he]
    conv_rhs => rw [← e.linearIsometryEquiv.apply_symm_apply (p - x), LinearIsometryEquiv.inner_map_map]
  rw [← inner_sub_right, ← inner_sub_right]
  rw [← hi, inner_coords, inner_coords]
  simp [PiLp.sub_apply, shortMap_apply, shortScales, hu0]
  ring

theorem shortMap_thickTube_slab {a : ℝ} (ha : 0 < a)
    (e : AffineIsometryEquiv ℝ Space Space) (x v : Space) :
    ∃ u : Space, ‖u‖ = 1 ∧ ∃ s : ℝ,
      shortMap e a ha '' closedTube (3 * a) x v ⊆ slab (innerSL ℝ u) s a := by
  obtain ⟨u, hu, hu0, huv⟩ := exists_transverse_coordinate_normal (e.linearIsometryEquiv.symm v)
  have hν : ‖e.linearIsometryEquiv u‖ = 1 := by simpa using hu
  have hνv : inner ℝ (e.linearIsometryEquiv u) v = 0 := by
    rw [← e.linearIsometryEquiv.apply_symm_apply v, LinearIsometryEquiv.inner_map_map]
    exact huv
  have hsource : closedTube (3 * a) x v ⊆
      {p | |inner ℝ (e.linearIsometryEquiv u) p - inner ℝ (e.linearIsometryEquiv u) x| ≤ 3 * a} := by
    apply closure_minimal (WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab hν hνv x (3 * a))
    exact isClosed_le (by fun_prop) continuous_const
  refine ⟨u, hu, inner ℝ u (shortMap e a ha x), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  change |inner ℝ u (shortMap e a ha p) - inner ℝ u (shortMap e a ha x)| ≤ a
  rw [shortMap_inner e ha hu0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 64)]
  have hh : |inner ℝ (e.linearIsometryEquiv u) p - inner ℝ (e.linearIsometryEquiv u) x| ≤ 3 * a := hsource hp
  linarith

theorem BodyConvexCount.volume_weighted {n : ℕ} {U : Fin n → Set Space} {w m C : ℝ}
    (hC : 0 ≤ C) (hm : 0 ≤ m) (hc : BodyConvexCount U w m)
    (hv : ∀ i, volume (U i) ≤ ENNReal.ofReal (C * w)) : ConvexVolumeCount U (C * m) := by
  classical
  intro Q hQ
  let S := Finset.univ.filter (fun i => U i ⊆ Q)
  have he : (S.card : ℝ) = Set.ncard {i | U i ⊆ Q} := by
    simp [S, Set.ncard_eq_toFinset_card']
  calc
    _ = ∑ i ∈ S, volume (U i) := by simp only [S, Finset.sum_filter]
    _ ≤ ∑ _i ∈ S, ENNReal.ofReal (C * w) := Finset.sum_le_sum (fun i _ => hv i)
    _ = ENNReal.ofReal C * ENNReal.ofReal ((Set.ncard {i | U i ⊆ Q} : ℝ) * w) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), he,
        ← ENNReal.ofReal_mul hC]
      congr 1
      ring
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal m * volume Q) := mul_le_mul' le_rfl (hc Q hQ)
    _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]

end
end WangZahlLot.Obl.wz_flat_factored_improvement
