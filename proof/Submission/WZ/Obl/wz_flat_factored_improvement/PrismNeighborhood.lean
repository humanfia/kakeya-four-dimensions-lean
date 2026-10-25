-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.PrismNeighborhood.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatMap
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridUnion

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridCell gridUnion gridCell_dist_lt)

def dilatedPrism (r a b : ℝ) : Set Space :=
  {p | |p 0| ≤ r * a ∧ |p 1| ≤ r * b ∧ |p 2| ≤ 2 * r}

theorem dilatedPrism_closed (r a b : ℝ) : IsClosed (dilatedPrism r a b) := by
  exact (isClosed_le (show Continuous (fun p : Space => |p 0|) by fun_prop) continuous_const).inter
    ((isClosed_le (show Continuous (fun p : Space => |p 1|) by fun_prop) continuous_const).inter
      (isClosed_le (show Continuous (fun p : Space => |p 2|) by fun_prop) continuous_const))

theorem dilatedPrism_eq_preimage {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    dilatedPrism r a b = (fun p : Space => r⁻¹ • p) ⁻¹' StandardPrism a b := by
  ext p
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  have hi (i : Fin 3) (s : ℝ) : |(r⁻¹ • p) i| ≤ s ↔ |p i| ≤ r * s := by
    change |r⁻¹ * p i| ≤ s ↔ _
    rw [abs_mul, abs_of_pos (inv_pos.mpr hr), inv_mul_le_iff₀ hr]
  rw [hi, hi, hi]
  simp only [mul_comm r 2]

theorem dilatedPrism_convex {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    Convex ℝ (dilatedPrism r a b) := by
  rw [dilatedPrism_eq_preimage hr]
  exact (standardPrism_convex a b).linear_preimage (r⁻¹ • LinearMap.id)

theorem dilatedPrism_volume {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume (dilatedPrism r a b) = ENNReal.ofReal (16 * r ^ 3 * a * b) := by
  let B := EuclideanSpace.basisFun (Fin 3) ℝ
  have he : dilatedPrism r a b = {p : Space | ∀ i,
      ![-(r * a), -(r * b), -(2 * r)] i ≤ B.repr (p - 0) i ∧
      B.repr (p - 0) i ≤ ![r * a, r * b, 2 * r] i} := by
    ext p
    simp [B, dilatedPrism, Fin.forall_fin_succ, abs_le]
  rw [he, WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume,
    Fin.prod_univ_three]
  change ENNReal.ofReal (r * a - -(r * a)) * ENNReal.ofReal (r * b - -(r * b)) *
    ENNReal.ofReal (2 * r - -(2 * r)) = _
  simp only [sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem dilatedPrism_norm {r a b : ℝ} (hr : 0 ≤ r) (hab : a ≤ b) (hb2 : b ≤ 2)
    {p : Space} (hp : p ∈ dilatedPrism r a b) : ‖p‖ ≤ 4 * r := by
  have hi (i : Fin 3) : |p i| ≤ 2 * r := by
    fin_cases i
    · exact hp.1.trans (by nlinarith [mul_le_mul_of_nonneg_left (hab.trans hb2) hr])
    · exact hp.2.1.trans (by nlinarith [mul_le_mul_of_nonneg_left hb2 hr])
    · exact hp.2.2
  have hh := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le (by positivity) hi
  linarith

theorem dilatedPrism_compact {r a b : ℝ} (hr : 0 ≤ r) (hab : a ≤ b) (hb2 : b ≤ 2) :
    IsCompact (dilatedPrism r a b) :=
  (isCompact_closedBall (0 : Space) (4 * r)).of_isClosed_subset (dilatedPrism_closed r a b)
    (fun p hp => mem_closedBall_zero_iff.mpr (dilatedPrism_norm hr hab hb2 hp))

theorem thickening_prism_subset {r a b : ℝ} (hr : 0 ≤ r) (hab : a ≤ b) (hb2 : b ≤ 2)
    (e : AffineIsometryEquiv ℝ Space Space) :
    thickening (r * a) (e '' StandardPrism a b) ⊆ e '' dilatedPrism (r + 1) a b := by
  intro p hp
  obtain ⟨q, ⟨z, hz, rfl⟩, hpq⟩ := mem_thickening_iff.mp hp
  refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
  have hd : dist (e.symm p) z < r * a := by
    rw [← e.symm.dist_map p (e z), e.symm_apply_apply] at hpq
    exact hpq
  have hi (i : Fin 3) : |e.symm p i| ≤ |z i| + r * a := by
    have hc : |e.symm p i - z i| ≤ dist (e.symm p) z := by
      simpa [dist_eq_norm] using PiLp.norm_apply_le (e.symm p - z) i
    have ha := abs_add_le (e.symm p i - z i) (z i)
    rw [sub_add_cancel] at ha
    linarith
  refine ⟨?_, ?_, ?_⟩
  · linarith [hi 0, hz.1]
  · nlinarith [hi 1, hz.2.1, mul_le_mul_of_nonneg_left hab hr]
  · nlinarith [hi 2, hz.2.2, mul_le_mul_of_nonneg_left (hab.trans hb2) hr]

theorem gridUnion_flat_subset {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb2 : b ≤ 2)
    (e : AffineIsometryEquiv ℝ Space Space) (s : Finset (Fin 3 → ℤ))
    (hs : ∀ z ∈ s, (e '' StandardPrism a b ∩ gridCell a z).Nonempty) :
    gridUnion a s ⊆ e '' dilatedPrism 3 a b := by
  have hh := thickening_prism_subset (r := 2) (by norm_num) hab hb2 e
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num] at hh
  apply Subset.trans _ hh
  exact Set.iUnion₂_subset fun z hz =>
    WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_subset_neighborhood ha (hs z hz)

theorem gridUnion_flat_volume {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb2 : b ≤ 2)
    (e : AffineIsometryEquiv ℝ Space Space) (s : Finset (Fin 3 → ℤ))
    (hs : ∀ z ∈ s, (e '' StandardPrism a b ∩ gridCell a z).Nonempty) :
    volume (gridUnion a s) ≤ ENNReal.ofReal (432 * a * b) := by
  have hh := measure_mono (μ := volume) (gridUnion_flat_subset ha hab hb2 e s hs)
  rw [WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image,
    dilatedPrism_volume (by norm_num : (0 : ℝ) ≤ 3) ha.le (ha.le.trans hab)] at hh
  convert hh using 1 <;> norm_num

end WangZahlLot.Obl.wz_flat_factored_improvement
