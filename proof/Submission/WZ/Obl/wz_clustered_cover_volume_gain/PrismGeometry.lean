-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.PrismGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarsePrism
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismBridge

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)

def frozenBasis (e : V ≃ₗᵢ[ℝ] V) : OrthonormalBasis (Fin 3) ℝ V :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).map e.symm

@[simp] lemma frozenBasis_apply (e : V ≃ₗᵢ[ℝ] V) (j : Fin 3) :
    frozenBasis e j = boxAxis e j := rfl

lemma frozen_prism_box (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    P a b c z e = orthogonalBox ![a / 2, b / 2, c / 2] z (frozenBasis e) := by
  ext p
  simp only [orthogonalBox, P, ι, Set.mem_ofPred_eq, frozenBasis_apply, inner_boxAxis]
  constructor
  · intro hp j
    fin_cases j
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
  · intro hp
    exact ⟨hp 0, hp 1, hp 2⟩

lemma frozen_prism_volume {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) : volume (P a b c z e) = ENNReal.ofReal (a * b * c) := by
  rw [frozen_prism_box, volume_orthogonalBox]
  · congr 1
    norm_num [Fin.prod_univ_three]
    ring
  · intro j
    fin_cases j <;> simp <;> positivity

lemma frozen_prism_norm {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) {p : V} (hp : p ∈ P a b c z e) : ‖p - z‖ ≤ c := by
  have hP : p ∈ P a c c z e := ⟨hp.1, hp.2.1.trans (by linarith), hp.2.2⟩
  have hh := prism_norm_le ha (hab.trans hbc) z e hP
  linarith [ha.trans (hab.trans hbc)]

lemma frozen_prism_compact {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) : IsCompact (P a b c z e) := by
  apply (isCompact_closedBall z c).of_isClosed_subset
  · rw [frozen_prism_box]
    exact orthogonalBox_closed _ _ _
  · intro p hp
    exact frozen_prism_norm ha hab hbc z e hp

lemma frozen_prism_convex (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    Convex ℝ (P a b c z e) := by
  rw [frozen_prism_box]
  exact orthogonalBox_convex _ _ _

lemma ball_subset_frozen_prism {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) : ball z (a / 2) ⊆ P a b c z e := by
  intro p hp
  have hh (j : Fin 3) : |e (p - z) j| ≤ a / 2 := by
    have h := PiLp.norm_apply_le (e (p - z)) j
    rw [Real.norm_eq_abs, e.norm_map] at h
    exact h.trans hp.le
  exact ⟨hh 0, (hh 1).trans (by linarith), (hh 2).trans (by linarith)⟩

lemma frozen_prism_ends {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    z + (c / 2) • boxAxis e 2 ∈ P a b c z e ∧
      z - (c / 2) • boxAxis e 2 ∈ P a b c z e := by
  rw [frozen_prism_box]
  have hmem (t : ℝ) (ht : |t| ≤ c / 2) :
      z + t • boxAxis e 2 ∈ orthogonalBox ![a / 2, b / 2, c / 2] z (frozenBasis e) := by
    intro j
    rw [add_sub_cancel_left, inner_smul_right]
    change |t * inner ℝ (frozenBasis e j) (frozenBasis e 2)| ≤ _
    rw [(frozenBasis e).inner_eq_ite]
    fin_cases j
    · norm_num
      positivity
    · norm_num
      positivity
    · simpa using ht
  constructor
  · exact hmem _ (by rw [abs_of_nonneg (by positivity : 0 ≤ c / 2)])
  · simpa only [neg_smul, sub_eq_add_neg] using hmem (-(c / 2))
      (by rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ c / 2)])

/-- Uniform bounds for each frozen grain after coarse transverse dilation. -/
lemma frozen_prism_coarse_bounds {θ a b c : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ θ * c) (hc : 0 < c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) (haxis : ‖coarseLinear θ (boxAxis e 2)‖ ≤ 43) :
    ∀ p ∈ P a b c z e,
      ‖coarseLinear θ (p - z)‖ ≤ 25 * c ∧
      |inner ℝ (unit (dualLinear θ (boxAxis e 0))) (coarseLinear θ (p - z))| ≤ a / θ := by
  obtain ⟨u, hu0, hu2, hU⟩ := coarse_prism_enclosure hθ hθ1 (by positivity : 0 ≤ a / 2)
    (show a / 2 ≤ b / 2 by linarith) (show b / 2 ≤ θ * (c / 2) by nlinarith)
    (by positivity : 0 ≤ c / 2) (by norm_num : (0 : ℝ) ≤ 43) (frozenBasis e) z haxis
  have habc : a / (2 * θ) ≤ c / 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hbc' : b / θ ≤ c := (div_le_iff₀ hθ).mpr (by nlinarith)
  intro p hp
  have hh := hU ⟨p, by rwa [← frozen_prism_box], rfl⟩
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  change |inner ℝ (u 0) (coarseLinear θ p - coarseLinear θ z)| ≤ (a / 2) / θ at h0
  change |inner ℝ (u 1) (coarseLinear θ p - coarseLinear θ z)| ≤ 2 * (b / 2) / θ at h1
  change |inner ℝ (u 2) (coarseLinear θ p - coarseLinear θ z)| ≤ (43 + 2) * (c / 2) at h2
  rw [← map_sub] at h0 h1 h2
  constructor
  · have hn := norm_le_coord_sum (u.repr (coarseLinear θ (p - z)))
    simp only [u.repr.norm_map, OrthonormalBasis.repr_apply_apply] at hn
    have he : a / 2 / θ = a / (2 * θ) := by ring
    have he' : 2 * (b / 2) / θ = b / θ := by ring
    rw [he] at h0
    rw [he'] at h1
    linarith
  · rw [hu0, frozenBasis_apply] at h0
    exact h0.trans (div_le_div_of_nonneg_right (by linarith) hθ.le)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
