-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.AxialReframe.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.OrthogonalPair
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorBox
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.PacketCrossing
import Submission.WZ.Obl.wz_coarse_grains_assembly.CarrierNet

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, AxialReframe.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V P T boxAxis boxAxis_norm inner_boxAxis frozen_prism_norm)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit norm_sq_coords)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor (perp inner_perp)

/-- Rotate the two axes within a prism's plane so that a prescribed
direction has zero middle component. The short coordinate stays exact. -/
theorem exists_axial_frame (e : V ≃ₗᵢ[ℝ] V) {u : V}
    (hu : ‖u‖ = 1) (hshort : |e u 0| < 1) :
    ∃ e' : V ≃ₗᵢ[ℝ] V, (∀ p, e' p 0 = e p 0) ∧ e' u 1 = 0 := by
  classical
  let n := boxAxis e 0
  let p := perp n u
  have hn : ‖n‖ = 1 := boxAxis_norm e 0
  have hnp : inner ℝ n p = 0 := inner_perp hn u
  have hp : p ≠ 0 := by
    intro hp
    have he : u = inner ℝ n u • n := by
      exact sub_eq_zero.mp hp
    have hh := congrArg norm he
    rw [hu, norm_smul, Real.norm_eq_abs, hn, mul_one] at hh
    have heq : inner ℝ n u = e u 0 := inner_boxAxis e 0 u
    rw [heq] at hh
    linarith
  have hnl : inner ℝ n (unit p) = 0 := by
    simp only [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit, inner_smul_right, hnp, mul_zero]
  obtain ⟨B, hB0, hB2⟩ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.basis_of_orthogonal_pair
    hn (norm_unit hp) hnl
  refine ⟨B.repr, ?_, ?_⟩
  · intro q
    rw [B.repr_apply_apply, hB0]
    exact inner_boxAxis e 0 q
  · have hnorm : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    have hpunit : ‖p‖ • unit p = p := by
      simp only [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
    have hu' : u = (inner ℝ n u) • n + ‖p‖ • unit p := by
      rw [hpunit]
      dsimp [p, perp]
      module
    have hcoords : B.repr u = (inner ℝ n u) • EuclideanSpace.single 0 1 +
        ‖p‖ • EuclideanSpace.single 2 1 := by
      calc
        B.repr u = B.repr ((inner ℝ n u) • n + ‖p‖ • unit p) := congrArg B.repr hu'
        _ = _ := by rw [map_add, map_smul, map_smul, ← hB0, ← hB2, B.repr_self, B.repr_self]
    rw [hcoords]
    simp

/-- An axial frame gives small middle coordinates on a fixed fine
direction class while preserving the original short-direction bound. -/
theorem axial_frame_direction_bounds {θ a c : ℝ} {u v : V}
    (e e' : V ≃ₗᵢ[ℝ] V) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hc : 0 < c) (ha : a ≤ θ * c / 128)
    (hv : ‖v‖ = 1) (hvu : ‖v - u‖ ≤ θ / 100)
    (hshort : |e v 0| ≤ 6 * a / c)
    (hcoord : ∀ p, e' p 0 = e p 0) (hu1 : e' u 1 = 0) :
    1 / 2 ≤ |e' v 2| ∧ |e' v 0| ≤ 6 * a / c ∧ |e' v 1| ≤ θ / 100 := by
  have hzero : |e' v 0| ≤ 6 * a / c := by rw [hcoord]; exact hshort
  have hone : |e' v 1| ≤ θ / 100 := by
    have hh := (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.abs_rotated_coord_le
      e' (v - u) 1).trans hvu
    simpa only [map_sub, PiLp.sub_apply, hu1, sub_zero] using hh
  refine ⟨?_, hzero, hone⟩
  have hsmall : 6 * a / c ≤ 1 / 8 := by
    apply (div_le_iff₀ hc).mpr
    nlinarith
  have hnorm : (e' v 0) ^ 2 + (e' v 1) ^ 2 + (e' v 2) ^ 2 = 1 := by
    rw [← norm_sq_coords, e'.norm_map, hv]
    norm_num
  have h0 := sq_le_sq₀ (abs_nonneg (e' v 0)) (by norm_num : (0 : ℝ) ≤ 1 / 8) |>.mpr
    (hzero.trans hsmall)
  have h1 := sq_le_sq₀ (abs_nonneg (e' v 1)) (by norm_num : (0 : ℝ) ≤ 1 / 100) |>.mpr
    (hone.trans (by linarith))
  rw [sq_abs] at h0 h1
  have h2 := sq_abs (e' v 2)
  nlinarith [abs_nonneg (e' v 2)]

/-- A sufficiently long axial enlargement contains the old prism in its
one-eighth core. The short coordinate has not been rotated. -/
theorem axial_reframe_core {θ K a ρ c : ℝ} (e e' : V ≃ₗᵢ[ℝ] V) (z : V)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hK : 16 ≤ θ * K)
    (ha : 0 ≤ a) (hab : a ≤ ρ * c) (hbc : ρ * c ≤ c) (hc : 0 < c)
    (hcoord : ∀ p, e' p 0 = e p 0) :
    P a (ρ * c) c z e ⊆ P ((128 * K * a) / 8) ((θ * (K * c)) / 8) ((K * c) / 8) z e' := by
  have hK0 : 0 < K := by nlinarith
  have hK16 : 16 ≤ K := by nlinarith
  intro p hp
  have hn := frozen_prism_norm ha hab hbc z e hp
  have h1 := (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.abs_rotated_coord_le
    e' (p - z) 1).trans hn
  have h2 := (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.abs_rotated_coord_le
    e' (p - z) 2).trans hn
  refine ⟨?_, ?_, ?_⟩
  · change |e' (p - z) 0| ≤ _
    rw [hcoord]
    exact hp.1.trans (by nlinarith)
  · have hh := mul_le_mul_of_nonneg_right hK hc.le
    nlinarith
  · nlinarith

set_option maxHeartbeats 800000 in
/-- A fixed angular class can be put into long, axially aligned prisms
at a fixed small coarse radius. All old pieces and the endpoint room survive. -/
theorem axial_reframe_geometry {δ θ K a ρ c : ℝ} {x v y u z q : V}
    (e e' : V ≃ₗᵢ[ℝ] V) (hδ : 0 < δ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hK : 16 ≤ θ * K) (hδa : δ ≤ a) (hab : a ≤ ρ * c) (hbc : ρ * c ≤ c)
    (hthin : a ≤ θ * c / 128) (hsmall : K * c ≤ θ / 8)
    (hv : ‖v‖ = 1) (hvu : ‖v - u‖ ≤ θ / 100)
    (hshort : |e v 0| ≤ 6 * a / c)
    (hcoord : ∀ p, e' p 0 = e p 0) (hu1 : e' u 1 = 0)
    (hq : q ∈ T δ x v ∩ P a (ρ * c) c z e)
    (hleft : 100 * (K * c) < dist q x) (hright : 100 * (K * c) < dist q (x + v))
    (hcontain : T δ x v ⊆ T (θ / 4) y u) :
    P a (ρ * c) c z e ⊆ P (128 * K * a) (θ * (K * c)) (K * c) z e' ∧
    (∀ p ∈ T δ x v ∩ frontier (P (128 * K * a) (θ * (K * c)) (K * c) z e'),
      |e' (p - z) 2| = (K * c) / 2) ∧
    (∀ t ∈ ({-(K * c) / 2, (K * c) / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P (128 * K * a) (θ * (K * c)) (K * c) z e',
        e' (p - z) 2 = t) ∧
    P (128 * K * a) (θ * (K * c)) (K * c) z e' ⊆ T θ y u ∧
    (e' u 0) ^ 2 + (e' u 1) ^ 2 ≤ (10 * θ) ^ 2 ∧
    ∀ p ∈ P (128 * K * a) (θ * (K * c)) (K * c) z e',
      96 * (K * c) < dist p x ∧ 96 * (K * c) < dist p (x + v) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  have hδc : δ ≤ c := hδa.trans (hab.trans hbc)
  have hK0 : 0 < K := by nlinarith
  have hK16 : 16 ≤ K := by nlinarith
  have hKc : 0 < K * c := mul_pos hK0 hc
  have hnewab : 128 * K * a ≤ θ * (K * c) := by nlinarith
  have hnewbc : θ * (K * c) ≤ K * c := by nlinarith
  have hcore := axial_reframe_core e e' z hθ hθ1 hK ha.le hab hbc hc hcoord
  have hnewa : 0 < 128 * K * a := by positivity
  have hnewb : 0 < θ * (K * c) := by positivity
  have hsub : P a (ρ * c) c z e ⊆ P (128 * K * a) (θ * (K * c)) (K * c) z e' := by
    intro p hp
    have hh := hcore hp
    exact ⟨hh.1.trans (by linarith), hh.2.1.trans (by linarith), hh.2.2.trans (by linarith)⟩
  have hd := axial_frame_direction_bounds e e' hθ hθ1 hc hthin hv hvu hshort hcoord hu1
  have hnew0 : K * c * |e' v 0| ≤ (128 * K * a) / 16 := by
    have hh := (le_div_iff₀ hc).mp hd.2.1
    have hh' := mul_le_mul_of_nonneg_left hh hK0.le
    nlinarith
  have hnew1 : K * c * |e' v 1| ≤ (θ * (K * c)) / 16 := by
    have hh := mul_le_mul_of_nonneg_left hd.2.2 hKc.le
    nlinarith
  have hcross := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.prism_crossing_of_core_point
    e' hδ (by nlinarith : 16 * δ ≤ 128 * K * a)
    (by nlinarith : 16 * δ ≤ θ * (K * c)) (by nlinarith : 16 * δ ≤ K * c)
    hd.1 hnew0 hnew1
    (q := q) ⟨⟨hq.1, not_mem_tubeEnds_of_clearance
      (by nlinarith : δ ≤ K * c) hv (by linarith) (by linarith)⟩, hcore hq.2⟩
  have hqz : ‖q - z‖ ≤ c := frozen_prism_norm ha.le hab hbc z e hq.2
  have hnear (p : V) (hp : p ∈ P (128 * K * a) (θ * (K * c)) (K * c) z e') :
      dist p q ≤ 2 * (K * c) := by
    have hpz := frozen_prism_norm (by positivity : 0 ≤ 128 * K * a) hnewab hnewbc z e' hp
    calc
      _ ≤ dist p z + dist z q := dist_triangle _ _ _
      _ ≤ K * c + c := by
        rw [dist_eq_norm, dist_comm z q, dist_eq_norm]
        exact add_le_add hpz hqz
      _ ≤ _ := by nlinarith
  refine ⟨hsub, hcross.1, hcross.2, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨r, hr, hqr⟩ := mem_thickening_iff.mp (hcontain hq.1)
    refine mem_thickening_iff.mpr ⟨r, hr, ?_⟩
    have hh := hnear p hp
    have htri := dist_triangle p q r
    linarith
  · have hdiff : |e' u 0 - e' v 0| ≤ θ / 100 := by
      have hh := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.abs_rotated_coord_le e' (u - v) 0
      rw [map_sub, PiLp.sub_apply] at hh
      exact hh.trans (by simpa only [norm_sub_rev] using hvu)
    have h0 : |e' u 0| ≤ θ := by
      have hh := abs_add_le (e' u 0 - e' v 0) (e' v 0)
      rw [sub_add_cancel] at hh
      have ha' := (le_div_iff₀ hc).mp hd.2.1
      have hbound : 6 * a / c ≤ θ / 8 := by apply (div_le_iff₀ hc).mpr; nlinarith
      linarith
    rw [hu1, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    have hh := (sq_le_sq₀ (abs_nonneg (e' u 0)) hθ.le).mpr h0
    rw [sq_abs] at hh
    nlinarith [sq_nonneg θ]
  · intro p hp
    have hh : dist q p ≤ 2 * (K * c) := by rw [dist_comm]; exact hnear p hp
    constructor
    · linarith [dist_triangle q p x]
    · linarith [dist_triangle q p (x + v)]

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
