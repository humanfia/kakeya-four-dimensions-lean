-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NaturalTubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NaturalTubes.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from the internal o169/x0551 NaturalTubes (0190d24, 6d9b949, d4e092b). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Tubes

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis boxAxis_norm norm_le_coord_sum)

/-- The two tangential axes of a plate in a doubled plate have controlled
components along the containing plate's normal. -/
theorem near_plate_tangent {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V)
    (hnear : P a c c z e ⊆ P (2 * a) (2 * c) (2 * c) z₀ e₀)
    (j : Fin 3) (hj : j ≠ 0) :
    |e₀ (boxAxis e j) 0| ≤ 2 * a / c := by
  have hmem (t : ℝ) (ht : |t| ≤ c / 2) : z + t • boxAxis e j ∈ P a c c z e := by
    have he : e (t • boxAxis e j) = t • EuclideanSpace.basisFun (Fin 3) ℝ j := by
      simp [boxAxis]
    change |e (z + t • boxAxis e j - z) 0| ≤ a / 2 ∧
      |e (z + t • boxAxis e j - z) 1| ≤ c / 2 ∧
      |e (z + t • boxAxis e j - z) 2| ≤ c / 2
    rw [add_sub_cancel_left, he]
    fin_cases j <;> simp_all [EuclideanSpace.basisFun_apply, EuclideanSpace.single]
      <;> constructor <;> positivity
  have hp := (hnear (hmem (c / 2) (by rw [abs_of_pos (by positivity)]))).1
  have hm := (hnear (hmem (-c / 2) (by rw [neg_div, abs_neg, abs_of_pos (by positivity)]))).1
  have hdiff : e₀ (z + (c / 2) • boxAxis e j - z₀) 0 -
      e₀ (z + (-c / 2) • boxAxis e j - z₀) 0 = c * e₀ (boxAxis e j) 0 := by
    have he : (z + (c / 2) • boxAxis e j - z₀) -
        (z + (-c / 2) • boxAxis e j - z₀) = c • boxAxis e j := by module
    rw [← PiLp.sub_apply, ← map_sub, he, map_smul]
    rfl
  have hh := abs_sub (e₀ (z + (c / 2) • boxAxis e j - z₀) 0)
    (e₀ (z + (-c / 2) • boxAxis e j - z₀) 0)
  rw [hdiff, abs_mul, abs_of_pos hc] at hh
  rw [le_div_iff₀ hc]
  nlinarith

/-- Transverse bounds on an affine image of a prism give a tube around the
image of its central long segment. -/
theorem affine_prism_tube {a b c ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hρ : 0 < ρ)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (h0 : a * ‖f.linear (boxAxis e 0)‖ ≤ ρ)
    (h1 : b * ‖f.linear (boxAxis e 1)‖ ≤ ρ) :
    f '' P a b c z e ⊆ T (2 * ρ)
      (f z - (c / 2) • f.linear (boxAxis e 2)) (c • f.linear (boxAxis e 2)) := by
  rintro _ ⟨p, hp, rfl⟩
  let t : Fin 3 → ℝ := fun i => e (p - z) i
  have hexpand : p - z = t 0 • boxAxis e 0 + t 1 • boxAxis e 1 + t 2 • boxAxis e 2 := by
    apply e.injective
    simp only [map_add, map_smul, boxAxis, e.apply_symm_apply]
    ext i
    fin_cases i <;> simp [t, EuclideanSpace.basisFun_apply]
  let q := f z + t 2 • f.linear (boxAxis e 2)
  have hq : q ∈ segment ℝ (f z - (c / 2) • f.linear (boxAxis e 2))
      (f z - (c / 2) • f.linear (boxAxis e 2) + c • f.linear (boxAxis e 2)) := by
    rw [segment_eq_image']
    refine ⟨t 2 / c + 1 / 2, ⟨?_, ?_⟩, ?_⟩
    · have hh := (abs_le.mp hp.2.2).1
      change -(c / 2) ≤ t 2 at hh
      have hh' : -(1 / 2 : ℝ) ≤ t 2 / c :=
        (le_div_iff₀ hc).mpr (by linarith)
      linarith
    · have hh := (abs_le.mp hp.2.2).2
      change t 2 ≤ c / 2 at hh
      have hh' : t 2 / c ≤ (1 / 2 : ℝ) :=
        (div_le_iff₀ hc).mpr (by linarith)
      linarith
    · dsimp [q]
      have ht : (t 2 / c + 1 / 2) * c = t 2 + c / 2 := by field_simp
      simp only [add_sub_cancel_left, smul_smul]
      rw [ht]
      module
  have hdiff : f p - q = t 0 • f.linear (boxAxis e 0) + t 1 • f.linear (boxAxis e 1) := by
    have hmap : f p = f z + f.linear (p - z) := by
      have H := f.map_vadd z (p - z)
      simp only [vadd_eq_add, sub_add_cancel] at H
      simpa only [add_comm] using H
    rw [hmap, hexpand, f.linear.map_add, f.linear.map_add, f.linear.map_smul,
      f.linear.map_smul, f.linear.map_smul]
    dsimp [q]
    abel
  apply mem_thickening_iff.mpr
  refine ⟨q, hq, ?_⟩
  rw [dist_eq_norm, hdiff]
  have ht0 : |t 0| ≤ a / 2 := hp.1
  have ht1 : |t 1| ≤ b / 2 := hp.2.1
  calc
    _ ≤ ‖t 0 • f.linear (boxAxis e 0)‖ + ‖t 1 • f.linear (boxAxis e 1)‖ := norm_add_le _ _
    _ = |t 0| * ‖f.linear (boxAxis e 0)‖ + |t 1| * ‖f.linear (boxAxis e 1)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ρ := by
      have H0 := mul_le_mul_of_nonneg_right ht0 (norm_nonneg (f.linear (boxAxis e 0)))
      have H1 := mul_le_mul_of_nonneg_right ht1 (norm_nonneg (f.linear (boxAxis e 1)))
      nlinarith
    _ < _ := by linarith

/-- The natural plate normalization puts every neighboring grain in a round
tube. Its central segment has length between one quarter and one. -/
theorem natural_grain_linear_bounds {a ρ c : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c)
    (hac : a ≤ ρ * c) (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hnear : P (a / ρ) c c z e ⊆ P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀)
    (hcoord : ∀ p i, f p i = (![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i *
      e₀ (p - z₀) i) :
    a * ‖f.linear (boxAxis e 0)‖ ≤ ρ ∧
      ‖f.linear (boxAxis e 1)‖ ≤ c⁻¹ ∧ ‖f.linear (boxAxis e 2)‖ ≤ c⁻¹ := by
  let A := f.linear
  have hA (v : V) (i : Fin 3) : A v i =
      (![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i * e₀ v i := by
    have hi := congrArg (fun p : V => p i) (f.map_vadd z₀ v)
    change f (v + z₀) i = A v i + f z₀ i at hi
    rw [hcoord, hcoord] at hi
    simpa only [add_sub_cancel_right, sub_self, map_zero, WithLp.ofLp_zero,
      Pi.zero_apply, mul_zero, add_zero] using hi.symm
  have hunit (j i : Fin 3) : |e₀ (boxAxis e j) i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, e₀.norm_map, boxAxis_norm] using
      PiLp.norm_apply_le (e₀ (boxAxis e j)) i
  have hnormal (j : Fin 3) (hj : j ≠ 0) : |e₀ (boxAxis e j) 0| ≤ 2 * (a / ρ) / c :=
    near_plate_tangent (div_pos ha hρ) hc z z₀ e e₀ (by simpa only [mul_div_assoc] using hnear) j hj
  have hcoord0 (j : Fin 3) : |A (boxAxis e j) 0| ≤ ρ / (4 * a) := by
    rw [hA]
    change |ρ / (4 * a) * e₀ (boxAxis e j) 0| ≤ _
    rw [abs_mul, abs_of_pos (by positivity : 0 < ρ / (4 * a))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hunit j 0) (by positivity : 0 ≤ ρ / (4 * a))
  have hcoords (j i : Fin 3) (hi : i ≠ 0) : |A (boxAxis e j) i| ≤ (4 * c)⁻¹ := by
    rw [hA]
    have he : (![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i = (4 * c)⁻¹ := by
      fin_cases i <;> simp_all
    rw [he, abs_mul, abs_of_pos (by positivity : 0 < (4 * c)⁻¹)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hunit j i) (by positivity : 0 ≤ (4 * c)⁻¹)
  have htangent (j : Fin 3) (hj : j ≠ 0) : ‖A (boxAxis e j)‖ ≤ c⁻¹ := by
    have h0 : |A (boxAxis e j) 0| ≤ 1 / (2 * c) := by
      rw [hA]
      change |ρ / (4 * a) * e₀ (boxAxis e j) 0| ≤ _
      rw [abs_mul, abs_of_pos (by positivity : 0 < ρ / (4 * a))]
      calc
        _ ≤ (ρ / (4 * a)) * (2 * (a / ρ) / c) :=
          mul_le_mul_of_nonneg_left (hnormal j hj) (by positivity)
        _ = _ := by field_simp; ring
    have hsum := norm_le_coord_sum (A (boxAxis e j))
    have he : 1 / (2 * c) + (4 * c)⁻¹ + (4 * c)⁻¹ = c⁻¹ := by field_simp; ring
    rw [← he]
    linarith [hcoords j 1 (by decide), hcoords j 2 (by decide)]
  have hnorm0 : a * ‖A (boxAxis e 0)‖ ≤ ρ := by
    have hh := norm_le_coord_sum (A (boxAxis e 0))
    have h := mul_le_mul_of_nonneg_left
      (show ‖A (boxAxis e 0)‖ ≤ ρ / (4 * a) + (4 * c)⁻¹ + (4 * c)⁻¹ by
        linarith [hcoord0 0, hcoords 0 1 (by decide), hcoords 0 2 (by decide)]) ha.le
    have hratio : a / c ≤ ρ := (div_le_iff₀ hc).mpr hac
    have he : a * (ρ / (4 * a) + (4 * c)⁻¹ + (4 * c)⁻¹) = ρ / 4 + (a / c) / 2 := by
      field_simp
      ring
    rw [he] at h
    linarith
  exact ⟨hnorm0, htangent 1 (by decide), htangent 2 (by decide)⟩

/-- The natural normalization gives a round carrier whose endpoints belong
to the transformed grain. -/
theorem natural_grain_tube_data {a ρ c : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c)
    (hac : a ≤ ρ * c) (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hnear : P (a / ρ) c c z e ⊆ P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀)
    (hcoord : ∀ p i, f p i = (![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i *
      e₀ (p - z₀) i)
    (hdist : ∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) :
    ∃ x v : V, (1 / 4 : ℝ) ≤ ‖v‖ ∧ ‖v‖ ≤ 1 ∧
      f '' P a (ρ * c) c z e ⊆ T (2 * ρ) x v ∧
      x ∈ f '' P a (ρ * c) c z e ∧ x + v ∈ f '' P a (ρ * c) c z e := by
  let A := f.linear
  obtain ⟨hnorm0, htan1, htan2⟩ := natural_grain_linear_bounds ha hρ hc hac z z₀ e e₀ f hnear hcoord
  have hnorm1 : (ρ * c) * ‖A (boxAxis e 1)‖ ≤ ρ := by
    have h := mul_le_mul_of_nonneg_left htan1 (mul_pos hρ hc).le
    simpa only [mul_assoc, mul_inv_cancel₀ hc.ne', mul_one] using h
  have hvle : ‖c • A (boxAxis e 2)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have h := mul_le_mul_of_nonneg_left htan2 hc.le
    simpa only [mul_inv_cancel₀ hc.ne'] using h
  have hvge : (1 / 4 : ℝ) ≤ ‖c • A (boxAxis e 2)‖ := by
    have h := hdist (z + c • boxAxis e 2) z
    have he : f (z + c • boxAxis e 2) - f z = c • A (boxAxis e 2) := by
      have hh := f.map_vadd z (c • boxAxis e 2)
      simpa only [vadd_eq_add, add_comm, map_smul, sub_eq_iff_eq_add] using hh
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc, boxAxis_norm, mul_one, dist_eq_norm, he] at h
    convert h using 1 <;> field_simp
  refine ⟨f z - (c / 2) • A (boxAxis e 2), c • A (boxAxis e 2), hvge, hvle,
    affine_prism_tube ha.le (mul_pos hρ hc).le hc hρ z e f hnorm0 hnorm1, ?_, ?_⟩
  · refine ⟨z - (c / 2) • boxAxis e 2,
      (WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_ends
        ha.le (mul_pos hρ hc).le hc.le z e).2, ?_⟩
    have hh := f.map_vadd z (-((c / 2) • boxAxis e 2))
    simpa only [vadd_eq_add, add_comm, sub_eq_add_neg, map_neg, map_smul] using hh
  · refine ⟨z + (c / 2) • boxAxis e 2,
      (WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_ends
        ha.le (mul_pos hρ hc).le hc.le z e).1, ?_⟩
    have hh := f.map_vadd z ((c / 2) • boxAxis e 2)
    simp only [vadd_eq_add, map_smul] at hh
    rw [add_comm z, hh]
    change (c / 2) • A (boxAxis e 2) + f z = _
    module

/-- A normalized grain lies in a short round tube. -/
theorem natural_grain_tube {a ρ c : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c)
    (hac : a ≤ ρ * c) (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hnear : P (a / ρ) c c z e ⊆ P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀)
    (hcoord : ∀ p i, f p i = (![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i *
      e₀ (p - z₀) i)
    (hdist : ∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) :
    ∃ x v : V, (1 / 4 : ℝ) ≤ ‖v‖ ∧ ‖v‖ ≤ 1 ∧
      f '' P a (ρ * c) c z e ⊆ T (2 * ρ) x v := by
  obtain ⟨x, v, hvlo, hvhi, hsub, _⟩ :=
    natural_grain_tube_data ha hρ hc hac z z₀ e e₀ f hnear hcoord hdist
  exact ⟨x, v, hvlo, hvhi, hsub⟩

/-- The short carriers of normalized grains can be extended to unit tubes
without changing their radius. -/
theorem natural_grain_unit_tube {a ρ c : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c)
    (hac : a ≤ ρ * c) (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hnear : P (a / ρ) c c z e ⊆ P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀)
    (hcoord : ∀ p i, f p i = (![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i *
      e₀ (p - z₀) i)
    (hdist : ∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) :
    ∃ x v : V, ‖v‖ = 1 ∧ f '' P a (ρ * c) c z e ⊆ T (2 * ρ) x v := by
  obtain ⟨x, v, hvlo, hvhi, hsub⟩ := natural_grain_tube ha hρ hc hac z z₀ e e₀ f hnear hcoord hdist
  have hv : v ≠ 0 := by intro hz; rw [hz, norm_zero] at hvlo; norm_num at hvlo
  let u := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit v
  have hu : ‖u‖ = 1 := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_unit hv
  refine ⟨x + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • u, u, hu, hsub.trans ?_⟩
  have hh := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.image_tube_extend
    (AffineEquiv.refl ℝ V).toContinuousAffineEquiv x v u (δ := 2 * ρ)
    (by norm_num : (0 : ℝ) < 1) (norm_nonneg v) hvhi
    (WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_smul_unit hv).symm
    (fun p q => by simp)
  simpa only [AffineEquiv.coe_toContinuousAffineEquiv, AffineEquiv.coe_refl,
    Set.image_id, one_mul, id_eq, T, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.tube] using hh

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
