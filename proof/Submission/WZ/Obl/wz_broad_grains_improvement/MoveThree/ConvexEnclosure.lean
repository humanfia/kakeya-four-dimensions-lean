-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ConvexEnclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ConvexEnclosure.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0708 commit 170d089, ConvexEnclosure.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorBox
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseNormalize
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.Box

/-!
# Physical enclosures for inverse images of filled prisms

An affine inverse image of an orthogonal prism need not be orthogonal. We use
the accepted convex box approximation to replace it by an actual frozen prism,
with explicit volume and length losses. No coarse cover is constructed here.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap uniformMap_apply uniformMap_volume)

/-- A similarity takes the full neighbourhood of a segment to the corresponding
neighbourhood of the image segment. -/
theorem similarity_image_tube (f : V ≃ᵃ[ℝ] V) {s : ℝ} (hs : 0 < s)
    (hdist : ∀ p q, dist (f p) (f q) = s * dist p q) (δ : ℝ) (x v : V) :
    f '' T δ x v = T (s*δ) (f x) (f.linear v) := by
  have hxv : f (x+v) = f x + f.linear v := by
    simpa only [vadd_eq_add, add_comm] using f.map_vadd x v
  have hseg : f '' segment ℝ x (x+v) = segment ℝ (f x) (f x + f.linear v) := by
    have hh := image_segment ℝ f.toAffineMap x (x+v)
    change f '' segment ℝ x (x+v) = segment ℝ (f x) (f (x+v)) at hh
    rwa [hxv] at hh
  ext p
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
    apply mem_thickening_iff.mpr
    refine ⟨f q, hseg ▸ mem_image_of_mem f hq, ?_⟩
    rw [hdist]
    exact mul_lt_mul_of_pos_left hpq hs
  · intro hp
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
    rw [← hseg] at hq
    obtain ⟨q, hq, rfl⟩ := hq
    refine ⟨f.symm p, mem_thickening_iff.mpr ⟨q, hq, ?_⟩, f.apply_symm_apply p⟩
    have hh := hdist (f.symm p) q
    rw [f.apply_symm_apply] at hh
    rw [hh] at hpq
    exact (mul_lt_mul_iff_right₀ hs).mp hpq

/-- A convex body containing a segment-neighbourhood of length `ell` has a
comparable-volume rectangular enclosure whose long side is `4 R ell`. -/
theorem convex_short_tube_enclosure {δ ell R : ℝ} {W : Set V} {x v z₀ : V}
    (hδ : 0 < δ) (hell : 0 < ell) (hR : 0 < R)
    (hv : ‖v‖ = ell) (hW : Convex ℝ W)
    (hball : W ⊆ ball z₀ (R*ell)) (hT : T δ x v ⊆ W) :
    ∃ (a b : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V),
      δ ≤ a ∧ a ≤ b ∧ b ≤ 4*R*ell ∧ W ⊆ P a b (4*R*ell) z e ∧
      μ (P a b (4*R*ell) z e) ≤ O (1728*R) * μ W := by
  let f : V ≃ᵃ[ℝ] V := (AffineEquiv.constVAdd ℝ V (-z₀)).trans
    (uniformMap (inv_pos.mpr hell)).toAffineEquiv
  have hf (p : V) : f p = ell⁻¹ • (p-z₀) := by
    change ell⁻¹ • (-z₀+p) = ell⁻¹ • (p-z₀)
    congr 1
    abel
  have hd (p q : V) : dist (f p) (f q) = ell⁻¹ * dist p q := by
    rw [hf, hf, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hell), dist_sub_right]
  have hunit : ‖f.linear v‖ = 1 := by
    change ‖ell⁻¹ • v‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hell), hv, inv_mul_cancel₀ hell.ne']
  have hfnorm : f '' W ⊆ ball (0 : V) R := by
    rintro _ ⟨p, hp, rfl⟩
    have hp' := hball hp
    rw [mem_ball, dist_eq_norm] at hp'
    rw [mem_ball, dist_zero_right, hf, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hell)]
    calc
      _ < ell⁻¹ * (R*ell) := mul_lt_mul_of_pos_left hp' (inv_pos.mpr hell)
      _ = R := by field_simp
  have hftube : T (ell⁻¹*δ) (f x) (f.linear v) ⊆ f '' W := by
    rw [← similarity_image_tube f (inv_pos.mpr hell) hd]
    exact image_mono hT
  have hvol : μ (f '' W) = O (ell⁻¹ ^ 3) * μ W := by
    have he : f '' W = uniformMap (inv_pos.mpr hell) '' ((fun p : V => p + (-z₀)) '' W) := by
      rw [← image_comp]
      apply image_congr
      intro p _
      simp only [Function.comp_apply, uniformMap_apply, hf, sub_eq_add_neg]
    rw [he]
    change volume (uniformMap (inv_pos.mpr hell) '' ((fun p : V => p + (-z₀)) '' W)) = _
    rw [uniformMap_volume, image_add_right, measure_preimage_add_right]
  obtain ⟨a, b, z, e, hda, hab, hbR, hbox, harea⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.box_approx
      (mul_pos (inv_pos.mpr hell) hδ) hunit
      (Convex.affine_image f.toAffineMap hW) hfnorm hftube
  change O (a*b) ≤ 432 * μ (f '' W) at harea
  have ha : 0 < a := (mul_pos (inv_pos.mpr hell) hδ).trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hcontain : W ⊆ P (ell*a) (ell*b) (4*R*ell) (z₀ + ell • z) e := by
    intro p hp
    have hh := hbox (mem_image_of_mem f hp)
    have he : e (p-(z₀+ell • z)) = ell • e (f p-z) := by
      rw [← map_smul, hf, smul_sub, smul_smul, mul_inv_cancel₀ hell.ne', one_smul]
      congr 1
      abel
    change |e (p-(z₀+ell • z)) 0| ≤ (ell*a)/2 ∧
      |e (p-(z₀+ell • z)) 1| ≤ (ell*b)/2 ∧
      |e (p-(z₀+ell • z)) 2| ≤ (4*R*ell)/2
    rw [he]
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hell]
    exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hh.1 hell.le],
      by nlinarith [mul_le_mul_of_nonneg_left hh.2.1 hell.le],
      by nlinarith [mul_le_mul_of_nonneg_left hh.2.2 hell.le]⟩
  refine ⟨ell*a, ell*b, z₀+ell • z, e, ?_, ?_, ?_, hcontain, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hda hell.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hell.ne', one_mul] using hh
  · exact mul_le_mul_of_nonneg_left hab hell.le
  · nlinarith [mul_le_mul_of_nonneg_left hbR hell.le]
  · have hpvol : μ (P (ell*a) (ell*b) (4*R*ell) (z₀+ell • z) e) =
        O ((ell*a)*(ell*b)*(4*R*ell)) :=
      WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P
        (mul_pos hell ha).le (mul_pos hell hb).le (by positivity) _ _
    rw [hpvol]
    calc
      O ((ell*a)*(ell*b)*(4*R*ell)) = O (4*R*ell^3) * O (a*b) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*R*ell^3)]
        congr 1
        ring
      _ ≤ O (4*R*ell^3) * (432 * μ (f '' W)) := mul_le_mul' le_rfl harea
      _ = O (1728*R) * μ W := by
        rw [hvol]
        have he : O (4*R*ell^3) * (432 : ENNReal) * O (ell⁻¹ ^ 3) = O (1728*R) := by
          have h432 : (432 : ENNReal) = O (432 : ℝ) := by norm_num [O]
          rw [h432, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*R*ell^3),
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*R*ell^3*432)]
          congr 1
          field_simp
          ring
        simpa only [← mul_assoc] using congrArg (fun t : ENNReal => t * μ W) he

/-- The middle half of the long axis has a round neighbourhood inside a prism. -/
theorem prism_contains_short_tube {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    T (a/4) (z-(c/4) • boxAxis e 2) ((c/2) • boxAxis e 2) ⊆ P a b c z e := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hcoordq : ∀ i : Fin 3, |e (q-z) i| ≤ if i=2 then c/4 else 0 := by
    rw [segment_eq_image'] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    have he : e ((z-(c/4) • boxAxis e 2 +
        t • (z-(c/4) • boxAxis e 2 + (c/2) • boxAxis e 2 -
          (z-(c/4) • boxAxis e 2)))-z) =
        (t*(c/2)-c/4) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
      rw [show (z-(c/4) • boxAxis e 2 +
        t • (z-(c/4) • boxAxis e 2 + (c/2) • boxAxis e 2 -
          (z-(c/4) • boxAxis e 2)))-z =
        (t*(c/2)-c/4) • boxAxis e 2 by module, map_smul]
      simp only [boxAxis, e.apply_symm_apply]
    intro i
    rw [he]
    fin_cases i <;> norm_num [EuclideanSpace.basisFun_apply]
    rw [abs_le]
    constructor <;> nlinarith [ht.1, ht.2, ha.trans_le (hab.trans hbc)]
  have hcoordp (i : Fin 3) : |e (p-z) i| ≤ a/4 + (if i=2 then c/4 else 0) := by
    have hnorm : |e (p-q) i| < a/4 := by
      have hh := PiLp.norm_apply_le (e (p-q)) i
      rw [Real.norm_eq_abs, e.norm_map] at hh
      exact hh.trans_lt hpq
    have he : e (p-z) = e (p-q) + e (q-z) := by rw [← map_add]; congr 1; abel
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hnorm.le (hcoordq i))
  have h0 := hcoordp 0
  have h1 := hcoordp 1
  have h2 := hcoordp 2
  norm_num only [Fin.reduceEq, ite_true, ite_false, add_zero] at h0 h1 h2
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Inclusion of an entire prism prevents any side of its rectangular enclosure
from being shorter than the original smallest side. -/
theorem prism_short_le_of_subset {a b c A B C : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hac : a ≤ c) (z z' : V) (e e' : V ≃ₗᵢ[ℝ] V)
    (hsub : P a b c z e ⊆ P A B C z' e') : a ≤ A := by
  have hball {p : V} (hp : ‖p-z‖ ≤ a/2) : p ∈ P a b c z e := by
    have hcoord (i : Fin 3) : |e (p-z) i| ≤ a/2 := by
      have hh := PiLp.norm_apply_le (e (p-z)) i
      rw [Real.norm_eq_abs, e.norm_map] at hh
      exact hh.trans hp
    exact ⟨hcoord 0, (hcoord 1).trans (by linarith), (hcoord 2).trans (by linarith)⟩
  let u := boxAxis e' 0
  have hu : ‖u‖ = 1 := boxAxis_norm e' 0
  have hp : z+(a/2) • u ∈ P a b c z e := hball (by
    rw [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ a/2)])
  have hm : z-(a/2) • u ∈ P a b c z e := hball (by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ a/2)])
  have hdiff : e' (z+(a/2) • u-z') 0 - e' (z-(a/2) • u-z') 0 = a := by
    change (e' (z+(a/2) • u-z') - e' (z-(a/2) • u-z')) 0 = a
    rw [← map_sub, show (z+(a/2) • u-z')-(z-(a/2) • u-z')=a • u by module, map_smul]
    simp [u, boxAxis, EuclideanSpace.basisFun_apply]
  have hh := abs_sub (e' (z+(a/2) • u-z') 0) (e' (z-(a/2) • u-z') 0)
  rw [hdiff, abs_of_nonneg ha] at hh
  linarith [(hsub hp).1, (hsub hm).1]

/-- A physical convex body containing one whole old grain admits a rectangular
enclosure of controlled volume and a fixed multiple of the old length. -/
theorem convex_grain_enclosure {a b c R : ℝ} {W : Set V} {z z₀ : V}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hR : 0 < R)
    (e : V ≃ₗᵢ[ℝ] V) (hW : Convex ℝ W)
    (hball : W ⊆ ball z₀ (R*c)) (hP : P a b c z e ⊆ W) :
    ∃ (A B : ℝ) (z' : V) (e' : V ≃ₗᵢ[ℝ] V),
      a ≤ A ∧ A ≤ B ∧ B ≤ 4*R*c ∧ W ⊆ P A B (4*R*c) z' e' ∧
      μ (P A B (4*R*c) z' e') ≤ O (3456*R) * μ W := by
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  obtain ⟨A, B, z', e', _, hAB, hBc, hbox, hvol⟩ := convex_short_tube_enclosure
    (by positivity : 0 < a/4) (by positivity : 0 < c/2) (by positivity : 0 < 2*R)
    (x := z-(c/4) • boxAxis e 2) (v := (c/2) • boxAxis e 2)
    (by rw [norm_smul, boxAxis_norm, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]) hW
    (by simpa only [show (2*R)*(c/2) = R*c by ring] using hball)
    ((prism_contains_short_tube ha hab hbc z e).trans hP)
  have heq : 4*(2*R)*(c/2) = 4*R*c := by ring
  rw [heq] at hBc hbox hvol
  refine ⟨A, B, z', e', prism_short_le_of_subset ha.le hab (hab.trans hbc)
    z z' e e' (hP.trans hbox), hAB, hBc, hbox, ?_⟩
  simpa only [show 1728*(2*R) = 3456*R by ring] using hvol

/-- Undoing an affine normalization and then enclosing its image costs only a
fixed volume factor when the inverse map has a controlled Lipschitz constant. -/
theorem inverse_prism_enclosure {a b c A₀ B₀ C₀ K : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hA₀ : 0 ≤ A₀) (hAB₀ : A₀ ≤ B₀) (hBC₀ : B₀ ≤ C₀) (hC₀ : 0 < C₀) (hK : 0 < K)
    (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hInv : ∀ p q, dist (f.symm p) (f.symm q) ≤ (K*c)*dist p q)
    (hwhole : f '' P a b c z e ⊆ P A₀ B₀ C₀ z₀ e₀) :
    ∃ (A B : ℝ) (z' : V) (e' : V ≃ₗᵢ[ℝ] V),
      a ≤ A ∧ A ≤ B ∧ B ≤ 8*K*C₀*c ∧
      f.symm '' P A₀ B₀ C₀ z₀ e₀ ⊆ P A B (8*K*C₀*c) z' e' ∧
      μ (P A B (8*K*C₀*c) z' e') ≤ O (6912*K*C₀) * μ (f.symm '' P A₀ B₀ C₀ z₀ e₀) := by
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  have hnorm (p : V) (hp : p ∈ P A₀ B₀ C₀ z₀ e₀) : dist p z₀ ≤ C₀ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_norm hA₀ hAB₀ hBC₀ z₀ e₀ hp
  have hball : f.symm '' P A₀ B₀ C₀ z₀ e₀ ⊆ ball (f.symm z₀) ((2*K*C₀)*c) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_ball]
    calc
      _ ≤ (K*c)*dist p z₀ := hInv p z₀
      _ ≤ (K*c)*C₀ := mul_le_mul_of_nonneg_left (hnorm p hp) (mul_pos hK hc).le
      _ < (2*K*C₀)*c := by nlinarith [mul_pos (mul_pos hK hc) hC₀]
  have hP : P a b c z e ⊆ f.symm '' P A₀ B₀ C₀ z₀ e₀ := by
    intro p hp
    exact ⟨f p, hwhole (mem_image_of_mem f hp), f.symm_apply_apply p⟩
  have hconvex : Convex ℝ (f.symm '' P A₀ B₀ C₀ z₀ e₀) :=
    Convex.affine_image f.symm.toAffineMap
      (WangZahlLot.Obl.wz_move_three_thick_grains_gain.convex_P _ _ _ _ _)
  obtain ⟨A, B, z', e', haA, hAB, hB, hbox, hvol⟩ :=
    convex_grain_enclosure ha hab hbc (by positivity : 0 < 2*K*C₀) e hconvex hball hP
  rw [show 4*(2*K*C₀)*c = 8*K*C₀*c by ring] at hB hbox hvol
  rw [show 3456*(2*K*C₀) = 6912*K*C₀ by ring] at hvol
  exact ⟨A, B, z', e', haA, hAB, hB, hbox, hvol⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
