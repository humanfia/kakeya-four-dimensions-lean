-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AlignmentAnisotropic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentRadialCover
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AnisotropicGain

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

theorem alignment_anisotropic_gain {δ ε η κ w t h c : ℝ} {e b : Plane}
    {F G : Finset Plane} (T : G → Finset Plane) {Q : Set Triple}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 ≤ η) (hηε : η ≤ ε / 2)
    (hδw : δ ≤ w) (hh : 0 < h) (hh1 : h ≤ 1) (ht : 0 < t) (hth : t ≤ h)
    (hwt : w ≤ t / 2) (hwh : 2 * w / h ≤ 1) (hratio : δ ^ (-ε / 2) ≤ h / w)
    (hht : h / t ≤ δ ^ (-κ)) (he : ‖e‖ = 1)
    (hF : ClosedFiniteFrostman δ (δ ^ (-η)) F) (hG : ClosedFiniteFrostman δ (δ ^ (-η)) G)
    (hFnorm : ∀ a ∈ F, ‖a‖ ≤ 4) (hFstrip : ∀ a ∈ F, |inner ℝ a e| ≤ h)
    (hstrip : ∀ x ∈ G, |inner ℝ x (perp e) - c| ≤ w)
    (hpin : |inner ℝ b (perp e) - c| = t)
    (hsep : ∀ x ∈ G, 1 / 2 ≤ ‖b - x‖) (hfar : ∀ x ∈ G, ‖b - x‖ ≤ 8)
    (hT : ∀ x, T x ⊆ F) (hne : ∃ x, (T x).Nonempty)
    (hdensity : δ ^ η * (G.card : ℝ) * (F.card : ℝ) ≤ ∑ x, ((T x).card : ℝ))
    (hQ : ∀ x, ∀ a ∈ T x, (a, (x : Plane), b) ∈ Q) : ProjectionGain δ η ε Q := by
  have hw : 0 < w := hδ.trans_le hδw
  have hC : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hb.scale_le_one (by linarith)
  obtain ⟨x, hx⟩ := anisotropic_radial_gain F G T hδ hδw hh hh1 ht hth hwt hwh
    hC (by positivity : 0 < δ ^ η) (by linarith : 0 ≤ 1 - ε / 2) (by linarith : 1 - ε / 2 < 1)
    he hF hG hstrip hpin hsep hfar hT hne hdensity
  have hKbound : 8192 * δ ^ (-η) * h / t ≤ 8192 * δ ^ (-η - κ) := by
    calc 8192 * δ ^ (-η) * h / t = 8192 * δ ^ (-η) * (h / t) := by ring
      _ ≤ 8192 * δ ^ (-η) * δ ^ (-κ) := mul_le_mul_of_nonneg_left hht (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hδ]; congr 1
  have hcover := hb.radial_cover_lower hδ hε hε1 hh hw
    (by positivity : 0 < 8192 * δ ^ (-η) * h / t) hratio hKbound hx
  apply projectionGain_of_bounded_negative hδw (hb.gain_length hδ hw hηε hratio) hcover
    (by convert le_rfl using 1 <;> congr 1 <;> ring)
  · rintro s ⟨a, ha, rfl⟩
    refine ⟨(a, (x : Plane), b), hQ x a ha, ?_⟩
    change -inner ℝ a (b - x) = inner ℝ a ((x : Plane) - b)
    rw [show (x : Plane) - b = -(b - x) by abel, inner_neg_right]
  · rintro s ⟨a, ha, rfl⟩
    have haf : a ∈ F := hT x ha
    have hnorma := anisotropic_orthogonal_norm he hh (hFstrip a haf) (hFnorm a haf)
    have hnormbx := anisotropic_difference_norm he hh hth
      ((hstrip x x.property).trans (by linarith)) hpin.le (hfar x x.property)
    change |inner ℝ a (b - x)| ≤ 80 * h
    rw [anisotropicMap_dual_dot he hh a b x, abs_mul, abs_of_pos hh]
    have hi := abs_real_inner_le_norm (anisotropicMap e h⁻¹ 1 a)
      (anisotropicMap e 1 h⁻¹ b - anisotropicMap e 1 h⁻¹ x)
    have hprod : ‖anisotropicMap e h⁻¹ 1 a‖ *
        ‖anisotropicMap e 1 h⁻¹ b - anisotropicMap e 1 h⁻¹ x‖ ≤ 5 * 10 :=
      mul_le_mul hnorma hnormbx (norm_nonneg _) (by norm_num)
    exact (mul_le_mul_of_nonneg_left (hi.trans hprod) hh.le).trans (by nlinarith)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
