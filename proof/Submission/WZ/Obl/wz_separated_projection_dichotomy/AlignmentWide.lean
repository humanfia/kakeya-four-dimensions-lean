-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AlignmentWide.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentRadialCover
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripRadialGain

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

theorem alignment_wide_gain {δ ε η κ w t c : ℝ} {n b : Plane}
    {F G : Finset Plane} (T : G → Finset Plane) {Q : Set Triple}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 ≤ η) (hηε : η ≤ ε / 2)
    (hδw : δ ≤ w) (hw1 : 2 * w ≤ 1) (ht : 0 < t) (ht16 : t ≤ 16)
    (hwt : w ≤ t / 2) (hratio : δ ^ (-ε / 2) ≤ 1 / w) (htt : 1 / t ≤ δ ^ (-κ))
    (hn : ‖n‖ = 1)
    (hF : ClosedFiniteFrostman δ (δ ^ (-η)) F) (hG : ClosedFiniteFrostman δ (δ ^ (-η)) G)
    (hFnorm : ∀ a ∈ F, ‖a‖ ≤ 4)
    (hstrip : ∀ x ∈ G, |inner ℝ x n - c| ≤ w) (hpin : t ≤ |inner ℝ b n - c|)
    (hsep : ∀ x ∈ G, 1 / 2 ≤ ‖b - x‖) (hfar : ∀ x ∈ G, ‖b - x‖ ≤ 8)
    (hT : ∀ x, T x ⊆ F) (hne : ∃ x, (T x).Nonempty)
    (hdensity : δ ^ η * (G.card : ℝ) * (F.card : ℝ) ≤ ∑ x, ((T x).card : ℝ))
    (hQ : ∀ x, ∀ a ∈ T x, (a, (x : Plane), b) ∈ Q) : ProjectionGain δ η ε Q := by
  have hw : 0 < w := hδ.trans_le hδw
  have hC : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hb.scale_le_one (by linarith)
  obtain ⟨x, hx⟩ := strip_radial_gain F G T hδ hδw hw1 ht ht16 hwt hC
    (by positivity : 0 < δ ^ η) (by linarith : 0 ≤ 1 - ε / 2) (by linarith : 1 - ε / 2 < 1)
    hn hF hG hstrip hpin hsep hfar hT hne hdensity
  have hKbound : 4096 * δ ^ (-η) / t ≤ 8192 * δ ^ (-η - κ) := by
    calc 4096 * δ ^ (-η) / t = 4096 * δ ^ (-η) * (1 / t) := by ring
      _ ≤ 4096 * δ ^ (-η) * δ ^ (-κ) := mul_le_mul_of_nonneg_left htt (by positivity)
      _ = 4096 * δ ^ (-η - κ) := by rw [mul_assoc, ← Real.rpow_add hδ]; congr 1
      _ ≤ _ := by gcongr; norm_num
  have hcover := hb.radial_cover_lower hδ hε hε1 zero_lt_one hw
    (by positivity : 0 < 4096 * δ ^ (-η) / t) hratio hKbound
    (by simpa only [div_one] using hx)
  apply projectionGain_of_bounded_negative hδw (hb.gain_length hδ hw hηε hratio) hcover
    (by convert le_rfl using 1 <;> congr 1 <;> ring)
  · rintro s ⟨a, ha, rfl⟩
    refine ⟨(a, (x : Plane), b), hQ x a ha, ?_⟩
    change -inner ℝ a (b - x) = inner ℝ a ((x : Plane) - b)
    rw [show (x : Plane) - b = -(b - x) by abel, inner_neg_right]
  · rintro s ⟨a, ha, rfl⟩
    have hprod : ‖a‖ * ‖b - (x : Plane)‖ ≤ 4 * 8 :=
      mul_le_mul (hFnorm a (hT x ha)) (hfar x x.property) (norm_nonneg _) (by norm_num)
    exact ((abs_real_inner_le_norm _ _).trans hprod).trans (by norm_num)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
