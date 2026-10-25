-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AlignmentFirst.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentNumerics
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripProjectionCount
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ProjectionInterval

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- A vertex outside the wider orthogonal strip yields the gain alternative.
This is the first step of the alignment lemma. -/
theorem alignment_first_gain {δ ε η κ c t : ℝ} {a b e : Plane} {G T : Finset Plane}
    {Q : Set Triple} (hb : AlignmentScaleBudget δ ε η κ)
    (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hκ : 0 ≤ κ) (hηκ : η ≤ κ)
    (hδt : δ ≤ t) (he : ‖e‖ = 1) (ha : ‖a‖ ≤ 4)
    (hG : ClosedFiniteFrostman δ (δ ^ (-η)) G)
    (hTG : T ⊆ G) (hTne : T.Nonempty)
    (hdensity : δ ^ η * (G.card : ℝ) ≤ (T.card : ℝ))
    (hstrip : ∀ x ∈ T, |inner ℝ x (perp e) - c| ≤ t)
    (hpin : |inner ℝ b (perp e) - c| ≤ t)
    (hfar : ∀ x ∈ T, ‖x - b‖ ≤ 8)
    (houtside : δ ^ (-κ) * t ≤ |inner ℝ a e|)
    (hQ : ∀ x ∈ T, (a, x, b) ∈ Q) : ProjectionGain δ η ε Q := by
  have ht : 0 < t := hδ.trans_le hδt
  have hA : 0 < |inner ℝ a e| := (by positivity : 0 < δ ^ (-κ) * t).trans_le houtside
  have hκpow : 1 ≤ δ ^ (-κ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hb.scale_le_one (by linarith)
  have htA : t ≤ |inner ℝ a e| := by nlinarith
  have hratio : δ ^ (-κ) ≤ |inner ℝ a e| / t := (le_div_iff₀ ht).mpr houtside
  have hnum := hb.transverse_gain hδ hε hε1 (div_pos hA ht) hratio
  have hnum' : (2 * (16 * |inner ℝ a e|) / t) ^ (1 - ε) ≤
      δ ^ η * |inner ℝ a e| / (18 * δ ^ (-η) * t) := by
    have hid : δ ^ η / δ ^ (-η) = δ ^ (2 * η) := by
      rw [← Real.rpow_sub hδ]
      congr 1
      ring
    calc (2 * (16 * |inner ℝ a e|) / t) ^ (1 - ε) =
          (32 * (|inner ℝ a e| / t)) ^ (1 - ε) := by congr 1; ring
      _ ≤ δ ^ (2 * η) * (|inner ℝ a e| / t) / 18 := hnum
      _ = _ := by rw [← hid]; ring
  have hηpow : δ ^ (-η) ≤ δ ^ (-κ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hb.scale_le_one (by linarith)
  have hlength : δ ^ (-η) * t ≤ 2 * (16 * |inner ℝ a e|) := by
    have h := mul_le_mul_of_nonneg_right hηpow ht.le
    nlinarith
  apply projectionGain_of_bounded_subset hδt hlength
    (strip_transverse_projection_count hδ hδt (by positivity) he ha hA hG hTG hTne hdensity hstrip) hnum'
  · rintro s ⟨x, hx, rfl⟩
    exact ⟨(a, x, b), hQ x hx, rfl⟩
  · rintro s ⟨x, hx, rfl⟩
    exact strip_dot_abs_bound he ha ht.le (hstrip x hx) hpin (hfar x hx) htA

end WangZahlLot.Obl.wz_separated_projection_dichotomy
