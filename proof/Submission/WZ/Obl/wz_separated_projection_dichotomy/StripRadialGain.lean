-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripRadialGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripRadialFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialGain

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

theorem strip_pin_gap {n b x : Plane} {c w t : ℝ}
    (hx : |inner ℝ x n - c| ≤ w) (hb : t ≤ |inner ℝ b n - c|) (hw : w ≤ t / 2) :
    t / 2 ≤ |inner ℝ x n - inner ℝ b n| := by
  have htriangle : |inner ℝ b n - c| ≤ |inner ℝ x n - inner ℝ b n| + |inner ℝ x n - c| := by
    calc |inner ℝ b n - c| = |(inner ℝ b n - inner ℝ x n) + (inner ℝ x n - c)| := by congr 1; ring
      _ ≤ |inner ℝ b n - inner ℝ x n| + |inner ℝ x n - c| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (inner ℝ b n) (inner ℝ x n)]
  linarith

/-- Unscaled counterpart of the anisotropic radial estimate, useful when
the outer strip is already wide. -/
theorem strip_radial_gain {δ w t C d γ c : ℝ} {n b : Plane}
    (F G : Finset Plane) (T : G → Finset Plane)
    (hδ : 0 < δ) (hδw : δ ≤ w) (hw : 2 * w ≤ 1)
    (ht : 0 < t) (ht16 : t ≤ 16) (hwt : w ≤ t / 2)
    (hC : 1 ≤ C) (hd : 0 < d) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hn : ‖n‖ = 1)
    (hF : ClosedFiniteFrostman δ C F) (hG : ClosedFiniteFrostman δ C G)
    (hstrip : ∀ x ∈ G, |inner ℝ x n - c| ≤ w)
    (hpin : t ≤ |inner ℝ b n - c|)
    (hsep : ∀ x ∈ G, 1 / 2 ≤ ‖b - x‖) (hfar : ∀ x ∈ G, ‖b - x‖ ≤ 8)
    (hT : ∀ x, T x ⊆ F) (hne : ∃ x, (T x).Nonempty)
    (hdensity : d * (G.card : ℝ) * (F.card : ℝ) ≤ ∑ x, ((T x).card : ℝ)) :
    ∃ x : G, ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers w ((fun a => inner ℝ a (b - x)) '' (↑(T x) : Set Plane)) cc →
        d ^ 2 ≤ (8 * (4096 * C / t) ^ 2 * energyConstant γ * (2 * w) ^ γ) * (m : ℝ) := by
  have hwpos : 0 < w := hδ.trans_le hδw
  have hCK : C ≤ 4096 * C / t := (le_div_iff₀ ht).mpr (by
    nlinarith [mul_le_mul_of_nonneg_left ht16 (zero_le_one.trans hC)])
  have hδρ : δ ≤ 2 * w := by linarith
  have hbf : ∀ x : G, b ≠ (x : Plane) := by
    intro x heq
    have h := hsep x x.property
    rw [heq, sub_self, norm_zero] at h
    norm_num at h
  have hdir0 := hG.indexed.radial_of_strip (by positivity : 0 ≤ 2 * w) hδρ
    (zero_le_one.trans hC) hn (half_pos ht) (by linarith : t / 2 ≤ 16)
    (by linarith : w ≤ 2 * w) hbf (fun x => hstrip x x.property)
    (fun x => strip_pin_gap (hstrip x x.property) hpin hwt)
    (fun x => (hfar x x.property).trans (by norm_num : (8 : ℝ) ≤ 16))
  have hdir : IndexedFrostman (2 * w) (4096 * C / t) (fun x : G => radialDirection b x) := by
    convert hdir0 using 1 <;> ring
  have hF' := ((hF.mono_constant hδ.le hCK).mono_scale hδρ)
  obtain ⟨x, hx⟩ := indexed_kaufman_energy_gain T hF' hdir (by positivity) hw
    (hC.trans hCK) hd (fun x => radialDirection_norm (hbf x)) hγ hγ1 hT hne
    (by simpa only [Fintype.card_coe] using hdensity)
  refine ⟨x, ?_⟩
  intro m cc hc
  exact hx m _ (hc.normalized_radial_dot hwpos.le (hsep x x.property))

end WangZahlLot.Obl.wz_separated_projection_dichotomy
