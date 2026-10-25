-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.RadialGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FamilyGain

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

theorem Covers.normalized_radial_dot {δ : ℝ} {b x : Plane} {A : Set Plane}
    (hδ : 0 ≤ δ) (hsep : 1 / 2 ≤ ‖b - x‖) {m : ℕ} {cc : Fin m → ℝ}
    (hcov : Covers δ ((fun a => inner ℝ a (b - x)) '' A) cc) :
    Covers (2 * δ) ((fun a => inner ℝ (radialDirection b x) a) '' A)
      (fun i => cc i / ‖b - x‖) := by
  have hn : 0 < ‖b - x‖ := by linarith
  have hbx : b ≠ x := sub_ne_zero.mp (norm_pos_iff.mp hn)
  rintro t ⟨a, ha, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ⟨a, ha, rfl⟩)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hid : inner ℝ (radialDirection b x) a = inner ℝ a (b - x) / ‖b - x‖ := by
    apply (eq_div_iff hn.ne').mpr
    rw [radialDirection_dot hbx]
    ring
  change dist (inner ℝ (radialDirection b x) a) (cc i / ‖b - x‖) ≤ 2 * δ
  calc dist (inner ℝ (radialDirection b x) a) (cc i / ‖b - x‖) =
        dist (inner ℝ a (b - x)) (cc i) / ‖b - x‖ := by
          rw [hid, Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hn]
    _ ≤ δ / ‖b - x‖ := div_le_div_of_nonneg_right hi hn.le
    _ ≤ 2 * δ := (div_le_iff₀ hn).mpr (by nlinarith)

/-- A thin radial family gives a large dot-product projection. Direction
multiplicities are retained, so no discretization of the circle is needed. -/
theorem thin_radial_projection_gain {δ K c d γ : ℝ} (F E G : Finset Plane) (b : Plane)
    (T : E → Finset Plane) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hK : 1 ≤ K) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 0 < d)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hF : ClosedFiniteFrostman δ K F)
    (hsep : ∀ x ∈ E, 1 / 2 ≤ ‖b - x‖) (hfar : ∀ x ∈ E, ‖b - x‖ ≤ 8)
    (hret : c * (G.card : ℝ) ≤ (E.card : ℝ))
    (hthin : ∀ (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
      ((E.filter (fun x => |inner ℝ (x - b) u| < r)).card : ℝ) ≤ K * r * (G.card : ℝ))
    (hT : ∀ x, T x ⊆ F) (hne : ∃ x, (T x).Nonempty)
    (hdensity : d * (E.card : ℝ) * (F.card : ℝ) ≤ ∑ x, ((T x).card : ℝ)) :
    ∃ x : E, ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun a => inner ℝ a (b - x)) '' (↑(T x) : Set Plane)) cc →
        d ^ 2 ≤ (8 * (17 * K / c) ^ 2 * energyConstant γ * (2 * δ) ^ γ) * (m : ℝ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKC : K ≤ 17 * K / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc1 hK0]
  have hne' : ∀ x ∈ E, b ≠ x := by
    intro x hx heq
    have hs := hsep x hx
    simp only [heq, sub_self, norm_zero] at hs
    norm_num at hs
  have hdir := radialDirection_indexedFrostman E G b hδ hK0 hc hne' hfar hret hthin
  have hF' := (hF.mono_constant hδ.le hKC).mono_scale (by linarith : δ ≤ 2 * δ)
  obtain ⟨x, hx⟩ := indexed_kaufman_energy_gain T hF'
    (hdir.mono_scale (by linarith : δ ≤ 2 * δ)) (by positivity) (by linarith)
    (hK.trans hKC) hd (fun x => radialDirection_norm (hne' x x.property)) hγ hγ1
    hT hne (by simpa only [Fintype.card_coe] using hdensity)
  refine ⟨x, ?_⟩
  intro m cc hc
  exact hx m _ (hc.normalized_radial_dot hδ.le (hsep x x.property))

end WangZahlLot.Obl.wz_separated_projection_dichotomy
