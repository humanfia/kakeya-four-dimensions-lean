-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/ZoomLocalization.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/ZoomLocalization.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.QuantitativeLocalization
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.AffineTransport

/-!
# Localizing a dominated group measure to a zoom ball

A group measure `μ` on events, with base map `Zc` into block (cube) coordinates bounded by
`A ^ s`, density at most `β` times volume and mass at least `m`, keeps a fixed power of its mass
in a ball of radius `(A ^ Mloc)⁻¹` about one of its own points `Zc ω₀`
(`power_bounded_image_mass_localization`). In the zoomed coordinates `z = λ (x - Zc ω₀)` the
localized measure lives in the ball of radius `λ / A ^ Mloc` and its density is at most
`β / λ ^ 3`. With `λ ≤ A ^ Mloc` its mass-to-density ratio loses only a fixed power of `A`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MeasureTheory Metric Set

/-- The zoom map `x ↦ λ (x - c)`. -/
def zoomMap (c : Base) (lam : ℝ) (x : Base) : Base := lam • (x - c)

lemma continuous_zoomMap (c : Base) (lam : ℝ) : Continuous (zoomMap c lam) :=
  (continuous_id.sub continuous_const).const_smul lam

lemma measurable_zoomMap (c : Base) (lam : ℝ) : Measurable (zoomMap c lam) :=
  (continuous_zoomMap c lam).measurable

lemma volume_preimage_zoomMap (c : Base) {lam : ℝ} (hlam : 0 < lam) (U : Set Base) :
    volume (zoomMap c lam ⁻¹' U) = ENNReal.ofReal (lam ^ 3)⁻¹ * volume U := by
  have h1 : zoomMap c lam ⁻¹' U = (fun x => x + (-c)) ⁻¹' ((fun y => lam • y) ⁻¹' U) := by
    ext x
    simp [zoomMap, sub_eq_add_neg]
  rw [h1, measure_preimage_add_right, Measure.addHaar_preimage_smul volume hlam.ne']
  simp [abs_of_pos (pow_pos hlam 3)]

lemma norm_zoomMap_lt_one {c x : Base} {lam : ℝ} (hlam : 0 < lam) (hx : x ∈ ball c lam⁻¹) :
    ‖zoomMap c lam x‖ < 1 := by
  rw [mem_ball, dist_eq_norm] at hx
  rw [zoomMap, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  calc lam * ‖x - c‖ < lam * lam⁻¹ := mul_lt_mul_of_pos_left hx hlam
    _ = 1 := mul_inv_cancel₀ hlam.ne'

/-- The zoom of a point at distance less than `r` from the centre has norm less than `λ r`. -/
lemma norm_zoomMap_lt {c x : Base} {lam r : ℝ} (hlam : 0 < lam) (hx : x ∈ ball c r) :
    ‖zoomMap c lam x‖ < lam * r := by
  rw [mem_ball, dist_eq_norm] at hx
  rw [zoomMap, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  exact mul_lt_mul_of_pos_left hx hlam

/-- **Zoom localization.** A dominated group measure keeps a fixed power of its mass in the
ball of radius `(A ^ Mloc)⁻¹` about one of its points; under the zoom `x ↦ λ (x - Zc ω₀)` the
localized part has density at most `β / λ ^ 3` and lies in the ball of radius `λ / A ^ Mloc`. -/
theorem zoom_group_localization {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Zc : Ω → Base) (hZc : Measurable Zc) (G : Set Ω) (hG : MeasurableSet G) (hfin : μ G ≠ ⊤)
    {A : ℝ} (hA : 2 ≤ A) (s Mloc : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hbound : ∀ ω ∈ G, Zc ω ∈ ball (0 : Base) (A ^ s))
    {m β : ℝ} (hm : 0 < m) (hmass : ENNReal.ofReal m ≤ μ G)
    (hdom : ∀ U : Set Base, MeasurableSet U → μ (G ∩ Zc ⁻¹' U) ≤ ENNReal.ofReal β * volume U) :
    ∃ ω₀ ∈ G,
      MeasurableSet {ω | ω ∈ G ∧ Zc ω ∈ ball (Zc ω₀) (A ^ Mloc)⁻¹} ∧
      ENNReal.ofReal (m / A ^ (3 * (s + Mloc) + 14)) ≤
        μ {ω | ω ∈ G ∧ Zc ω ∈ ball (Zc ω₀) (A ^ Mloc)⁻¹} ∧
      (∀ U : Set Base, MeasurableSet U →
        μ ((fun ω => zoomMap (Zc ω₀) lam (Zc ω)) ⁻¹' U ∩
          {ω | ω ∈ G ∧ Zc ω ∈ ball (Zc ω₀) (A ^ Mloc)⁻¹}) ≤
        ENNReal.ofReal (β / lam ^ 3) * volume U) ∧
      ∀ ω ∈ {ω | ω ∈ G ∧ Zc ω ∈ ball (Zc ω₀) (A ^ Mloc)⁻¹},
        ‖zoomMap (Zc ω₀) lam (Zc ω)‖ < lam * (A ^ Mloc)⁻¹ := by
  have hApos : 0 < A := by linarith
  have hGne : G.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty] at hmass
    exact absurd (ENNReal.ofReal_pos.mpr hm) (not_lt.mpr hmass)
  obtain ⟨ω₀, hω₀, hloc⟩ := power_bounded_image_mass_localization μ Zc G hGne hA s Mloc hbound
    hfin
  set Gz := {ω | ω ∈ G ∧ Zc ω ∈ ball (Zc ω₀) (A ^ Mloc)⁻¹} with hGz
  have hGzm : MeasurableSet Gz := hG.inter (hZc measurableSet_ball)
  refine ⟨ω₀, hω₀, hGzm, ?_, ?_, ?_⟩
  · -- the mass of the localization ball
    set k := 3 * (s + Mloc) + 14
    have hk : 0 < A ^ k := pow_pos hApos k
    have hkne : ENNReal.ofReal (A ^ k) ≠ 0 := (ENNReal.ofReal_pos.mpr hk).ne'
    rw [ENNReal.ofReal_div_of_pos hk, ENNReal.div_le_iff hkne ENNReal.ofReal_ne_top, mul_comm]
    exact hmass.trans hloc
  · intro U hU
    have hpre : MeasurableSet (zoomMap (Zc ω₀) lam ⁻¹' U) := measurable_zoomMap _ _ hU
    calc μ ((fun ω => zoomMap (Zc ω₀) lam (Zc ω)) ⁻¹' U ∩ Gz)
        ≤ μ (G ∩ Zc ⁻¹' (zoomMap (Zc ω₀) lam ⁻¹' U)) := by
          apply measure_mono
          intro ω hω
          exact ⟨hω.2.1, hω.1⟩
      _ ≤ ENNReal.ofReal β * volume (zoomMap (Zc ω₀) lam ⁻¹' U) := hdom _ hpre
      _ = ENNReal.ofReal β * (ENNReal.ofReal (lam ^ 3)⁻¹ * volume U) := by
          rw [volume_preimage_zoomMap _ hlam]
      _ = ENNReal.ofReal (β / lam ^ 3) * volume U := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul' (inv_nonneg.mpr (pow_pos hlam 3).le),
            div_eq_mul_inv]
  · intro ω hω
    exact norm_zoomMap_lt hlam hω.2

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
