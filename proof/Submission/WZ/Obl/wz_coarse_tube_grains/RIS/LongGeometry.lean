-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LongGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleSubfamily

/-!
# Bounded-length carrier tubes

The midpoint convention agrees with `rescaleMap`: all carriers below are centered at `y+w/2`.
The fine tubes still have unit directions and length one.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

/-- A length-`L` carrier centered at `y+w/2`. -/
def Carrier (L ρ : ℝ) (y w : Space) : Set Space :=
  Tube ρ (y + ((1 - L) / 2) • w) (L • w)

/-- Angular confinement is independent of the length of the carrier. -/
theorem pd_lt_of_tube_subset_carrier {δ ρ L : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (h : Tube δ x v ⊆ Carrier L ρ y w) :
    pd v w < 4 * ρ := by
  have hx : x ∈ Carrier L ρ y w :=
    h (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hxv : x + v ∈ Carrier L ρ y w :=
    h (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  obtain ⟨q, hq, hxq⟩ := mem_thickening_iff.mp hx
  obtain ⟨q', hq', hxq'⟩ := mem_thickening_iff.mp hxv
  rw [segment_eq_image'] at hq hq'
  obtain ⟨s, _, rfl⟩ := hq
  obtain ⟨s', _, rfl⟩ := hq'
  simp only [add_sub_cancel_left] at hxq hxq'
  rw [dist_eq_norm] at hxq hxq'
  set d := (s' - s) * L
  have hdv : ‖v - d • w‖ < 2 * ρ := by
    have heq : v - d • w =
        (x + v - (y + ((1 - L) / 2) • w + s' • (L • w))) -
        (x - (y + ((1 - L) / 2) • w + s • (L • w))) := by dsimp [d]; module
    rw [heq]
    have hb := norm_sub_le (x + v - (y + ((1 - L) / 2) • w + s' • (L • w)))
      (x - (y + ((1 - L) / 2) • w + s • (L • w)))
    linarith
  have hgap : abs (1 - abs d) < 2 * ρ := by
    have hgap := abs_norm_sub_norm_le v (d • w)
    rw [hv, norm_smul, Real.norm_eq_abs, hw, mul_one] at hgap
    exact hgap.trans_lt hdv
  rcases le_or_gt 0 d with hd | hd
  · have hgap' : |1 - d| < 2 * ρ := by simpa [abs_of_nonneg hd] using hgap
    have heq : v - w = (v - d • w) - (1 - d) • w := by module
    have hnorm := norm_sub_le (v - d • w) ((1 - d) • w)
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one, ← heq] at hnorm
    exact (min_le_left _ _).trans_lt (by linarith)
  · have hgap' : |1 + d| < 2 * ρ := by simpa [abs_of_neg hd] using hgap
    have heq : v + w = (v - d • w) + (1 + d) • w := by module
    have hnorm := norm_add_le (v - d • w) ((1 + d) • w)
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one, ← heq] at hnorm
    exact (min_le_right _ _).trans_lt (by linarith)

/-- The anisotropic image of a length-`L` carrier is uniformly bounded. -/
theorem rescaleMap_carrier_norm_lt (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {κ ρ L : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hL : 0 ≤ L) {p : Space} (hp : p ∈ Carrier L ρ y w) :
    ‖rescaleMap e y w hκ hρ p‖ < κ * (L / 2 + 1) := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have heq : y + ((1 - L) / 2) • w + s • (L • w) =
      y + ((1 - L) / 2 + s * L) • w := by module
  have hq : ‖rescaleMap e y w hκ hρ (y + ((1 - L) / 2) • w + s • (L • w))‖ ≤ κ * (L / 2) := by
    rw [heq, rescaleMap_segment_norm e hew hκ hρ]
    apply mul_le_mul_of_nonneg_left _ hκ.le
    apply abs_le.mpr
    constructor <;> nlinarith [hs.1, hs.2]
  have hd := rescaleMap_dist_le e y w hκ hρ hρ1 p
    (y + ((1 - L) / 2) • w + s • (L • w))
  have hdist : κ * ρ⁻¹ * dist p (y + ((1 - L) / 2) • w + s • (L • w)) < κ := by
    calc
      _ < κ * ρ⁻¹ * ρ := by gcongr
      _ = κ := by field_simp
  have hn := norm_le_norm_add_norm_sub
    (rescaleMap e y w hκ hρ (y + ((1 - L) / 2) • w + s • (L • w)))
    (rescaleMap e y w hκ hρ p)
  rw [norm_sub_rev, ← dist_eq_norm] at hn
  linarith

/-- Unit carriers are contained in any longer centered carrier. -/
theorem tube_subset_carrier {L ρ : ℝ} (hL : 1 ≤ L) (y w : Space) :
    Tube ρ y w ⊆ Carrier L ρ y w := by
  apply thickening_subset_of_subset
  have hL0 : 0 < L := by linarith
  intro p hp
  rw [segment_eq_image'] at hp ⊢
  obtain ⟨s, hs, rfl⟩ := hp
  refine ⟨(s + (L - 1) / 2) / L, ?_, ?_⟩
  · constructor
    · apply div_nonneg <;> linarith [hs.1]
    · rw [div_le_one hL0]; linarith [hs.2]
  · simp only [add_sub_cancel_left, smul_smul]
    rw [div_mul_cancel₀ _ hL0.ne']
    module

/-- The centered carrier lies inside its two-fold dilation. -/
theorem carrier_subset_dilate {L ρ : ℝ} (hρ : 0 ≤ ρ) (y w : Space) :
    Carrier L ρ y w ⊆ Carrier (2 * L) (2 * ρ) y w := by
  have h := tube_subset_dilate hρ (y + ((1 - L) / 2) • w) (L • w)
  have hc : y + ((1 - L) / 2) • w - (1 / 2 : ℝ) • (L • w) =
      y + ((1 - 2 * L) / 2) • w := by module
  have hd : (2 : ℕ) • (L • w) = (2 * L) • w := by
    rw [two_smul]; module
  rw [hc, hd] at h
  exact h

/-- The midpoint diameter of fine tubes in a bounded-length carrier is bounded. -/
theorem midpoint_dist_lt_carrier {δ ρ L : ℝ} (hδ : 0 < δ) (hρ1 : ρ ≤ 1) (hL : 0 ≤ L)
    {x v x' v' y w : Space} (hw : ‖w‖ = 1)
    (hsub : Tube δ x v ⊆ Carrier L ρ y w) (hsub' : Tube δ x' v' ⊆ Carrier L ρ y w) :
    ‖(x' + (1 / 2 : ℝ) • v') - (x + (1 / 2 : ℝ) • v)‖ < L + 2 := by
  have hmid : ∀ {a b : Space}, Tube δ a b ⊆ Carrier L ρ y w →
      ∃ s ∈ Icc (0 : ℝ) 1,
        ‖(a + (1 / 2 : ℝ) • b) - (y + ((1 - L) / 2) • w + s • (L • w))‖ < ρ := by
    intro a b hab
    have hm : a + (1 / 2 : ℝ) • b ∈ Carrier L ρ y w := by
      apply hab
      apply self_subset_thickening hδ
      rw [segment_eq_image']
      exact ⟨1 / 2, by norm_num, by simp⟩
    obtain ⟨q, hq, hmq⟩ := mem_thickening_iff.mp hm
    rw [segment_eq_image'] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    exact ⟨s, hs, by simpa [dist_eq_norm] using hmq⟩
  obtain ⟨s, hs, h1⟩ := hmid hsub
  obtain ⟨s', hs', h2⟩ := hmid hsub'
  have heq : (x' + (1 / 2 : ℝ) • v') - (x + (1 / 2 : ℝ) • v) =
      ((x' + (1 / 2 : ℝ) • v') - (y + ((1 - L) / 2) • w + s' • (L • w))) -
      ((x + (1 / 2 : ℝ) • v) - (y + ((1 - L) / 2) • w + s • (L • w))) +
      ((s' - s) * L) • w := by module
  rw [heq]
  have h3 : ‖((s' - s) * L) • w‖ ≤ L := by
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one, abs_mul, abs_of_nonneg hL]
    have hs1 : |s' - s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2, hs'.1], by linarith [hs.1, hs'.2]⟩
    nlinarith
  have h4 := norm_add_le
    (((x' + (1 / 2 : ℝ) • v') - (y + ((1 - L) / 2) • w + s' • (L • w))) -
      ((x + (1 / 2 : ℝ) • v) - (y + ((1 - L) / 2) • w + s • (L • w))))
    (((s' - s) * L) • w)
  have h5 := norm_sub_le
    ((x' + (1 / 2 : ℝ) • v') - (y + ((1 - L) / 2) • w + s' • (L • w)))
    ((x + (1 / 2 : ℝ) • v) - (y + ((1 - L) / 2) • w + s • (L • w)))
  linarith

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
