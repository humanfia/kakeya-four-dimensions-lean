-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomConflict.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomBasic

/-!
# Lines that are close at two separated points

If two lines pass within `2ε` of each other at two points whose parameters on the first line
are at least `λ ≥ 8ε` apart, their directions agree up to sign within `16 ε / λ`, and the second
line stays within `2ε + |t - t₁| · 16 ε / λ` of the first.  Two unit tubes overlapping in more
than half the volume of the first contain two common points with parameters `1/1024` apart.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- Directions of two lines close at two separated points. -/
theorem dir_of_two_points {u w a b : Space} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    {s₁ s₂ t₁ t₂ ε l : ℝ} (hl : 0 < l) (hεl : 8 * ε ≤ l) (hsep : l ≤ |s₂ - s₁|)
    (h₁ : ‖(a + s₁ • u) - (b + t₁ • w)‖ ≤ 2 * ε)
    (h₂ : ‖(a + s₂ • u) - (b + t₂ • w)‖ ≤ 2 * ε) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖w - σ • u‖ ≤ 16 * ε / l := by
  have hε : 0 ≤ ε := (by have := norm_nonneg ((a + s₁ • u) - (b + t₁ • w)); linarith)
  have hΔ : ‖(t₂ - t₁) • w - (s₂ - s₁) • u‖ ≤ 4 * ε := by
    have he : (t₂ - t₁) • w - (s₂ - s₁) • u =
        ((a + s₁ • u) - (b + t₁ • w)) - ((a + s₂ • u) - (b + t₂ • w)) := by module
    rw [he]; exact (norm_sub_le _ _).trans (by linarith)
  have ht : l / 2 ≤ |t₂ - t₁| := by
    have h := norm_sub_norm_le ((s₂ - s₁) • u) ((t₂ - t₁) • w)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hu, hw, mul_one, mul_one,
      norm_sub_rev] at h
    linarith
  have htpos : 0 < |t₂ - t₁| := by linarith
  set q := (s₂ - s₁) / (t₂ - t₁)
  have hwq : ‖w - q • u‖ ≤ 8 * ε / l := by
    have he : w - q • u = (t₂ - t₁)⁻¹ • ((t₂ - t₁) • w - (s₂ - s₁) • u) := by
      have hne : t₂ - t₁ ≠ 0 := abs_pos.mp htpos
      simp only [q, smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul, div_eq_inv_mul]
    rw [he, norm_smul, Real.norm_eq_abs, abs_inv, inv_mul_le_iff₀ htpos]
    calc ‖(t₂ - t₁) • w - (s₂ - s₁) • u‖ ≤ 4 * ε := hΔ
      _ ≤ |t₂ - t₁| * (8 * ε / l) := by
        rw [mul_div_assoc', le_div_iff₀ hl]; nlinarith
  have hq1 : |1 - abs q| ≤ 8 * ε / l := by
    have h := norm_sub_norm_le w (q • u)
    have h' := norm_sub_norm_le (q • u) w
    rw [norm_smul, Real.norm_eq_abs, hu, hw, mul_one] at h h'
    rw [norm_sub_rev] at h'
    rw [abs_le]; constructor <;> linarith
  have h16 : 16 * ε / l = 8 * ε / l + 8 * ε / l := by ring
  rcases le_or_gt 0 q with hq | hq
  · refine ⟨1, Or.inl rfl, ?_⟩
    have he : w - (1 : ℝ) • u = (w - q • u) + (q - 1) • u := by module
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_sub_comm, ← abs_of_nonneg hq]
    rw [abs_of_nonneg hq] at hq1 ⊢
    linarith
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have he : w - (-1 : ℝ) • u = (w - q • u) + (q + 1) • u := by module
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
    rw [abs_of_neg hq] at hq1
    have : |q + 1| = |1 - -q| := by congr 1; ring
    rw [this]
    linarith

/-- The second line stays close to the first one, with a linearly growing error. -/
theorem line_close_of_two_points {u w a b : Space} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    {s₁ s₂ t₁ t₂ ε l : ℝ} (hl : 0 < l) (hεl : 8 * ε ≤ l) (hsep : l ≤ |s₂ - s₁|)
    (h₁ : ‖(a + s₁ • u) - (b + t₁ • w)‖ ≤ 2 * ε)
    (h₂ : ‖(a + s₂ • u) - (b + t₂ • w)‖ ≤ 2 * ε) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ t : ℝ,
      ‖(b + t • w) - (a + (s₁ + σ * (t - t₁)) • u)‖ ≤ 2 * ε + |t - t₁| * (16 * ε / l) := by
  obtain ⟨σ, hσ, hwσ⟩ := dir_of_two_points hu hw hl hεl hsep h₁ h₂
  refine ⟨σ, hσ, fun t => ?_⟩
  have he : (b + t • w) - (a + (s₁ + σ * (t - t₁)) • u) =
      -((a + s₁ • u) - (b + t₁ • w)) + (t - t₁) • (w - σ • u) := by module
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_smul, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left hwσ (abs_nonneg (t - t₁))
  linarith

/-- Two unit tubes overlapping in more than half of the first contain two common points
whose axial parameters on the first tube are more than `1/1024` apart. -/
theorem overlap_far_points {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 1024) {a u : Space}
    (hu : ‖u‖ = 1) {B : Set Space}
    (hover : (1 / 2 : ℝ≥0∞) * volume (Tube ρ a u) < volume (Tube ρ a u ∩ B)) :
    ∃ s₁ ∈ Icc (0 : ℝ) 1, ∃ s₂ ∈ Icc (0 : ℝ) 1, 1 / 1024 < |s₂ - s₁| ∧
      (∃ p ∈ B, ‖p - (a + s₁ • u)‖ < ρ) ∧ (∃ p ∈ B, ‖p - (a + s₂ • u)‖ < ρ) := by
  set S : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ ∃ p ∈ B, ‖p - (a + s • u)‖ < ρ}
  by_cases hdiam : ∀ s ∈ S, ∀ t ∈ S, dist s t ≤ 1 / 1024
  · exfalso
    have hsub : Tube ρ a u ∩ B ⊆ thickening ρ ((fun s => a + s • u) '' S) := by
      rintro p ⟨hpT, hpB⟩
      obtain ⟨s, hs, hps⟩ := exists_param_of_mem_tube' hpT
      exact mem_thickening_iff.mpr ⟨a + s • u, ⟨s, ⟨hs, p, hpB, hps⟩, rfl⟩,
        by rwa [dist_eq_norm]⟩
    have hvol := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
      a u hu (T := S) (fun s hs => hs.1) hρ (by norm_num) hdiam
    have hlow := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hρ a u hu
    have hup : volume (Tube ρ a u ∩ B) ≤ ENNReal.ofReal (3 / 8 * ρ ^ 2) := by
      refine (measure_mono hsub).trans (hvol.trans (ENNReal.ofReal_le_ofReal ?_))
      have : 128 * (2 * (1 / 1024) + ρ) ≤ 3 / 8 := by linarith
      nlinarith [sq_nonneg ρ]
    have hhalf : ENNReal.ofReal (1 / 2 * ρ ^ 2) ≤ (1 / 2 : ℝ≥0∞) * volume (Tube ρ a u) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      have h2 : ENNReal.ofReal (1 / 2) = (1 / 2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      rw [h2]
      gcongr
    have hlt : ENNReal.ofReal (3 / 8 * ρ ^ 2) < ENNReal.ofReal (1 / 2 * ρ ^ 2) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      nlinarith [sq_pos_of_pos hρ]
    exact absurd (hup.trans_lt (hlt.trans_le (hhalf.trans_lt hover).le)) (lt_irrefl _)
  · push Not at hdiam
    obtain ⟨s, hs, t, ht, hst⟩ := hdiam
    refine ⟨s, hs.1, t, ht.1, ?_, hs.2, ht.2⟩
    rwa [Real.dist_eq, abs_sub_comm] at hst

end

end WangZahlLot.Obl.wz_c2_slope_normalization
