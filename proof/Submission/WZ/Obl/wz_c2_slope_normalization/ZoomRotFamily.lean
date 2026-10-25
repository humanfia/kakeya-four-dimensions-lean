-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomRotFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomFamily
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomSlope

/-!
# Rotating a family with a slowly varying slope

Rotating about the vertical axis by `-arctan (h 0)` turns a slope `h` with first and second
derivatives at most `1/16` into the normalized slope `rotSlope h`.  Each twisted slice is
dilated by a factor in `(0, 2]`, which at most doubles the covering constant.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

theorem Grains.mono_constant {σ δ K K' : ℝ} {n : ℕ} {v : Fin n → Space}
    {Y : Fin n → Set Space} {f : ℝ → ℝ} {P : Space → Space} (hδ : 0 < δ) (hKK' : K ≤ K')
    (h : Grains σ δ K v Y f P) : Grains σ δ K' v Y f P := by
  obtain ⟨hglobal, hLip, hnorm, horth, hlocal⟩ := h
  refine ⟨fun z hz => (hglobal z hz).mono_constant hδ hKK', hLip, hnorm, horth, ?_⟩
  intro ρ hρ hρ1 p hp
  exact (hlocal ρ hρ hρ1 p hp).mono_constant (hδ.trans_le hρ) hKK'

/-- Rotation of a family with a slowly varying slope normalizes the slope. -/
theorem rotate_family {σ η δ K : ℝ} {m : ℕ} {x v : Fin m → Space} {Y : Fin m → Set Space}
    {h : ℝ → ℝ} {P : Space → Space} (hδ : 0 < δ) (hK : 1 / 2 ≤ K) (hσ1 : σ ≤ 1)
    (hfam : ExtremalFamily σ η δ m x v Y) (hgr : Grains σ δ K v Y h P)
    (hh : ContDiff ℝ 2 h) (hd1 : ∀ t, |deriv h t| ≤ 1 / 16)
    (hd2 : ∀ t, |deriv (deriv h) t| ≤ 1 / 16) :
    ∃ (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (P' : Space → Space),
      ExtremalFamily σ η δ m x' v' Y' ∧ NormalizedC2Slope (rotSlope h) ∧
        Grains σ δ (2 * K) v' Y' (rotSlope h) P' := by
  set h0 := h 0
  set θ := -Real.arctan h0
  set e := rotZ θ
  have hK0 : 0 < K := by linarith
  have hgd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hA : 0 < Real.sqrt (1 + h0 ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcos : Real.cos θ = 1 / Real.sqrt (1 + h0 ^ 2) := by
    simp only [θ, Real.cos_neg, Real.cos_arctan]
  have hsin : Real.sin θ = -(h0 / Real.sqrt (1 + h0 ^ 2)) := by
    simp only [θ, Real.sin_neg, Real.sin_arctan]
  refine ⟨fun i => e (x i), fun i => e (v i), fun i => e '' Y i, fun p => e (P (e.symm p)),
    hfam.isometry e, rotSlope_normalized (by norm_num) hh hd1 hd2, ?_⟩
  apply (hgr.mono_constant hδ (by linarith : K ≤ 2 * K)).isometry e
  intro z hz
  have hz2 : z ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  set H := h z
  set G := rotSlope h z
  have hden := rotSlope_denom hgd (by norm_num : (1 / 16 : ℝ) ≤ 1 / 16) hd1 z
  rw [clampφ_eq hz2] at hden
  have hB : 0 < 1 + H * h0 := by
    have : 0 < (1 + h0 ^ 2) / 2 := by positivity
    linarith
  have hGeq : G = (H - h0) / (1 + H * h0) := rotSlope_eq hz2
  have hBne : 1 + H * h0 ≠ 0 := hB.ne'
  have hBne' : 1 + h0 * H ≠ 0 := by rw [mul_comm]; exact hB.ne'
  have hrel : G * Real.cos θ - Real.sin θ = H * (Real.cos θ + G * Real.sin θ) := by
    rw [hcos, hsin, hGeq]
    field_simp
    ring
  set μ := Real.cos θ + G * Real.sin θ
  have hμ : μ = Real.sqrt (1 + h0 ^ 2) / (1 + H * h0) := by
    have hsq : Real.sqrt (1 + h0 ^ 2) ^ 2 = 1 + h0 ^ 2 := Real.sq_sqrt (by positivity)
    simp only [μ]
    rw [hcos, hsin, hGeq]
    field_simp
    rw [hsq]
    ring
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hμ2 : μ ≤ 2 := by
    rw [hμ, div_le_iff₀ hB]
    have h1 : Real.sqrt (1 + h0 ^ 2) ≤ 1 + h0 ^ 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_nonneg h0]
    linarith
  have hslice : ProjectedSlice (rotSlope h) (⋃ i, e '' Y i) z =
      (fun u => μ * u) '' ProjectedSlice h (⋃ i, Y i) z := by
    rw [← image_iUnion]
    exact projectedSlice_rotZ _ rfl rfl hrel
  rw [hslice]
  obtain ⟨hglobal, -, -, -, -⟩ := hgr
  have hα : 0 ≤ 1 - σ := by linarith
  rcases le_total μ 1 with hle | hge
  · have h1 := (hglobal z hz).contract_image hδ hμpos.ne' (by rw [abs_of_pos hμpos]; exact hle)
    exact h1.mono_constant hδ (by linarith)
  · exact (hglobal z hz).dilate_image hδ hα hK hge hμ2

end

end WangZahlLot.Obl.wz_c2_slope_normalization
