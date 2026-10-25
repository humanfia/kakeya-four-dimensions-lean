import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameLabels

/-!
# Scales of the residual labels

Every grid level has a retained node, so its blocks are finer than the
parent block. The residual block length is `q / q₀`; the residual depth of
level `h` is `h * (U' / m)`, and the original depth is `s₀` plus it. The
residual block counts are within `K ^ 2` of `N ^ (κ * h * U' / m)`.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- Every grid level has a retained residual label. -/
theorem FrameGood.level_nonempty (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    ∃ i : Fin (f.retained h).card, True := by
  obtain ⟨p, hp⟩ := hg.core_nonempty
  obtain ⟨i, u, hiu⟩ := hg.core_cover p hp h hh
  exact ⟨f.labelOf h (i, u) (f.mem_retained ⟨p, hiu, hp⟩), trivial⟩

theorem FrameGood.T₀_le (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    f.T₀ ≤ f.Tl h := by
  obtain ⟨i, -⟩ := hg.level_nonempty hh
  exact f.T₀_le (hg.inside hh i).1

/-- The residual block length is the original one divided by the parent's. -/
theorem FrameGood.resq (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    (2 : ℝ) ^ (-(f.resT h : ℤ)) = f.ql h / f.q₀ := by
  have hT := hg.T₀_le hh
  rw [q₀_eq]
  simp only [ql, resT, T₀] at *
  rw [div_eq_mul_inv, ← zpow_neg, neg_neg, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  push_cast [Nat.cast_sub hT]
  ring

theorem FrameGood.depth_eq (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    f.depth h = s₀ + (h : ℝ) * (U' / f.m) := by
  simp only [depth, frameDepth, min_eq_left hh]

theorem FrameGood.q₀_le_K (hg : FrameGood f Rk θ K₂ e₀') :
    D.N k ^ (D.κ * s₀) / D.K k ≤ f.q₀⁻¹ ∧ f.q₀⁻¹ ≤ D.K k * D.N k ^ (D.κ * s₀) := by
  have hc := hg.count 0 (Nat.zero_le _)
  rw [hg.depth_zero] at hc
  have : f.q₀⁻¹ = (2 : ℝ) ^ f.Tl 0 := by simp [q₀, T₀]
  rw [this]
  exact hc

/-- The residual block counts. -/
theorem FrameGood.res_count (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m))) / D.K k ^ 2 ≤ (2 : ℝ) ^ f.resT h ∧
      (2 : ℝ) ^ f.resT h ≤ D.K k ^ 2 * D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m))) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hK : 0 < D.K k := by linarith [hg.K_ge]
  have hT := hg.T₀_le hh
  have hc := hg.count h hh
  have hc₀ := hg.count 0 (Nat.zero_le _)
  rw [hg.depth_eq hh] at hc
  rw [hg.depth_zero] at hc₀
  have hsplit : D.N k ^ (D.κ * (s₀ + (h : ℝ) * (U' / f.m))) =
      D.N k ^ (D.κ * s₀) * D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m))) := by
    rw [← Real.rpow_add hN]; ring_nf
  rw [hsplit] at hc
  have hpow : (2 : ℝ) ^ f.resT h * (2 : ℝ) ^ f.T₀ = (2 : ℝ) ^ f.Tl h := by
    rw [← pow_add, resT, Nat.sub_add_cancel hT]
  set X := (2 : ℝ) ^ f.resT h
  set Y := (2 : ℝ) ^ f.T₀ with hY
  have hY0 : 0 < Y := by positivity
  set A := D.N k ^ (D.κ * s₀)
  set B := D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m)))
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hY1 : A / D.K k ≤ Y := hc₀.1
  have hY2 : Y ≤ D.K k * A := hc₀.2
  rw [← hpow] at hc
  obtain ⟨hc1, hc2⟩ := hc
  constructor
  · rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hK] at hc1 hY1
    nlinarith
  · rw [div_le_iff₀ hK] at hY1
    have hX : 0 ≤ X := by positivity
    have h1 : X * A ≤ X * (Y * D.K k) := mul_le_mul_of_nonneg_left hY1 hX
    have h2 : X * A ≤ D.K k ^ 2 * B * A := by nlinarith
    exact le_of_mul_le_mul_right h2 hA

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
