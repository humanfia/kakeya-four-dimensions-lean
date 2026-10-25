import Submission.Obl.k4_contact_affine_residual_candidate_transfer.GoodFramesSmall

/-!
# Atlas and nesting of the residual model on good frames

With the crude mesh exponent `r₁ = 8 U' + 1`, the fine mesh exponent
`r₂ = 9 U' + 1` and the cap range `R = 9 U' + 2`, the numerical conditions of
the slope passes hold eventually, because the calibration constants at scalar
factor one are subpower. Together with the residual caps of good frames this
gives the slope bounds at every grid level, hence the residual atlas for every
loss sequence above the subpower atlas constant, and the residual nesting.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

/-- The residual caps of good frames after one original tail, as provided by
`eventual_frame_capsAt`. -/
def FrameCapsEventually {α : Type} [MeasurableSpace α] (D : Data α) (s₀ U' R : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ (f : Frame D k s₀ U') (Rk θ K₂ e₀' : ℝ),
    FrameGood f Rk θ K₂ e₀' → D.N k ^ (-1 : ℝ) ≤ θ → f.H * f.a₀ ≤ 1 / 4 →
    f.CapsAt (27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / θ)) R

theorem numeric_crude {N P K U' d : ℝ} (hN : 1 ≤ N) (hU' : 0 ≤ U') (hd1 : d ≤ 1)
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hPK : P * K ^ 4 ≤ 1 / 2 * N ^ (1 : ℝ)) :
    P * (N ^ (d * U')) ^ 6 * (K ^ 4 * N ^ (2 * U')) * N ^ (-(8 * U' + 1)) ≤ 1 / 2 := by
  have hN0 : 0 < N := by linarith
  have e : (N ^ (d * U')) ^ 6 * N ^ (2 * U') * N ^ (-(8 * U' + 1)) =
      N ^ (6 * (d * U') + 2 * U' + -(8 * U' + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
      ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  have hle : N ^ (6 * (d * U') + 2 * U' + -(8 * U' + 1)) ≤ N ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have h1 : N ^ (1 : ℝ) * N ^ (-1 : ℝ) = 1 := by rw [← Real.rpow_add hN0]; simp
  calc P * (N ^ (d * U')) ^ 6 * (K ^ 4 * N ^ (2 * U')) * N ^ (-(8 * U' + 1))
      = P * K ^ 4 * ((N ^ (d * U')) ^ 6 * N ^ (2 * U') * N ^ (-(8 * U' + 1))) := by ring
    _ = P * K ^ 4 * N ^ (6 * (d * U') + 2 * U' + -(8 * U' + 1)) := by rw [e]
    _ ≤ (1 / 2 * N ^ (1 : ℝ)) * N ^ (-1 : ℝ) :=
        mul_le_mul hPK hle (Real.rpow_nonneg hN0.le _) (by positivity)
    _ = 1 / 2 := by rw [mul_assoc, h1, mul_one]

theorem numeric_fine {N P K U' : ℝ} (hN : 1 ≤ N) (hU' : 0 ≤ U')
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hPK : P * K ^ 4 ≤ 1 / 2 * N ^ (1 : ℝ)) :
    P * (K ^ 4 * N ^ (2 * U')) * N ^ (-(9 * U' + 1)) ≤ 1 / 2 := by
  have hN0 : 0 < N := by linarith
  have e : N ^ (2 * U') * N ^ (-(9 * U' + 1)) = N ^ (2 * U' + -(9 * U' + 1)) := by
    rw [← Real.rpow_add hN0]
  have hle : N ^ (2 * U' + -(9 * U' + 1)) ≤ N ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h1 : N ^ (1 : ℝ) * N ^ (-1 : ℝ) = 1 := by rw [← Real.rpow_add hN0]; simp
  calc P * (K ^ 4 * N ^ (2 * U')) * N ^ (-(9 * U' + 1))
      = P * K ^ 4 * (N ^ (2 * U') * N ^ (-(9 * U' + 1))) := by ring
    _ = P * K ^ 4 * N ^ (2 * U' + -(9 * U' + 1)) := by rw [e]
    _ ≤ (1 / 2 * N ^ (1 : ℝ)) * N ^ (-1 : ℝ) :=
        mul_le_mul hPK hle (Real.rpow_nonneg hN0.le _) (by positivity)
    _ = 1 / 2 := by rw [mul_assoc, h1, mul_one]

theorem numeric_coeff {N P Pc K U' d B : ℝ} (hN : 1 ≤ N) (hU' : 0 ≤ U') (hd1 : d ≤ 1)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hPc : Pc ≤ P * (N ^ (d * U')) ^ 6) (hPc0 : 0 ≤ Pc)
    (hPB : B * P * K ^ 4 ≤ 1 * N ^ (1 : ℝ)) :
    B * Pc * (K ^ 4 * N ^ (2 * U')) * N ^ (-(9 * U' + 1)) ≤ N ^ (-U') := by
  have hN0 : 0 < N := by linarith
  have hP : 0 ≤ P * (N ^ (d * U')) ^ 6 := hPc0.trans hPc
  have e : (N ^ (d * U')) ^ 6 * N ^ (2 * U') * N ^ (-(9 * U' + 1)) =
      N ^ (6 * (d * U') + 2 * U' + -(9 * U' + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
      ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  have hle : N ^ (6 * (d * U') + 2 * U' + -(9 * U' + 1)) ≤ N ^ (-1 + -U') :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have h1 : N ^ (1 : ℝ) * N ^ (-1 + -U') = N ^ (-U') := by
    rw [← Real.rpow_add hN0]; ring_nf
  calc B * Pc * (K ^ 4 * N ^ (2 * U')) * N ^ (-(9 * U' + 1))
      ≤ B * (P * (N ^ (d * U')) ^ 6) * (K ^ 4 * N ^ (2 * U')) * N ^ (-(9 * U' + 1)) := by
        gcongr
    _ = B * P * K ^ 4 * ((N ^ (d * U')) ^ 6 * N ^ (2 * U') * N ^ (-(9 * U' + 1))) := by ring
    _ = B * P * K ^ 4 * N ^ (6 * (d * U') + 2 * U' + -(9 * U' + 1)) := by rw [e]
    _ ≤ (1 * N ^ (1 : ℝ)) * N ^ (-1 + -U') := by
        refine mul_le_mul hPB hle (Real.rpow_nonneg hN0.le _) (by positivity)
    _ = N ^ (-U') := by rw [one_mul, h1]

variable {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ}

namespace GoodFrames

variable (gf : GoodFrames D s₀ U' e₀') (p : Parameters D)
include p

/-- At late indices the frame is good, its range is large, and its slope
bounds hold at every grid level with the slope constant of the index. -/
theorem eventually_slopes (hs₀ : 0 < s₀) (hU' : 0 < U') {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hA : BoxCalibration A₀) (hcaps : FrameCapsEventually D s₀ U' (9 * U' + 2)) (R' : ℝ) :
    ∀ᶠ k in atTop, ∃ f : Frame D k s₀ U', gf.fr k = some f ∧
      ∃ Rk θ K₂ : ℝ, FrameGood f Rk θ K₂ e₀' ∧ R' ≤ Rk ∧
        20 * D.K k ^ 3 * K₂ * f.H / θ ≤ max 1 (gf.slopeK A₀ k) ∧
        ∀ h ≤ f.m, FrameSlopes f h (max 1 (gf.slopeK A₀ k)) := by
  have hN1 := N_one p
  have hN0 : ∀ k, 0 ≤ D.N k := fun k => by linarith [hN1 k]
  have hNt := p.scale_limit
  have hA₀0 : 0 ≤ A₀ := by linarith
  have hK := small_K p
  have hH := gf.small_Hk p
  have hθ := gf.small_θinv p
  have hbK := gf.small_boxK p
  have hC := gf.small_capC p
  have hH2 : Small D.N (fun k => 4 * gf.Hk k + 2) :=
    ((Small.const hNt (by norm_num : (0 : ℝ) ≤ 4)).mul hN0 hH).add hNt
      (Small.const hNt (by norm_num))
  have hH6 : Small D.N (fun k => 4 * gf.Hk k + 6) :=
    ((Small.const hNt (by norm_num : (0 : ℝ) ≤ 4)).mul hN0 hH).add hNt
      (Small.const hNt (by norm_num))
  have hP1 := Small.calib hN1 hNt hA₀0 hbK hC hH2 hK hθ (Small.const hNt zero_le_one)
  have hP2 := Small.calib hN1 hNt hA₀0 hbK hC hH6 hK hθ (gf.small_Ngap p p.dimension_nonneg)
  have ev1 := (hP1.mul hN0 (hK.pow hN0 hNt 4)).le_mul_rpow hNt (by norm_num : (0 : ℝ) < 1 / 2)
    one_pos
  have ev3 := (hP2.mul hN0 (hK.pow hN0 hNt 4)).le_mul_rpow hNt (by norm_num : (0 : ℝ) < 1 / 2)
    one_pos
  have hB : Small D.N (fun k => 3 * (1 + boxK (D.K k) (gf.K₂ k)) * 2 * gf.Hk k) :=
    (((Small.const hNt (by norm_num : (0 : ℝ) ≤ 3)).mul hN0
      ((Small.const hNt zero_le_one).add hNt hbK)).mul hN0
      (Small.const hNt (by norm_num : (0 : ℝ) ≤ 2))).mul hN0 hH
  have ev2 := ((hB.mul hN0 hP1).mul hN0 (hK.pow hN0 hNt 4)).le_mul_rpow hNt one_pos one_pos
  have evH := hH.le_mul_rpow hNt (by norm_num : (0 : ℝ) < 1 / 4) hs₀
  filter_upwards [gf.eventually_some, gf.Rk_large R', hcaps, ev1, ev2, ev3,
    gf.θ_large 1 one_pos, evH] with k ⟨f, hf⟩ hRk hcapk h1 h2 h3 hθk hHk
  have hg := gf.good k f hf
  have hHf := Hk_eq hf
  have hmf := steps_eq hf
  have hgf := gap_eq hf
  have hNk := hN1 k
  have hNpos : 0 < D.N k := by linarith
  have hK1 : 1 ≤ D.K k := hg.K_ge
  have hK₂1 : 1 ≤ gf.K₂ k := hg.K₂_ge
  have hθpos : 0 < gf.θ k := hg.θ_pos
  have hH1 : 1 ≤ f.H := hg.H_ge
  have hbK0 : 0 ≤ boxK (D.K k) (gf.K₂ k) := by unfold boxK; positivity
  have hCr : 0 < 27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / gf.θ k) := by positivity
  have hd1 : D.d ≤ 1 := p.dimension_lt_one.le
  refine ⟨f, hf, gf.Rk k, gf.θ k, gf.K₂ k, hg, hRk, ?_, ?_⟩
  · rw [← hHf]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · intro h hh
    have hq : f.H * f.a₀ ≤ 1 / 4 := by
      have ha : f.a₀ = D.N k ^ (-s₀) := by rw [Frame.a₀, hg.depth_zero]
      rw [ha, ← hHf]
      have h4 : D.N k ^ s₀ * D.N k ^ (-s₀) = 1 := by rw [← Real.rpow_add hNpos]; simp
      calc gf.Hk k * D.N k ^ (-s₀) ≤ 1 / 4 * D.N k ^ s₀ * D.N k ^ (-s₀) :=
            mul_le_mul_of_nonneg_right hHk (Real.rpow_nonneg hNpos.le _)
        _ = 1 / 4 := by rw [mul_assoc, h4, mul_one]
    have hcapsf := hcapk f (gf.Rk k) (gf.θ k) (gf.K₂ k) e₀' hg hθk hq
    have hR1 : (9 * U' + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hc : ∀ Φ Y : ℝ, 0 ≤ Φ → 0 ≤ 16 * (8 * boxK (D.K k) (gf.K₂ k) + 4) *
        (27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / gf.θ k)) * Φ * D.K k ^ 5 /
          gf.θ k ^ 2 := fun Φ _ hΦ => by positivity
    have hP1f : passA A₀ (boxK (D.K k) (gf.K₂ k)) (27 * (6 * D.K k + 5) * D.K k *
        (D.K k ^ 3 / gf.θ k)) (4 * f.H + 2) (D.K k) (gf.θ k) (D.N k ^ (D.d * U')) ≤
        passA A₀ (boxK (D.K k) (gf.K₂ k)) (27 * (6 * D.K k + 5) * D.K k *
          (D.K k ^ 3 / gf.θ k)) (4 * f.H + 2) (D.K k) (gf.θ k) 1 *
          (D.N k ^ (D.d * U')) ^ 6 :=
      passA_le_mul_pow hA₀0 hbK0 (hc _ 0 (by linarith))
        (Real.one_le_rpow hNk (mul_nonneg p.dimension_nonneg hU'.le))
    have hP1nn : 0 ≤ passA A₀ (boxK (D.K k) (gf.K₂ k)) (27 * (6 * D.K k + 5) * D.K k *
        (D.K k ^ 3 / gf.θ k)) (4 * f.H + 2) (D.K k) (gf.θ k) 1 :=
      passA_nonneg hA₀0 hbK0 hCr.le (by linarith) (by linarith) zero_le_one
    have hPcnn : 0 ≤ passA A₀ (boxK (D.K k) (gf.K₂ k)) (27 * (6 * D.K k + 5) * D.K k *
        (D.K k ^ 3 / gf.θ k)) (4 * f.H + 2) (D.K k) (gf.θ k) (D.N k ^ (D.d * U')) :=
      passA_nonneg hA₀0 hbK0 hCr.le (by linarith) (by linarith) (by positivity)
    have hP2nn : 0 ≤ passA A₀ (boxK (D.K k) (gf.K₂ k)) (27 * (6 * D.K k + 5) * D.K k *
        (D.K k ^ 3 / gf.θ k)) (4 * f.H + 6) (D.K k) (gf.θ k)
          (D.N k ^ (D.d * (U' / f.m))) :=
      passA_nonneg hA₀0 hbK0 hCr.le (by linarith) (by linarith) (by positivity)
    simp only [capC, hHf] at h1 h2 h3
    rw [hgf] at h3
    have hc1 := numeric_crude hNk hU'.le hd1 hP1nn (by linarith) h1
    have hc1' : passA A₀ (boxK (D.K k) (gf.K₂ k)) (27 * (6 * D.K k + 5) * D.K k *
        (D.K k ^ 3 / gf.θ k)) (4 * f.H + 2) (D.K k) (gf.θ k) (D.N k ^ (D.d * U')) *
        (D.K k ^ 4 * D.N k ^ (2 * U')) * D.N k ^ (-(8 * U' + 1)) ≤ 1 / 2 := by
      refine le_trans ?_ hc1
      gcongr
    have hc2 := numeric_coeff (B := 3 * (1 + boxK (D.K k) (gf.K₂ k)) * 2 * f.H) (K := D.K k)
      hNk hU'.le hd1 (by positivity) (by linarith) hP1f hPcnn (by linarith)
    have hc2' : 3 * (1 + boxK (D.K k) (gf.K₂ k)) * (passA A₀ (boxK (D.K k) (gf.K₂ k))
        (27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / gf.θ k)) (4 * f.H + 2) (D.K k)
        (gf.θ k) (D.N k ^ (D.d * U')) * (2 * f.H)) * (D.K k ^ 4 * D.N k ^ (2 * U')) *
        D.N k ^ (-(9 * U' + 1)) ≤ D.N k ^ (-U') := by
      refine le_of_eq_of_le ?_ hc2
      ring
    have hc3 := numeric_fine hNk hU'.le hP2nn (by linarith) h3
    have hsl := hg.frameSlopes p.rate_le_one hA₀ hA hCr hcapsf
      (r₁ := 8 * U' + 1) (r₂ := 9 * U' + 1) (hR1.trans (by linarith)) (by linarith)
      (hR1.trans (by linarith)) (by linarith) (by linarith) hc1' hc2' hc3 hh
    refine hsl.mono hNpos.le (le_trans ?_ (le_max_right _ _))
    simp only [slopeK, capC, hHf, hmf, hgf]
    exact le_max_right _ _

/-- The residual atlas on good frames, for every loss sequence eventually above
the (subpower) atlas constant. -/
theorem residual_atlas (hs₀ : 0 < s₀) (hU' : 0 < U') {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hA : BoxCalibration A₀) (hcaps : FrameCapsEventually D s₀ U' (9 * U' + 2))
    (K' : ℕ → ℝ) (hK' : ∀ᶠ k in atTop, gf.atlasK A₀ k ≤ K' k) :
    (residualData D s₀ U' e₀' K' gf.fr).Atlas := by
  refine residualData_atlas (N_one p) p.dimension_nonneg p.rate_pos.le hU'
    (fun k f hf => (gf.good k f hf).m_pos) (fun k => max 1 (gf.slopeK A₀ k))
    (fun k => lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ ?_
  · filter_upwards [hK'] with k hk
    exact hk
  · intro R _
    exact gf.eventually_slopes p hs₀ hU' hA₀ hA hcaps R

/-- The residual nesting on good frames. -/
theorem residual_nested (hU' : 0 < U') (K' : ℕ → ℝ) :
    (residualData D s₀ U' e₀' K' gf.fr).Nested := by
  refine residualData_nested hU' (fun k f hf => (gf.good k f hf).m_pos) ?_
  filter_upwards [gf.eventually_some] with k ⟨f, hf⟩
  exact ⟨f, hf, _, _, _, gf.good k f hf⟩

end GoodFrames

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
