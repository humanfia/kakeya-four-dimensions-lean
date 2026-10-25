/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/GoodFramesSmall.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.GoodFrames
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.Model

/-!
# The constants of good frames are subpower

The calibration constants, the slope constant and the atlas constant of a
good frame sequence are subpower, and the slope passes' calibration constants
grow at most by the sixth power of their scalar factor.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

theorem Small.congr {N x y : ℕ → ℝ} (h : Small N x) (e : ∀ k, x k = y k) : Small N y := by
  have : x = y := funext e
  rwa [← this]

theorem Small.calib {N : ℕ → ℝ} (hN1 : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    {A₀ : ℝ} (hA₀ : 0 ≤ A₀) {bK Cr Φ K θ Y : ℕ → ℝ} (hbK : Small N bK) (hCr : Small N Cr)
    (hΦ : Small N Φ) (hK : Small N K) (hθ : Small N (fun k => (θ k)⁻¹)) (hY : Small N Y) :
    Small N (fun k => passA A₀ (bK k) (Cr k) (Φ k) (K k) (θ k) (Y k)) := by
  have hN0 : ∀ k, 0 ≤ N k := fun k => by linarith [hN1 k]
  have h1 : Small N (fun k => (1 + bK k) ^ A₀) :=
    ((Small.const hNt zero_le_one).add hNt hbK).rpow hN1 hA₀
  have h8 : Small N (fun k => 8 * bK k + 4) :=
    ((Small.const hNt (by norm_num : (0 : ℝ) ≤ 8)).mul hN0 hbK).add hNt
      (Small.const hNt (by norm_num))
  have hin : Small N (fun k => 16 * (8 * bK k + 4) * Cr k * Φ k * K k ^ 5 *
      (θ k)⁻¹ ^ 2 * Y k) :=
    ((((((Small.const hNt (by norm_num : (0 : ℝ) ≤ 16)).mul hN0 h8).mul hN0 hCr).mul hN0
      hΦ).mul hN0 (hK.pow hN0 hNt 5)).mul hN0 (hθ.pow hN0 hNt 2)).mul hN0 hY
  have h6 : Small N (fun k => (1 + 16 * (8 * bK k + 4) * Cr k * Φ k * K k ^ 5 *
      (θ k)⁻¹ ^ 2 * Y k) ^ 6) :=
    ((Small.const hNt zero_le_one).add hNt hin).pow hN0 hNt 6
  refine (((Small.const hNt hA₀).mul hN0 h1).mul hN0 h6).congr fun k => ?_
  simp only [passA, div_eq_mul_inv, inv_pow]

/-- The calibration constant at scalar factor `Y ≥ 1` is at most the one at
`1` times `Y ^ 6`. -/
theorem passA_le_mul_pow {A₀ bK Cr Φ K θ Y : ℝ} (hA₀ : 0 ≤ A₀) (hbK : 0 ≤ bK)
    (hc : 0 ≤ 16 * (8 * bK + 4) * Cr * Φ * K ^ 5 / θ ^ 2) (hY : 1 ≤ Y) :
    passA A₀ bK Cr Φ K θ Y ≤ passA A₀ bK Cr Φ K θ 1 * Y ^ 6 := by
  unfold passA
  set c := 16 * (8 * bK + 4) * Cr * Φ * K ^ 5 / θ ^ 2
  have h1 : 1 + c * Y ≤ (1 + c * 1) * Y := by nlinarith
  have h2 : (1 + c * Y) ^ 6 ≤ ((1 + c * 1) * Y) ^ 6 :=
    pow_le_pow_left₀ (by positivity) h1 6
  have h3 : 0 ≤ A₀ * (1 + bK) ^ A₀ := mul_nonneg hA₀ (Real.rpow_nonneg (by linarith) _)
  calc A₀ * (1 + bK) ^ A₀ * (1 + c * Y) ^ 6
      ≤ A₀ * (1 + bK) ^ A₀ * ((1 + c * 1) * Y) ^ 6 := mul_le_mul_of_nonneg_left h2 h3
    _ = A₀ * (1 + bK) ^ A₀ * (1 + c * 1) ^ 6 * Y ^ 6 := by ring

variable {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ}

namespace GoodFrames

variable (gf : GoodFrames D s₀ U' e₀') (p : Parameters D)
include p

theorem N_one (k : ℕ) : 1 ≤ D.N k := by linarith [p.scale k]

theorem small_K : Small D.N D.K :=
  ⟨Eventually.of_forall fun k => by linarith [p.subpower.1 k], p.subpower.2⟩

theorem small_K₂ : Small D.N gf.K₂ := by
  refine ⟨?_, gf.K₂_small⟩
  filter_upwards [gf.eventually_some] with k ⟨f, hf⟩
  linarith [(gf.good k f hf).K₂_ge]

theorem small_θinv : Small D.N (fun k => (gf.θ k)⁻¹) :=
  Small.inv_of_large gf.θ_large (fun k => by linarith [p.scale k])

theorem small_Hk : Small D.N gf.Hk := by
  refine ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [gf.eventually_some] with k ⟨f, hf⟩
    rw [Hk_eq hf]
    linarith [(gf.good k f hf).H_ge]
  · filter_upwards [gf.eventually_some, gf.H_small ε hε] with k ⟨f, hf⟩ hk
    rw [Hk_eq hf]
    exact hk f hf

theorem small_steps : Small D.N gf.steps := by
  refine ⟨Eventually.of_forall fun k => Nat.cast_nonneg _, fun ε hε => ?_⟩
  filter_upwards [gf.eventually_some, gf.steps_small ε hε] with k ⟨f, hf⟩ hk
  rw [steps_eq hf]
  linarith [hk f hf]

theorem gap_le (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, gf.gap k ≤ ε := by
  filter_upwards [gf.eventually_some, gf.gap_small ε hε] with k ⟨f, hf⟩ hk
  rw [gap_eq hf]
  exact hk f hf

theorem small_Ngap {c : ℝ} (hc : 0 ≤ c) : Small D.N (fun k => D.N k ^ (c * gf.gap k)) := by
  apply Small.rpow_of_exponent (N_one p)
  intro ε hε
  rcases hc.eq_or_lt with hc0 | hc0
  · subst hc0
    exact Eventually.of_forall fun k => by simp [hε.le]
  · filter_upwards [gf.gap_le p (ε / c) (by positivity)] with k hk
    calc c * gf.gap k ≤ c * (ε / c) := mul_le_mul_of_nonneg_left hk hc0.le
      _ = ε := by field_simp

theorem small_capC : Small D.N gf.capC := by
  have hN0 : ∀ k, 0 ≤ D.N k := fun k => by linarith [N_one p k]
  have hNt := p.scale_limit
  have hK := small_K p
  have h6 : Small D.N (fun k => 6 * D.K k + 5) :=
    ((Small.const hNt (by norm_num : (0 : ℝ) ≤ 6)).mul hN0 hK).add hNt
      (Small.const hNt (by norm_num))
  refine ((((Small.const hNt (by norm_num : (0 : ℝ) ≤ 27)).mul hN0 h6).mul hN0 hK).mul hN0
    ((hK.pow hN0 hNt 3).mul hN0 (gf.small_θinv p))).congr fun k => ?_
  simp only [capC, div_eq_mul_inv]

theorem small_boxK : Small D.N (fun k => boxK (D.K k) (gf.K₂ k)) := by
  have hN0 : ∀ k, 0 ≤ D.N k := fun k => by linarith [N_one p k]
  have hNt := p.scale_limit
  exact (((Small.const hNt (by norm_num : (0 : ℝ) ≤ 50)).mul hN0
    ((small_K p).pow hN0 hNt 4)).mul hN0 ((gf.small_K₂ p).pow hN0 hNt 2)).congr
    fun k => by simp only [boxK]

theorem small_slopeK {A₀ : ℝ} (hA₀ : 0 ≤ A₀) : Small D.N (gf.slopeK A₀) := by
  have hN1 := N_one p
  have hN0 : ∀ k, 0 ≤ D.N k := fun k => by linarith [hN1 k]
  have hNt := p.scale_limit
  have hK := small_K p
  have hK₂ := gf.small_K₂ p
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
  have hP1 := Small.calib hN1 hNt hA₀ hbK hC hH2 hK hθ (Small.const hNt zero_le_one)
  have hP2 := Small.calib hN1 hNt hA₀ hbK hC hH6 hK hθ (gf.small_Ngap p p.dimension_nonneg)
  have h2H : Small D.N (fun k => 2 * gf.Hk k) :=
    (Small.const hNt (by norm_num : (0 : ℝ) ≤ 2)).mul hN0 hH
  have hNg : Small D.N (fun k => D.N k ^ gf.gap k) :=
    (gf.small_Ngap p (c := 1) zero_le_one).congr fun k => by simp
  have hfirst : Small D.N (fun k => 20 * D.K k ^ 3 * gf.K₂ k * gf.Hk k / gf.θ k) :=
    (((((Small.const hNt (by norm_num : (0 : ℝ) ≤ 20)).mul hN0 (hK.pow hN0 hNt 3)).mul hN0
      hK₂).mul hN0 hH).mul hN0 hθ).congr fun k => by simp only [div_eq_mul_inv]
  have h13 : Small D.N (fun k => 3 + 13 * D.K k ^ 4 * gf.K₂ k ^ 2) :=
    (Small.const hNt (by norm_num)).add hNt
      (((Small.const hNt (by norm_num : (0 : ℝ) ≤ 13)).mul hN0 (hK.pow hN0 hNt 4)).mul hN0
        (hK₂.pow hN0 hNt 2))
  have hsecond := h13.mul hN0 ((hP1.mul hN0 h2H).add hNt
    ((gf.small_steps p).mul hN0 ((hP2.mul hN0 h2H).mul hN0
      (hNg.mul hN0 (hK.pow hN0 hNt 8)))))
  exact (hfirst.max hNt hsecond).congr fun k => rfl

theorem small_atlasK {A₀ : ℝ} (hA₀ : 0 ≤ A₀) : Small D.N (gf.atlasK A₀) := by
  have hN1 := N_one p
  have hN0 : ∀ k, 0 ≤ D.N k := fun k => by linarith [hN1 k]
  have hNt := p.scale_limit
  have hc : 0 ≤ 1 + D.d + D.κ + D.κ := by
    have := p.dimension_nonneg; have := p.rate_pos; linarith
  exact (((Small.const hNt zero_le_one).max hNt (gf.small_slopeK p hA₀)).mul hN0
    (gf.small_Ngap p hc)).congr fun k => rfl

end GoodFrames

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
