import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameRowBounds

/-!
# Priors and masses of the residual labels, as real ratios

The residual prior of a label is `ν(A') / ν(parent history)`, and the residual
law of a set is its core mass over `q₀ * ν(parent history)`. In these terms
the floor, ceiling, incidence mass and joint palette cap of a residual label
follow from the original ones at its depth and at the parent depth, from the
core floors, and from the prior floors they force.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

theorem FrameGood.measurableSet_hist (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.nl h)) (u : EntryHistory f.M h) : MeasurableSet (f.hist h i u) :=
  f.measurableSet_hist hg.bmeas h
    (fun h' hh' i' => ⟨(hg.meas h' (hh'.trans hh) i').1, (hg.meas h' (hh'.trans hh) i').2.1⟩) i u

theorem FrameGood.measurableSet_parent (hg : FrameGood f Rk θ K₂ e₀') :
    MeasurableSet f.parentSet :=
  hg.measurableSet_hist (Nat.zero_le _) f.i₀ f.u₀

/-- The residual prior as a real ratio. -/
theorem FrameGood.cond_eq (hg : FrameGood f Rk θ K₂ e₀') {S : Set α} (hS : MeasurableSet S)
    (hSP : S ⊆ f.parentSet) :
    cond (D.ν k) f.parentSet S =
      ENNReal.ofReal ((D.ν k).real S / (D.ν k).real f.parentSet) := by
  have := hg.νprob
  have hP := hg.parent_pos
  have hPr : 0 < (D.ν k).real f.parentSet := ENNReal.toReal_pos hP.ne' hg.parent_ne_top
  rw [cond_apply hg.measurableSet_parent, inter_eq_right.mpr hSP,
    ← ofReal_measureReal (μ := D.ν k) (s := S), ← ofReal_measureReal (μ := D.ν k)
    (s := f.parentSet), ← ENNReal.ofReal_inv_of_pos hPr, ← ENNReal.ofReal_mul (by positivity),
    div_eq_inv_mul]

/-- Real form of the prior floor of a retained node. -/
theorem FrameGood.prior_floor_real (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.nl h)) (u : EntryHistory f.M h) (hne : (f.event h i u ∩ f.core).Nonempty) :
    θ * (D.ν k).real (D.A k (f.depth h) i) ≤ D.K k * (D.ν k).real (f.hist h i u) := by
  have := hg.νprob
  have h1 := hg.prior_floor hh i u hne
  rw [← ofReal_measureReal (μ := D.ν k), ← ofReal_measureReal (μ := D.ν k),
    ← ENNReal.ofReal_mul hg.θ_pos.le, ← ENNReal.ofReal_mul (by linarith [hg.K_ge]),
    ENNReal.ofReal_le_ofReal_iff (by have := hg.K_ge; positivity)] at h1
  exact h1

/-- Real form of the original floor and ceiling. -/
theorem FrameGood.floor_real (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.nl h)) :
    (D.N k ^ (-f.depth h)) ^ D.d * f.ql h ^ 2 * D.N k ^ (-D.ℓ * f.depth h) / D.K k ≤
      (D.ν k).real (D.A k (f.depth h) i) := by
  have := hg.νprob
  have h1 := hg.floor h hh i
  rw [← ofReal_measureReal (μ := D.ν k), ENNReal.ofReal_le_ofReal_iff measureReal_nonneg] at h1
  exact h1

theorem FrameGood.ceil_real (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.nl h)) :
    (D.ν k).real (D.A k (f.depth h) i) ≤
      D.K k * (D.N k ^ (-f.depth h)) ^ D.d * f.ql h ^ 2 * D.N k ^ (-D.ℓ * f.depth h) := by
  have := hg.νprob
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have h1 := hg.ceil h hh i
  rw [← ofReal_measureReal (μ := D.ν k), ENNReal.ofReal_le_ofReal_iff (by
    have := hg.K_ge; have := f.ql_pos h; positivity)] at h1
  exact h1

/-- The original label scale at a grid depth factors through the parent depth. -/
theorem FrameGood.scale_factor (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    (D.N k ^ (-f.depth h)) ^ D.d * f.ql h ^ 2 * D.N k ^ (-D.ℓ * f.depth h) =
      ((D.N k ^ (-f.depth 0)) ^ D.d * f.ql 0 ^ 2 * D.N k ^ (-D.ℓ * f.depth 0)) *
        ((D.N k ^ (-((h : ℝ) * (U' / f.m)))) ^ D.d * ((2 : ℝ) ^ (-(f.resT h : ℤ))) ^ 2 *
          D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m)))) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  rw [hg.resq hh, ← f.q₀_eq, hg.ℓ_eq, hg.depth_eq hh, hg.depth_zero]
  have hq := f.q₀_pos
  have e1 : D.N k ^ (-(s₀ + (h : ℝ) * (U' / f.m))) =
      D.N k ^ (-s₀) * D.N k ^ (-((h : ℝ) * (U' / f.m))) := by
    rw [← Real.rpow_add hN]; ring_nf
  have e2 : D.N k ^ (-D.κ * (s₀ + (h : ℝ) * (U' / f.m))) =
      D.N k ^ (-D.κ * s₀) * D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) := by
    rw [← Real.rpow_add hN]; ring_nf
  rw [e1, e2, Real.mul_rpow (by positivity) (by positivity)]
  field_simp

/-- The residual floor of a retained label. -/
theorem FrameGood.res_floor (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) :
    ENNReal.ofReal ((D.N k ^ (-((h : ℝ) * (U' / f.m)))) ^ D.d *
        ((2 : ℝ) ^ (-(f.resT h : ℤ))) ^ 2 * D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) /
          (D.K k ^ 3 / θ)) ≤
      cond (D.ν k) f.parentSet ((f.level h).A i) := by
  have := hg.νprob
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hK : 1 ≤ D.K k := hg.K_ge
  have hθ := hg.θ_pos
  set oi := (f.node h i).1
  obtain ⟨-, hhist⟩ := hg.inside hh i
  have hA' : MeasurableSet ((f.level h).A i) := hg.measurableSet_hist hh _ _
  rw [hg.cond_eq hA' hhist]
  apply ENNReal.ofReal_le_ofReal
  have hpr := hg.prior_floor_real hh oi _ (f.node_retained h i)
  have hfl := hg.floor_real hh oi
  have hP : (D.ν k).real f.parentSet ≤ (D.ν k).real (D.A k (f.depth 0) f.i₀) :=
    measureReal_mono (f.hist_subset_A 0 f.i₀ f.u₀)
  have hce := hg.ceil_real (Nat.zero_le _) f.i₀
  have hPpos : 0 < (D.ν k).real f.parentSet := ENNReal.toReal_pos hg.parent_pos.ne' hg.parent_ne_top
  rw [hg.scale_factor hh] at hfl
  set F₀ := (D.N k ^ (-f.depth 0)) ^ D.d * f.ql 0 ^ 2 * D.N k ^ (-D.ℓ * f.depth 0)
  set X := (D.N k ^ (-((h : ℝ) * (U' / f.m)))) ^ D.d * ((2 : ℝ) ^ (-(f.resT h : ℤ))) ^ 2 *
    D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m)))
  have hF₀ : 0 < F₀ := by have := f.ql_pos 0; positivity
  have hX : 0 ≤ X := by positivity
  rw [le_div_iff₀ hPpos, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  -- θ * (F₀ * X / K) ≤ θ * ν(A_oi) ≤ K * ν(A') and ν(P) ≤ K * F₀
  have h1 : θ * (F₀ * X / D.K k) ≤ D.K k * (D.ν k).real ((f.level h).A i) :=
    (mul_le_mul_of_nonneg_left hfl hθ.le).trans hpr
  have h2 : (D.ν k).real f.parentSet ≤ D.K k * F₀ := by
    have := hP.trans hce; simpa [F₀, mul_assoc] using this
  have hKpos : 0 < D.K k := by linarith
  calc
    X * (D.ν k).real f.parentSet ≤ X * (D.K k * F₀) := mul_le_mul_of_nonneg_left h2 hX
    _ = D.K k ^ 2 / θ * (θ * (F₀ * X / D.K k)) := by field_simp
    _ ≤ D.K k ^ 2 / θ * (D.K k * (D.ν k).real ((f.level h).A i)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (D.ν k).real ((f.level h).A i) * (D.K k ^ 3 / θ) := by ring

/-- The residual ceiling of a retained label. -/
theorem FrameGood.res_ceil (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) :
    cond (D.ν k) f.parentSet ((f.level h).A i) ≤
      ENNReal.ofReal (D.K k ^ 3 / θ * (D.N k ^ (-((h : ℝ) * (U' / f.m)))) ^ D.d *
        ((2 : ℝ) ^ (-(f.resT h : ℤ))) ^ 2 * D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m)))) := by
  have := hg.νprob
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hK : 1 ≤ D.K k := hg.K_ge
  have hθ := hg.θ_pos
  set oi := (f.node h i).1
  obtain ⟨-, hhist⟩ := hg.inside hh i
  have hA' : MeasurableSet ((f.level h).A i) := hg.measurableSet_hist hh _ _
  rw [hg.cond_eq hA' hhist]
  apply ENNReal.ofReal_le_ofReal
  have hpr := hg.prior_floor_real (Nat.zero_le _) f.i₀ f.u₀ hg.parent_retained
  have hfl₀ := hg.floor_real (Nat.zero_le _) f.i₀
  have hce := hg.ceil_real hh oi
  have hsub : (D.ν k).real ((f.level h).A i) ≤ (D.ν k).real (D.A k (f.depth h) oi) :=
    measureReal_mono (f.hist_subset_A h oi _)
  have hPpos : 0 < (D.ν k).real f.parentSet := ENNReal.toReal_pos hg.parent_pos.ne' hg.parent_ne_top
  have hce' : (D.ν k).real (D.A k (f.depth h) oi) ≤ D.K k *
      ((D.N k ^ (-f.depth h)) ^ D.d * f.ql h ^ 2 * D.N k ^ (-D.ℓ * f.depth h)) := by
    simpa only [mul_assoc] using hce
  rw [hg.scale_factor hh] at hce'
  set F₀ := (D.N k ^ (-f.depth 0)) ^ D.d * f.ql 0 ^ 2 * D.N k ^ (-D.ℓ * f.depth 0)
  set X := (D.N k ^ (-((h : ℝ) * (U' / f.m)))) ^ D.d * ((2 : ℝ) ^ (-(f.resT h : ℤ))) ^ 2 *
    D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m)))
  have hF₀ : 0 < F₀ := by have := f.ql_pos 0; positivity
  have hX : 0 ≤ X := by positivity
  have hKpos : 0 < D.K k := by linarith
  rw [div_le_iff₀ hPpos]
  -- ν(P) ≥ θ * ν(A_i₀) / K ≥ θ * F₀ / K ^ 2
  have h1 : θ * (F₀ / D.K k) ≤ D.K k * (D.ν k).real f.parentSet :=
    (mul_le_mul_of_nonneg_left hfl₀ hθ.le).trans hpr
  calc
    (D.ν k).real ((f.level h).A i) ≤ D.K k * (F₀ * X) := hsub.trans hce'
    _ = D.K k ^ 3 / θ * X * (θ * (F₀ / D.K k)) / D.K k := by field_simp
    _ ≤ D.K k ^ 3 / θ * X * (D.K k * (D.ν k).real f.parentSet) / D.K k := by
      gcongr
    _ = D.K k ^ 3 / θ * X * (D.ν k).real f.parentSet := by field_simp
    _ = _ := by simp only [X]; ring

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
