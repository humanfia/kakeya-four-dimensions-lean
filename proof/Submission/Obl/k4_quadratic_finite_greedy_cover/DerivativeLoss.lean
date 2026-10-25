-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/DerivativeLoss.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Candidates
import Submission.Obl.k4_quadratic_selector_sweep.Quadratic
import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set

/-- A quadratic's hidden derivative has an affine trace along every trajectory. -/
theorem trajectory_native_derivative_affine
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) (l : Trajectory) :
    ∃ a b : ℝ, ∀ t : ℝ,
      MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R) = a * t + b := by
  let b : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![l.2 0, l.2 1, l.2 2]
  let s : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5]
  obtain ⟨a, c, hc⟩ :=
    Submission.Obl.k4_quadratic_selector_sweep.quadratic_native_derivative_affine R hR b s
  refine ⟨a, c, ?_⟩
  intro t
  simpa [x, b, s, PiLp.add_apply, PiLp.smul_apply] using hc t

/-- If an affine function is large at one point of a block, its very small
sublevel occupies only a small fraction of that block. -/
theorem volume_affine_small_of_large_somewhere
    (a b l q M ε : ℝ) (hq : 0 < q) (hM : 0 < M) (hε : 0 ≤ ε) (hεM : ε ≤ M / 2)
    (hlarge : ∃ t₀ ∈ Icc l (l + q), M ≤ |a * t₀ + b|) :
    volume {t : ℝ | t ∈ Icc l (l + q) ∧ |a * t + b| < ε} ≤
      ENNReal.ofReal (8 * ε * q / M) := by
  obtain ⟨t₀, ht₀, hlarge⟩ := hlarge
  by_cases hsmall : |a| * q ≤ M / 2
  · have hempty : {t : ℝ | t ∈ Icc l (l + q) ∧ |a * t + b| < ε} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro t ⟨ht, hvalue⟩
      have hdist : |t₀ - t| ≤ q := abs_le.mpr ⟨by linarith [ht.2, ht₀.1], by linarith [ht.1, ht₀.2]⟩
      have htrace : |a * t₀ + b| ≤ |a * t + b| + |a| * q := by
        calc
          |a * t₀ + b| = |(a * t + b) + a * (t₀ - t)| := by congr 1; ring
          _ ≤ |a * t + b| + |a * (t₀ - t)| := abs_add_le _ _
          _ = |a * t + b| + |a| * |t₀ - t| := by rw [abs_mul]
          _ ≤ |a * t + b| + |a| * q :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hdist (abs_nonneg a))
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · have hbig : M / 2 < |a| * q := lt_of_not_ge hsmall
    have ha : 0 < |a| := by nlinarith [abs_nonneg a]
    let p : Polynomial ℝ := Polynomial.C a * Polynomial.X + Polynomial.C b
    have hdeg : p.natDegree ≤ 2 := Polynomial.natDegree_linear_le.trans (by omega)
    have hsub' : {t : ℝ | t ∈ Icc l (l + q) ∧ |a * t + b| < ε} ⊆
        {t : ℝ | |p.eval t| ≤ ε ∧ |a| ≤ |p.derivative.eval t|} := by
      intro t ht
      simpa [p] using (show |a * t + b| ≤ ε ∧ |a| ≤ |a| from ⟨ht.2.le, le_rfl⟩)
    calc
      _ ≤ volume {t : ℝ | |p.eval t| ≤ ε ∧ |a| ≤ |p.derivative.eval t|} := measure_mono hsub'
      _ ≤ ENNReal.ofReal (4 * ε / |a|) :=
        Submission.Lib.K4QuadraticSublevel.volume_quadratic_sublevel p hdeg hε ha
      _ ≤ ENNReal.ofReal (8 * ε * q / M) := by
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_div_iff₀ ha hM).mpr
        nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hbig) hε]

/-- The affine sublevel estimate integrated under the original trajectory prior.
It controls the counted mass lost when full trajectory assignments are enlarged. -/
theorem product_bad_derivative_le
    (ν : Measure Trajectory) (A : Set Trajectory) (hAm : MeasurableSet A)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (l q M ε : ℝ) (hq : 0 < q) (hM : 0 < M) (hε : 0 ≤ ε) (hεM : ε ≤ M / 2)
    (hlarge : ∀ a ∈ A, ∃ t ∈ Icc l (l + q),
      M ≤ |MvPolynomial.eval (x a t) (MvPolynomial.pderiv (3 : Fin 4) R)|) :
    ν.prod volume {p : Incidence | p.1 ∈ A ∧ p.2 ∈ Icc l (l + q) ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)| < ε} ≤
      ENNReal.ofReal (8 * ε * q / M) * ν A := by
  have hD : Continuous (fun p : Incidence =>
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) :=
    ((MvPolynomial.continuous_eval _).comp continuous_trajectory_point).abs
  let S : Set Incidence := {p | p.1 ∈ A ∧ p.2 ∈ Icc l (l + q) ∧
    |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)| < ε}
  have hSm : MeasurableSet S := by
    have ht : MeasurableSet {p : Incidence | p.2 ∈ Icc l (l + q)} :=
      measurableSet_Icc.preimage measurable_snd
    have hd : MeasurableSet {p : Incidence |
        |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)| < ε} :=
      measurableSet_lt hD.measurable measurable_const
    simpa only [S, Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage] using
      (hAm.preimage measurable_fst).inter (ht.inter hd)
  change ν.prod volume S ≤ _
  rw [Measure.prod_apply hSm]
  calc
    _ ≤ ∫⁻ a, A.indicator (fun _ => ENNReal.ofReal (8 * ε * q / M)) a ∂ν := by
      apply lintegral_mono
      intro a
      by_cases ha : a ∈ A
      · rw [Set.indicator_of_mem ha]
        obtain ⟨c, b, hc⟩ := trajectory_native_derivative_affine R hR a
        have hbig : ∃ t ∈ Icc l (l + q), M ≤ |c * t + b| := by
          simpa only [hc] using hlarge a ha
        simpa only [S, preimage_ofPred_eq, ha, true_and, hc] using
          volume_affine_small_of_large_somewhere c b l q M ε hq hM hε hεM hbig
      · simp [S, ha]
    _ = ENNReal.ofReal (8 * ε * q / M) * ν A := by
      rw [lintegral_indicator hAm, lintegral_const, Measure.restrict_apply_univ]

/-- A counted incidence floor on a whole time block gives the corresponding
trajectory-mass floor after cancelling the original time length. -/
theorem trajectory_floor_of_product_floor
    (ν : Measure Trajectory) (A S : Set Trajectory) (F : Set Incidence)
    (l q θ : ℝ) (hq : 0 < q) (hθ : 0 ≤ θ)
    (hF : F ⊆ S ×ˢ Icc l (l + q))
    (hfloor : ENNReal.ofReal (θ * q) * ν A ≤ ν.prod volume F) :
    ENNReal.ofReal θ * ν A ≤ ν S := by
  have hbnd : ν.prod volume F ≤ ν S * ENNReal.ofReal q := by
    apply (measure_mono hF).trans_eq
    rw [Measure.prod_prod, Real.volume_Icc, add_sub_cancel_left]
  have hprod : (ENNReal.ofReal θ * ν A) * ENNReal.ofReal q ≤ ν S * ENNReal.ofReal q := by
    calc
      _ = ENNReal.ofReal (θ * q) * ν A := by rw [ENNReal.ofReal_mul hθ]; ac_rfl
      _ ≤ ν.prod volume F := hfloor
      _ ≤ _ := hbnd
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hq).ne'
    ENNReal.ofReal_ne_top).mp hprod

/-- The original candidate witness forces a positive fraction of the old full
trajectory assignment, with its actual-gain exponent preserved. -/
theorem candidate_trajectory_floor_of_gain_le
    (Nk L : ℝ) (W C : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε hmax : ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (a : CandidateDatum C)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁) (hgain : a.gain ≤ hmax)
    (hc : CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H a) :
    ENNReal.ofReal (Nk ^ (-((d₁ * hmax + ρ * gain) * L) - ε)) *
      ν (γ a.parent) (A a.parent) ≤ ν (γ a.parent) a.trajectories := by
  let θ := Nk ^ (-((d₁ * hmax + ρ * gain) * L) - ε)
  let q := 1 / (2 : ℝ) ^ T (lev a.parent)
  let l := (j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent)
  have hq : 0 < q := by dsimp [q]; positivity
  have hθ : 0 ≤ θ := Real.rpow_nonneg (le_trans zero_le_one hN) _
  have hi : ((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent) = l + q := by
    dsimp [l, q]
    ring
  have hsub : a.counted ⊆ a.trajectories ×ˢ Icc l (l + q) := by
    intro p hp
    have hpt := hc.2.2.1 p hp
    exact ⟨hpt.1, by simpa only [hi] using hpt.2.1⟩
  have hfloor : ENNReal.ofReal (θ * q) * ν (γ a.parent) (A a.parent) ≤
      (ν (γ a.parent)).prod volume a.counted := by
    calc
      _ = ENNReal.ofReal θ *
          (ν (γ a.parent)).prod volume (packetRegion T lev j A a.parent) := by
        rw [packetRegion_measure, ENNReal.ofReal_mul hθ]
        dsimp [q]
        ac_rfl
      _ ≤ _ := candidate_relative_floor_of_gain_le Nk L W C ν B d₁ ρ gain ε hmax
        T lev γ j A H a hN hL hd₁ hgain hc
  exact trajectory_floor_of_product_floor (ν (γ a.parent)) (A a.parent) a.trajectories
    a.counted l q θ hq hθ hsub hfloor

end Submission.Obl.k4_quadratic_finite_greedy_cover
