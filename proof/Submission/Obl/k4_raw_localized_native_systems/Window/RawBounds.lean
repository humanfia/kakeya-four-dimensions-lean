import Submission.Obl.k4_raw_localized_native_systems.Window.RawLaws

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Lib.K4ChartLifting (Frame)

noncomputable section

variable {p : Data} {k : ℕ}

theorem native_bounds_ae {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    (H : Set Point) (hHm : MeasurableSet H) (hHsub : H ⊆ p.E k γ) :
    ∀ᵐ q ∂(priorMass p k γ).restrict H,
      |MvPolynomial.eval (x q.1 q.2) (p.P k γ)| ≤ p.K k ∧
      |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ))| ≤
        p.K k * p.B k γ ∧
      |MvPolynomial.eval (x q.1 q.2)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ)))| ≤
        p.K k * p.B k γ ^ 2 := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  rcases (hfmt k).2.2.2.1 γ with
    ⟨hprob, hB, hBmax, hBinv, hPdeg, hcoeff, hrepr, hE, hEsub,
      hsupp, hformat, hwhole, hsel⟩
  have hprod := (Measure.quasiMeasurePreserving_fst (μ := p.ν k γ)
    (ν := (volume : Measure ℝ))).ae hwhole
  have hrestr : ∀ᵐ q ∂(priorMass p k γ).restrict H,
      ∀ t ∈ Icc (0 : ℝ) 1,
      ‖y q.1 t‖ + ‖v q.1‖ ≤ p.K k ∧
      |MvPolynomial.eval (x q.1 t) (p.P k γ)| ≤ p.K k ∧
      |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ))| ≤
        p.K k * p.B k γ ∧
      |MvPolynomial.eval (x q.1 t)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ)))| ≤
        p.K k * p.B k γ ^ 2 := ae_restrict_of_ae hprod
  filter_upwards [hrestr, ae_restrict_mem hHm] with q hq hqH
  exact (hq q.2 (hEsub (hHsub hqH)).2).2

theorem earlierCoordinates_eq_normPt (F : Frame) (B : ℝ)
    (z : EuclideanSpace ℝ (Fin 4)) :
    earlierCoordinates F.t₀ F.q B F.c F.u F.D z =
      WithLp.toLp 2 (normPt F B (fun i => z i)) := by
  ext i
  fin_cases i <;>
    simp [earlierCoordinates, rawPlanar, normPt, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

theorem continuous_earlierCoordinates (F : Frame) (B : ℝ) :
    Continuous (earlierCoordinates F.t₀ F.q B F.c F.u F.D) := by
  have heq := funext (earlierCoordinates_eq_normPt F B)
  rw [heq]
  exact (PiLp.continuous_toLp 2 _).comp
    ((continuous_normPt F B).comp (PiLp.continuous_ofLp 2 _))

theorem earlierCoordinates_rawGraph (W : Atlas p k) (e : Fin W.C) (q : Point) :
    earlierCoordinates ((W.j e : ℝ) / (2 : ℝ) ^ W.T) (1 / (2 : ℝ) ^ W.T)
      (p.B k (W.γ e)) (W.c e) (W.u e) (W.Q e) (rawGraph q) = wz W e q := by
  exact earlierCoordinates_eq_normPt (chartFrame W e) _ _

/-- The raw earlier graph law retains the original test and native-signal bounds. -/
theorem rawLaw_bounds (hp : Valid p) {W : Atlas p k} {e : Fin W.C} {M D : ℕ}
    {H : Fin W.C → Set Point} {κ r K : ℝ}
    (hW : WChart p k W M D κ r e) (hHm : MeasurableSet (H e)) (hHsub : H e ⊆ W.F e)
    (hnat : ∀ᵐ q ∂(priorMass p k (W.γ e)).restrict (H e), |MvPolynomial.eval (x q.1 q.2) (p.P k (W.γ e))| ≤ K ∧
      |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e)))| ≤
        K * p.B k (W.γ e) ∧
      |MvPolynomial.eval (x q.1 q.2)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e))))| ≤
        K * p.B k (W.γ e) ^ 2) :
    ∀ᵐ z ∂rawLaw W H e,
      ‖base4 (earlierCoordinates ((W.j e : ℝ) / (2 : ℝ) ^ W.T) (1 / (2 : ℝ) ^ W.T)
        (p.B k (W.γ e)) (W.c e) (W.u e) (W.Q e) z)‖ ≤ 1 + κ ∧
      |MvPolynomial.eval (fun i => z i) (W.R e)| ≤ κ * δ (p.N k) r ∧
      p.B k (W.γ e) / κ ≤
        |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (W.R e))| ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (W.R e))| ≤
        κ * p.B k (W.γ e) ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (W.R e)))| ≤
        κ * p.B k (W.γ e) ^ 2 / δ (p.N k) r ∧
      |MvPolynomial.eval (fun i => z i) (p.P k (W.γ e))| ≤ K ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e)))| ≤
        K * p.B k (W.γ e) ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e))))| ≤
        K * p.B k (W.γ e) ^ 2 := by
  have hset : MeasurableSet {z : EuclideanSpace ℝ (Fin 4) |
      ‖base4 (earlierCoordinates ((W.j e : ℝ) / (2 : ℝ) ^ W.T) (1 / (2 : ℝ) ^ W.T)
        (p.B k (W.γ e)) (W.c e) (W.u e) (W.Q e) z)‖ ≤ 1 + κ ∧
      |MvPolynomial.eval (fun i => z i) (W.R e)| ≤ κ * δ (p.N k) r ∧
      p.B k (W.γ e) / κ ≤
        |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (W.R e))| ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (W.R e))| ≤
        κ * p.B k (W.γ e) ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (W.R e)))| ≤
        κ * p.B k (W.γ e) ^ 2 / δ (p.N k) r ∧
      |MvPolynomial.eval (fun i => z i) (p.P k (W.γ e))| ≤ K ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e)))| ≤
        K * p.B k (W.γ e) ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e))))| ≤
        K * p.B k (W.γ e) ^ 2} := by
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 4) =>
        ‖base4 (earlierCoordinates ((W.j e : ℝ) / (2 : ℝ) ^ W.T) (1 / (2 : ℝ) ^ W.T)
          (p.B k (W.γ e)) (W.c e) (W.u e) (W.Q e) z)‖) :=
      (show Continuous base4 by unfold base4; fun_prop).comp
        (continuous_earlierCoordinates (chartFrame W e) _) |>.norm
    exact (measurableSet_le hcont.measurable measurable_const).inter
      ((measurableSet_abs_le _ _).inter ((measurableSet_le_abs _ _).inter
        ((measurableSet_abs_le _ _).inter ((measurableSet_abs_le _ _).inter
          ((measurableSet_abs_le _ _).inter ((measurableSet_abs_le _ _).inter
            (measurableSet_abs_le _ _)))))))
  rw [rawLaw, ae_map_iff measurable_rawGraph.aemeasurable hset]
  filter_upwards [ae_restrict_mem hHm, hnat] with q hq hnq
  obtain ⟨-, hqA, hqt, hfl⟩ := hW.sel (hHsub hq)
  obtain ⟨hfit, hR0, hR1, hR2⟩ := hW.fit hqA hqt
  obtain ⟨hP0, hP1, hP2⟩ := hnq
  exact ⟨by rw [earlierCoordinates_rawGraph]; exact norm_base4_wz_le W e q hqt hfit,
    hR0, hfl, hR1, hR2, hP0, hP1, hP2⟩

/-- Scalar slack inequalities convert the chart bounds to the exact raw certificate. -/
theorem rawLaw_ae (hp : Valid p) {W : Atlas p k} {e : Fin W.C} {M D : ℕ}
    {H : Fin W.C → Set Point} {κ r K χ s : ℝ}
    (hW : WChart p k W M D κ r e) (hHm : MeasurableSet (H e)) (hHsub : H e ⊆ W.F e)
    (hnat : ∀ᵐ q ∂(priorMass p k (W.γ e)).restrict (H e), |MvPolynomial.eval (x q.1 q.2) (p.P k (W.γ e))| ≤ K ∧
      |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e)))| ≤
        K * p.B k (W.γ e) ∧
      |MvPolynomial.eval (x q.1 q.2)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e))))| ≤
        K * p.B k (W.γ e) ^ 2)
    (hκ : 1 ≤ κ) (hscale : 1 + κ ≤ p.N k ^ χ) (hK : K ≤ p.N k ^ χ)
    (hvalue : κ * δ (p.N k) r ≤ p.N k ^ χ * p.N k ^ (-s + χ))
    (hcurv : κ / δ (p.N k) r ≤ p.N k ^ χ / p.N k ^ (-s + χ)) :
    ∀ᵐ z ∂rawLaw W H e,
      ‖base4 (earlierCoordinates ((W.j e : ℝ) / (2 : ℝ) ^ W.T) (1 / (2 : ℝ) ^ W.T)
        (p.B k (W.γ e)) (W.c e) (W.u e) (W.Q e) z)‖ ≤ p.N k ^ χ ∧
      |MvPolynomial.eval (fun i => z i) (W.R e)| ≤ p.N k ^ χ * p.N k ^ (-s + χ) ∧
      p.B k (W.γ e) * (p.N k ^ χ)⁻¹ ≤
        |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (W.R e))| ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (W.R e))| ≤
        p.B k (W.γ e) * p.N k ^ χ ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (W.R e)))| ≤
        p.B k (W.γ e) ^ 2 * (p.N k ^ χ / p.N k ^ (-s + χ)) ∧
      |MvPolynomial.eval (fun i => z i) (p.P k (W.γ e))| ≤ p.N k ^ χ ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e)))| ≤
        p.B k (W.γ e) * p.N k ^ χ ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e))))| ≤
        p.B k (W.γ e) ^ 2 * p.N k ^ χ := by
  have hκ0 : 0 < κ := by linarith
  have hκχ : κ ≤ p.N k ^ χ := by linarith
  have hB := (hp.B_pos k (W.γ e)).le
  filter_upwards [rawLaw_bounds hp hW hHm hHsub hnat] with z hz
  rcases hz with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨h0.trans hscale, h1.trans hvalue, ?_, ?_, ?_, h5.trans hK, ?_, ?_⟩
  · apply le_trans _ h2
    rw [div_eq_mul_inv]
    have hi : (p.N k ^ χ)⁻¹ ≤ κ⁻¹ := by
      simpa only [one_div] using (one_div_le_one_div_of_le hκ0 hκχ)
    exact mul_le_mul_of_nonneg_left hi hB
  · calc _ ≤ κ * p.B k (W.γ e) := h3
      _ ≤ p.N k ^ χ * p.B k (W.γ e) := mul_le_mul_of_nonneg_right hκχ hB
      _ = _ := mul_comm _ _
  · calc _ ≤ κ * p.B k (W.γ e) ^ 2 / δ (p.N k) r := h4
      _ = p.B k (W.γ e) ^ 2 * (κ / δ (p.N k) r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcurv (sq_nonneg _)
  · calc _ ≤ K * p.B k (W.γ e) := h6
      _ ≤ p.N k ^ χ * p.B k (W.γ e) := mul_le_mul_of_nonneg_right hK hB
      _ = _ := mul_comm _ _
  · calc _ ≤ K * p.B k (W.γ e) ^ 2 := h7
      _ ≤ p.N k ^ χ * p.B k (W.γ e) ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg _)
      _ = _ := mul_comm _ _

end
end Submission.Obl.k4_raw_localized_native_systems.Window
