import Submission.Obl.k4_horizon_chart_assembly.GroupGeometry
import Submission.Obl.k4_horizon_chart_assembly.Selections

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators
open Submission.Lib.K4FinitePlankAtlases (PhysicalPlank)

noncomputable section

/-- The scalar quantitative chart used before choosing the asymptotic budget. -/
def RawChart : ℝ → ℕ → ℝ → ℕ → ℝ → ℝ → ℝ → Set Incidence →
    Plane → Plane → Matrix (Fin 2) (Fin 2) ℝ → MvPolynomial (Fin 4) ℝ →
    Set Trajectory → Set Incidence → Prop → Prop :=
  (fun Hout D κ T j a Bv Ev c u Q R A F ex => Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ Hout ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Hout ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧ R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Hout) ∧ MeasurableSet A ∧ MeasurableSet F ∧ (∀ i, Fmt 6 (Hout) D {xl | (i, xl) ∈ A} ∧ Fmt 7 (Hout) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧ (∀ l ∈ A, (l.1 : ℝ) ≤ Hout ∧ (∀ e, |l.2 e| ≤ Hout) ∧ ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin Q⁻¹ (yl l t - c - t • u)‖ ≤ κ ∧ |MvPolynomial.eval (xl l t) R| ≤ κ * a ∧ |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv ∧ |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * Bv ^ 2 / a) ∧ (∀ p ∈ F, p ∈ Ev ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧ Bv / κ ≤ |MvPolynomial.eval (xl p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧ ex)

/-- At the dyadic problem scale and a power budget this is the frozen chart predicate. -/
theorem rawChart_as_chart {N κ j L B : ℝ} {M D T : ℕ}
    {E : Set Incidence} {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Trajectory} {F : Set Incidence} {ex : Prop}
    (h : RawChart (N ^ M) D κ T j (dl N L) B E c u Q R A F ex) :
    Chart N M D κ T j L B E c u Q R A F ex := h

/-- Enlarging the raw complexity budget and degree preserves every geometric
and original-law incidence condition. -/
theorem rawChart_mono {H H' κ j a B : ℝ} {D D' T : ℕ}
    {E : Set Incidence} {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Trajectory} {F : Set Incidence} {ex ex' : Prop}
    (hH : H ≤ H') (hD : D ≤ D')
    (h : RawChart H D κ T j a B E c u Q R A F ex) (hEx : ex → ex') :
    RawChart H' D' κ T j a B E c u Q R A F ex' := by
  obtain ⟨hd, hc, hq, he, hr, hcoeff, hA, hF, hf, hw, hs, hx⟩ := h
  refine ⟨hd, hc.trans hH, hq.trans hH, he, hr, fun e => (hcoeff e).trans hH,
    hA, hF, ?_, ?_, hs, hEx hx⟩
  · intro i
    exact ⟨Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hf i).1 hH hD,
      Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hf i).2 hH hD⟩
  · intro l hl
    have hh := hw l hl
    exact ⟨hh.1.trans hH, fun e => (hh.2.1 e).trans hH, hh.2.2⟩

/-- Exact conversion of one normalized greedy packet to the frozen chart.
The quantitative envelopes are separate elementary inequalities, so the same
conversion works for every loss exponent and every original probability law. -/
theorem packet_to_rawChart
    (ν : Measure Trajectory) [SFinite ν]
    (E : Set Incidence) (P : MvPolynomial (Fin 4) ℝ)
    (K H Hout B n0 R s mid q a κ τ₀ j : ℝ) (Dout D₀ T Dmesh m : ℕ)
    (hK : 1 ≤ K) (hH : 0 ≤ H) (hB : 0 < B)
    (hP : P.totalDegree ≤ 2) (hE : MeasurableSet E)
    (hEf : ∀ i, Fmt 7 H D₀ {z : Fin 7 → ℝ |
      ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ E})
    (hq : 0 < q) (ha : 0 < a) (ha1 : a ≤ 1) (hqa : q ≤ a)
    (hqT : q = ((2 : ℝ) ^ T)⁻¹)
    (hs : s = j / (2 : ℝ) ^ T)
    (hR : 2 * K + 2 ≤ R) (hmid : mid ∈ Icc (0 : ℝ) 1)
    (hblock : Icc s (s + q) ⊆ Icc (0 : ℝ) 1)
    (hnear : ∀ t ∈ Icc s (s + q), |t - mid| ≤ q)
    (Γ : (Fin 2 → ℤ) × ℤ) (ps : Fin m → PhysicalPlank Dmesh) (i : Fin m)
    (A : Set Trajectory)
    (hAeq : A = packetAssignment (nativeGroup P B K H mid q a Γ)
      (groupIntercept q a s (R * q) Γ) (groupVelocity q (R * q)) ps i)
    (c w : Plane) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.det ≠ 0)
    (hQentries : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ 16)
    (hfit : ∀ l ∈ A, ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin Q⁻¹
        (groupIntercept q a s (R * q) Γ l + τ • groupVelocity q (R * q) l - c - τ • w)‖ ≤ 2)
    (hfloor : ENNReal.ofReal ((τ₀ / 4) * |Q.det|) ≤
      (ν.prod volume) (normalizedEvent (derivativeEvent E P (B / K)) s q ∩ (A ×ˢ univ)))
    (hκR : 64 * R ≤ κ) (hκK : K ≤ κ)
    (htrue : 4 * n0 * (R * q) ^ 2 ≤ τ₀ * κ)
    (hHout : H ≤ Hout) (hDout : max D₀ 4 ≤ Dout)
    (hformat : H + 114 + 16 * (m : ℝ) ≤ Hout)
    (hcenter : ‖liftedBlockCenter (midpointGroupCenter q Γ) c w s q (R * q)‖ +
      ‖liftedBlockSpeed w q (R * q)‖ ≤ Hout)
    (hframe : (∑ e : Fin 2, ∑ e' : Fin 2,
      (|((R * q) • Q) e e'| + |((R * q) • Q)⁻¹ e e'|)) ≤ Hout)
    (hcoeff : ∀ e, |(shiftedTest P (a * (Γ.2 : ℝ))).coeff e| ≤ Hout) :
    RawChart Hout Dout κ T j a B E
      (liftedBlockCenter (midpointGroupCenter q Γ) c w s q (R * q))
      (liftedBlockSpeed w q (R * q)) ((R * q) • Q) (shiftedTest P (a * (Γ.2 : ℝ)))
      A (selectedEvent E A P (B / K) s q)
      (ENNReal.ofReal (n0 * |((R * q) • Q).det| / ((2 : ℝ) ^ T * κ)) ≤
        (ν.prod volume) (selectedEvent E A P (B / K) s q)) := by
  have hK₀ : 0 < K := zero_lt_one.trans_le hK
  have hκ : 0 < κ := hK₀.trans_le hκK
  have hR₀ : 0 < R := by linarith
  have hr : 0 < R * q := mul_pos hR₀ hq
  have hAU : A ⊆ nativeGroup P B K H mid q a Γ := by
    rw [hAeq]
    exact inter_subset_left
  have hAf (n : ℕ) : Fmt 6 (110 + 16 * (m : ℝ)) 4 {x | (n, x) ∈ A} := by
    rw [hAeq]
    apply fmt_of_signRep (packetAssignment_signRep _
      (nativeGroup_signRep P hP B mid hK₀.le hH hq ha Γ) q a s (R * q) Γ ps i n)
    norm_num
    ring_nf
    exact le_rfl
  have hAf' (n : ℕ) : Fmt 6 (Hout) Dout {x | (n, x) ∈ A} :=
    Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hAf n) (by linarith) (by omega)
  have hAm : MeasurableSet A := by
    apply measurableSet_indexed_polynomialFormat (N := Hout) (M := 1) (D := Dout)
    intro n
    simpa only [PolynomialFormat, pow_one] using hAf' n
  have hFf (n : ℕ) : Fmt 7 (Hout) Dout {z : Fin 7 → ℝ |
      ((n, fun e : Fin 6 => z e.castSucc), z 6) ∈ selectedEvent E A P (B / K) s q} := by
    have h := selectedEvent_format E A hEf hAf P hP (B / K) s q n
    exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono h (by linarith) (by omega)
  have hend : s + q = (j + 1) / (2 : ℝ) ^ T := by
    rw [hs, hqT]
    ring
  have hIeq : Icc s (s + q) = Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) := by
    rw [hend, hs]
  have hdet : ((R * q) • Q).det ≠ 0 := by
    apply abs_pos.mp
    rw [scaled_frame_abs_det hr.le]
    exact mul_pos (sq_pos_of_pos hr) (abs_pos.mpr hQ)
  have hentry : (∑ e : Fin 2, ∑ e' : Fin 2, |((R * q) • Q) e e'|) ≤ κ / (2 : ℝ) ^ T := by
    rw [scaled_frame_entries hr.le]
    have hmul := mul_le_mul_of_nonneg_left hQentries hr.le
    have hκq := mul_le_mul_of_nonneg_right hκR hq.le
    rw [div_eq_mul_inv, ← hqT]
    nlinarith
  have hfull (l : Trajectory) (hl : l ∈ A) :
      WholeBlockFit (shiftedTest P (a * (Γ.2 : ℝ))) ((R * q) • Q)
        (liftedBlockCenter (midpointGroupCenter q Γ) c w s q (R * q))
        (liftedBlockSpeed w q (R * q)) κ B a s (s + q) l.2 := by
    exact wholeBlockFit_mono hκR hB.le ha
      (nativeGroup_wholeBlockFit P hP B H s mid hK₀.le hq ha ha1 hqa hB hR
        hmid hblock hnear Γ (hAU hl) Q hQ c w (hfit l hl))
  have hEcut : MeasurableSet (derivativeEvent E P (B / K)) := hE.inter
    (Submission.Obl.k4_quadratic_atlas_normalization.measurableSet_derivativeFloorSet P (B / K))
  have hmass := normalized_incidence_mass ν hEcut hAm s hq
  rw [← selectedEvent_eq] at hmass
  have hsmall : n0 * (R * q) ^ 2 / κ ≤ τ₀ / 4 := by
    apply (div_le_iff₀ hκ).mpr
    nlinarith
  have hreal : n0 * |((R * q) • Q).det| / ((2 : ℝ) ^ T * κ) ≤
      q * ((τ₀ / 4) * |Q.det|) := by
    calc
      _ = (q * |Q.det|) * (n0 * (R * q) ^ 2 / κ) := by
        rw [scaled_frame_abs_det hr.le, hqT]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (q * |Q.det|) * (τ₀ / 4) :=
        mul_le_mul_of_nonneg_left hsmall (mul_nonneg hq.le (abs_nonneg _))
      _ = _ := by ring
  have htruefloor : ENNReal.ofReal (n0 * |((R * q) • Q).det| / ((2 : ℝ) ^ T * κ)) ≤
      (ν.prod volume) (selectedEvent E A P (B / K) s q) := by
    calc
      _ ≤ ENNReal.ofReal (q * ((τ₀ / 4) * |Q.det|)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal q * ENNReal.ofReal ((τ₀ / 4) * |Q.det|) := ENNReal.ofReal_mul hq.le
      _ ≤ ENNReal.ofReal q * (ν.prod volume)
          (normalizedEvent (derivativeEvent E P (B / K)) s q ∩ (A ×ˢ univ)) :=
        mul_le_mul le_rfl hfloor (by positivity) (by positivity)
      _ = _ := hmass
  refine ⟨hdet, hcenter, hframe, hentry, shiftedTest_degree hP _, hcoeff,
    hAm, selectedEvent_measurable hE hAm P (B / K) s q, fun n => ⟨hAf' n, hFf n⟩, ?_, ?_, htruefloor⟩
  · intro l hl
    have hgroup := hAU hl
    refine ⟨hgroup.1.1.trans hHout, fun e => (hgroup.1.2.1 e).trans hHout, ?_⟩
    intro t ht
    have ht' : t ∈ Icc s (s + q) := hIeq.symm ▸ ht
    have hh := hfull l hl t ht'
    simpa [WholeBlockFit, graphPoint, planarPoint, xl, yl,
      Submission.Obl.k4_quadratic_atlas_normalization.x,
      Submission.Obl.k4_quadratic_atlas_normalization.y] using hh
  · intro p hp
    refine ⟨hp.1.1, hp.1.2.1, ?_, ?_⟩
    · have ht : p.2 ∈ Icc s (s + q) := ⟨hp.1.2.2.1, hp.1.2.2.2.le⟩
      exact hIeq ▸ ht
    · rw [pderiv_shiftedTest]
      exact (div_le_div_of_nonneg_left hB.le hK₀ hκK).trans hp.2

end
end Submission.Obl.k4_horizon_chart_assembly
