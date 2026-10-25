-- Lane B: the return of a normalized quadratic certificate to the physical old block.
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.PacketReturn
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.QuadraticTube
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.PhysicalExit

/-!
# Physical return (lane B, step 5)

A quadratic `Q` certified in normalized coordinates `(u, W)` on the ball `closedBall cq (2 r)`
(small near the graph `W = f u`, regular signed hidden derivative, curvature `≤ Aq / Eb`) is
pulled back by the normalization `x ↦ (c + M x_base, Bv x₃)` to the physical quadratic
`R = transportPolynomial c M Bv Q`. Along every retained event's line, for times within `θ h`
of the event, the normalized point stays in the certified ball and near the graph; so `R`, `∂₃R`
and `∂₃₃R` have the bounds of the direct exit there, and `PacketReturn.restoration_of_event_windows`
returns the whole-block `RestorationOutput`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial Metric QuadraticTube

noncomputable section

/-- **The physical return of a normalized certificate.** -/
theorem physical_return (ν : Measure Ln) [IsFiniteMeasure ν]
    (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    {Bv a w Eb Aq band r θ Cm Mcoef Cr : ℝ} (T j : ℕ) (Gl : Set Ln) (G G0 : Set Ev)
    (Q : Analytic.Poly) (cq : Analytic.Base) (f : Analytic.Base → ℝ)
    (hQ : Q.totalDegree ≤ 2)
    (hRcoeff : ∀ m, |(Analytic.transportPolynomial c M Bv Q).coeff m| ≤ Mcoef)
    (hBv : 0 < Bv) (ha : 0 < a) (hw : 0 < w) (hEb : 0 < Eb) (hAq : 1 ≤ Aq)
    (hband : 0 ≤ band) (hAqband : Aq * band ≤ Eb) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hQprop : ∀ u ∈ closedBall cq (2 * r), ∀ W : ℝ, Aq * |W - f u| ≤ Eb →
      |ev Q u W| ≤ Aq * (Eb + |W - f u|) ∧
      Aq⁻¹ ≤ ev (pderiv (3 : Fin 4) Q) u W ∧ ev (pderiv (3 : Fin 4) Q) u W ≤ Aq ∧
      |ev (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q)) u W| ≤ Aq / Eb)
    (hG0 : MeasurableSet G0) (hsub : G0 ⊆ G)
    (hevents : ∀ e ∈ G0, e.1 ∈ Gl ∧ e.2 ∈ Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T))
    (hnear : ∀ e ∈ G0, ∀ t ∈ Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T),
      |t - e.2| ≤ θ * ((2 : ℝ) ^ T)⁻¹ →
      Analytic.normalizedBase c M Bv (Analytic.graphPoint e.1 t) ∈ closedBall cq (2 * r) ∧
      |Bv * Analytic.graphPoint e.1 t 3 -
        f (Analytic.normalizedBase c M Bv (Analytic.graphPoint e.1 t))| ≤ band)
    (hmass : (ν.prod volume) G ≤ ENNReal.ofReal Cm * (ν.prod volume) G0)
    (hCr : max Cm (max (2 * Aq * Eb / (a * w)) (max Aq (Aq * (a * w) / Eb))) ≤ Cr)
    (hCr2 : 32 * max (2 * Aq * Eb / (a * w)) (max Aq (Aq * (a * w) / Eb)) / θ ^ 2 ≤ Cr) :
    RestorationOutput (ν.prod volume) Mcoef Cr Bv a w T j Gl G := by
  let R := Analytic.transportPolynomial c M Bv Q
  let Cv := max (2*Aq*Eb/(a*w)) (max Aq (Aq*(a*w)/Eb))
  have haw : 0 < a*w := mul_pos ha hw
  have hAq0 : 0 < Aq := by linarith only [hAq]
  have hCvAq : Aq ≤ Cv := (le_max_left _ _).trans (le_max_right _ _)
  have hCv : 0 < Cv := hAq0.trans_le hCvAq
  have hCvVal : 2*Aq*Eb ≤ Cv*(a*w) :=
    (div_le_iff₀ haw).mp (le_max_left _ _)
  have hCvCurv : Aq*(a*w)/Eb ≤ Cv := (le_max_right _ _).trans (le_max_right _ _)
  have hbandEb : band ≤ Eb :=
    (le_mul_of_one_le_left hband hAq).trans hAqband
  have hcoordinate (l:Ln) (t:ℝ) :
      point (Analytic.normalizedBase c M Bv (Analytic.graphPoint l t))
        (Bv*Analytic.graphPoint l t 3) = Analytic.coordinateMap c M Bv (xp l t) := by
    ext i
    fin_cases i <;> simp [point,Analytic.normalizedBase,Analytic.pointOfCoordinates,
      Analytic.coordinateMap,Analytic.graphPoint,xp,Fin.snoc]
  have hmap (P:Po) (l:Ln) (t:ℝ) :
      eval (Analytic.coordinateMap c M Bv (xp l t)) P =
        ev P (Analytic.normalizedBase c M Bv (Analytic.graphPoint l t))
          (Bv*Analytic.graphPoint l t 3) := by
    unfold ev
    rw [hcoordinate]
  have hlocal (e:Ev) (he:e∈G0)
      (t:ℝ) (ht:t∈Icc ((j:ℝ)/(2:ℝ)^T) (((j:ℝ)+1)/(2:ℝ)^T))
      (hne:|t-e.2| ≤ θ*((2:ℝ)^T)⁻¹) :
      |eval (xp e.1 t) R| ≤ Cv*(a*w) ∧
      |eval (xp e.1 t) (pderiv 3 R)| ≤ Cv*Bv ∧
      |eval (xp e.1 t) (pderiv 3 (pderiv 3 R))| ≤ Cv*Bv^2/(a*w) ∧
      Bv/Cv ≤ |eval (xp e.1 t) (pderiv 3 R)| := by
    obtain ⟨hu,hbandt⟩ := hnear e he t ht hne
    obtain ⟨hv,hdlo,hdhi,hd2⟩ := hQprop _ hu _
      ((mul_le_mul_of_nonneg_left hbandt hAq0.le).trans hAqband)
    have hderiv : 0 ≤ ev (pderiv (3:Fin 4) Q)
        (Analytic.normalizedBase c M Bv (Analytic.graphPoint e.1 t))
        (Bv*Analytic.graphPoint e.1 t 3) :=
      (inv_nonneg.mpr hAq0.le).trans hdlo
    have hval := Analytic.eval_transportPolynomial c M Bv Q (xp e.1 t)
    have hjets := Analytic.eval_transport_hidden_derivatives c M Bv Q (xp e.1 t)
    rw [hmap] at hval
    rw [hmap] at hjets
    have hdabs : |eval (xp e.1 t) (pderiv 3 R)| = Bv*ev (pderiv (3:Fin 4) Q)
        (Analytic.normalizedBase c M Bv (Analytic.graphPoint e.1 t))
        (Bv*Analytic.graphPoint e.1 t 3) := by
      rw [hjets.1,abs_mul,abs_of_pos hBv,abs_of_nonneg hderiv]
    refine ⟨?_,?_,?_,?_⟩
    · rw [hval]
      calc
        _ ≤ Aq*(Eb+|Bv*Analytic.graphPoint e.1 t 3-
            f (Analytic.normalizedBase c M Bv (Analytic.graphPoint e.1 t))|) := hv
        _ ≤ Aq*(Eb+Eb) := by gcongr; exact hbandt.trans hbandEb
        _ = 2*Aq*Eb := by ring
        _ ≤ _ := hCvVal
    · rw [hdabs]
      exact (mul_le_mul_of_nonneg_left hdhi hBv.le).trans
        (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hCvAq hBv.le)
    · rw [hjets.2,hmap,abs_mul,abs_of_nonneg (sq_nonneg Bv)]
      calc
        _ ≤ Bv^2*(Aq/Eb) := mul_le_mul_of_nonneg_left hd2 (sq_nonneg Bv)
        _ ≤ Cv*Bv^2/(a*w) := by
          rw [le_div_iff₀ haw]
          have hm := mul_le_mul_of_nonneg_right hCvCurv (sq_nonneg Bv)
          convert hm using 1 <;> ring
    · rw [hdabs]
      calc
        Bv/Cv ≤ Bv/Aq := div_le_div_of_nonneg_left hBv.le hAq0 hCvAq
        _ = Bv*Aq⁻¹ := div_eq_mul_inv _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hdlo hBv.le
  have hlow (e:Ev) (he:e∈G0) : Bv/Cv ≤ |eval (xp e.1 e.2) (pderiv 3 R)| := by
    exact (hlocal e he e.2 (hevents e he).2 (by simp; positivity)).2.2.2
  apply PacketReturn.restoration_of_event_windows ν R T j Gl G G0
    ((Analytic.totalDegree_transportPolynomial_le c M Bv Q).trans hQ) hRcoeff
    hCv hBv ha hw hθ hθ2 ((le_max_right _ _).trans hCr) hCr2
    ((le_max_left _ _).trans hCr) hG0 hsub hevents hlow
  · intro e he t ht hne
    have hh := hlocal e he t ht hne
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  · exact hmass

end

end Submission.Obl.k4_physical_parent_potential_candidates
