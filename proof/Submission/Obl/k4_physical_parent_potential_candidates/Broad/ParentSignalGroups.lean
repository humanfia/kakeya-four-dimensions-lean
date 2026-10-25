-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ParentSignalGroups.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Extrapolation

/-!
# Independent graph signals and certificate tests

The physical signal used to extract the field need not be the old chart's quadratic test.
The graph equation below uses `R0`, while the value and jet certificate uses `Rc`. In
particular, `R0` may be the parent polynomial supplied by `pb`, and `Rc` the actual old test.
The small value bound on `Rc` is preserved without requiring a small value bound on `R0`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open Set MvPolynomial
open Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

/-- A regular hidden derivative remains regular under a perturbation of half its lower
bound. The upper and lower bounds use the same original hidden scale. -/
lemma hidden_window_of_close {Bv κ x y : ℝ} (hB : 0 < Bv) (hκ : 1 ≤ κ)
    (hlo : Bv / κ ≤ |x|) (hhi : |x| ≤ κ * Bv)
    (hclose : |y - x| ≤ Bv / (2 * κ)) :
    (2 * κ)⁻¹ ≤ |Bv⁻¹ * y| ∧ |Bv⁻¹ * y| ≤ 2 * κ := by
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hsmall : Bv / (2 * κ) ≤ κ * Bv := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (1 : ℝ) ≤ 2 * κ * κ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hB.le]
  have hylo : Bv / (2 * κ) ≤ |y| := by
    have htri := abs_sub_abs_le_abs_sub x y
    rw [abs_sub_comm x y] at htri
    have hsplit : Bv / κ = Bv / (2 * κ) + Bv / (2 * κ) := by field_simp; ring
    linarith
  have hyhi : |y| ≤ 2 * κ * Bv := by
    have htri := abs_sub_abs_le_abs_sub y x
    linarith
  have hBi : 0 < Bv⁻¹ := inv_pos.mpr hB
  rw [abs_mul, abs_of_pos hBi]
  constructor
  · rw [show (2 * κ)⁻¹ = Bv⁻¹ * (Bv / (2 * κ)) by field_simp]
    exact mul_le_mul_of_nonneg_left hylo hBi.le
  · rw [show 2 * κ = Bv⁻¹ * (2 * κ * Bv) by field_simp]
    exact mul_le_mul_of_nonneg_left hyhi hBi.le

/-- The sign of a regular derivative survives the same perturbation. -/
lemma hidden_sign_of_close {Bv κ x y σ : ℝ} (hB : 0 < Bv) (hκ : 0 < κ)
    (hσ : σ ^ 2 = 1) (hlo : Bv / κ ≤ σ * x)
    (hclose : |y - x| ≤ Bv / (2 * κ)) : 0 < Bv⁻¹ * y * σ := by
  have hσabs : |σ| = 1 := by
    have hs : |σ| ^ 2 = 1 := by rw [sq_abs]; exact hσ
    nlinarith [abs_nonneg σ, sq_nonneg (|σ| - 1), sq_nonneg (|σ| + 1)]
  have hd : |σ * y - σ * x| ≤ Bv / (2 * κ) := by
    rw [← mul_sub, abs_mul, hσabs, one_mul]
    exact hclose
  have hsplit : Bv / κ = Bv / (2 * κ) + Bv / (2 * κ) := by field_simp; ring
  have hy : Bv / (2 * κ) ≤ σ * y := by linarith [(abs_le.mp hd).1]
  have hpos : 0 < σ * y := lt_of_lt_of_le (by positivity) hy
  have heq : Bv⁻¹ * y * σ = Bv⁻¹ * (σ * y) := by ring
  rw [heq]
  exact mul_pos (inv_pos.mpr hB) hpos

/-- The hidden derivative of any quadratic has the same short-time stability estimate;
the signal and the certificate can therefore be handled independently. -/
lemma quadratic_hidden_derivative_close {R : Po} (hR : R.totalDegree ≤ 2)
    (l : Ln) {a h κ Bv te t : ℝ} (hh : 0 < h) (hκ : 1 ≤ κ) (hB : 0 < Bv)
    (hb : ∀ s ∈ Icc a (a + h), |eval (xp l s) (pderiv 3 R)| ≤ κ * Bv)
    (ht : |t - te| ≤ h / (4 * κ ^ 2)) :
    |eval (xp l t) (pderiv 3 R) - eval (xp l te) (pderiv 3 R)| ≤ Bv / (2 * κ) := by
  let p : Polynomial ℝ := trajRestrict (pderiv 3 R) l
  have hdeg : p.natDegree ≤ 1 := by
    refine (natDegree_trajRestrict_le _ _).trans ?_
    have hd := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred R 3
    omega
  have hpb : ∀ s ∈ Icc a (a + h), |p.eval s| ≤ κ * Bv := by
    intro s hs
    simpa only [p, eval_trajRestrict, xp_eq_trajPoint] using hb s hs
  have hdiff := abs_eval_sub_le_of_affine p hdeg hh hpb t te
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hnum : 2 * (κ * Bv) / h * |t - te| ≤ Bv / (2 * κ) := by
    calc
      2 * (κ * Bv) / h * |t - te|
          ≤ 2 * (κ * Bv) / h * (h / (4 * κ ^ 2)) := by gcongr
      _ = Bv / (2 * κ) := by field_simp; ring
  have hdiff' : |eval (xp l t) (pderiv 3 R) - eval (xp l te) (pderiv 3 R)| ≤
      2 * (κ * Bv) / h * |t - te| := by
    simpa only [p, eval_trajRestrict, xp_eq_trajPoint] using hdiff
  exact hdiff'.trans hnum

/-- Whole-block fits for a parent signal give the physical group points required by the
restoration backend, with the old test retained as a separate small certificate. -/
theorem physicalGroupPoint_near_event_of_independent_signal (D : ℕ) :
    ∃ Cx : ℝ, 1 ≤ Cx ∧
    ∀ (R0 Rc : Po) (P : MvPolynomial (Fin 3) ℝ),
      R0.totalDegree ≤ 2 → Rc.totalDegree ≤ 2 → (R0 - liftBase P).totalDegree ≤ D →
    ∀ (l : Ln) (a h κ Bv V cl c₀ εfit ω σ te : ℝ),
      0 < h → 1 ≤ κ → 0 < Bv → 0 ≤ V → 0 ≤ εfit →
      (∀ s ∈ Icc a (a + h),
        |eval (xp l s) R0 - eval (fun i : Fin 3 => xp l s i.castSucc) P - cl| ≤ εfit) →
      (∀ s ∈ Icc a (a + h), |eval (xp l s) Rc| ≤ V) →
      (∀ s ∈ Icc a (a + h), |eval (xp l s) (pderiv 3 R0)| ≤ κ * Bv) →
      (∀ s ∈ Icc a (a + h), |eval (xp l s) (pderiv 3 Rc)| ≤ κ * Bv) →
      |cl - c₀| ≤ ω → σ ^ 2 = 1 → te ∈ Icc a (a + h) →
      Bv / κ ≤ σ * eval (xp l te) (pderiv 3 R0) →
      Bv / κ ≤ |eval (xp l te) (pderiv 3 Rc)| →
    ∀ t, |t - te| ≤ h / (4 * κ ^ 2) →
      PhysicalGroupPoint Bv⁻¹ (R0 - C c₀) Rc P (Cx * εfit + ω) (2 * κ) σ
        (Cx * V) (graphPoint l t) := by
  obtain ⟨Cext, hCext, hext⟩ := exists_extrapolation_constant (max D 2)
  refine ⟨Cext, hCext, ?_⟩
  intro R0 Rc P hR0 hRc hdeg l a h κ Bv V cl c₀ εfit ω σ te hh hκ hB hV hε
    hfit hval hder0 hderc hwin hσ hte hreg0 hregc t ht
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have htime : t ∈ Icc (a - h) (a + 2 * h) := by
    have hrad : h / (4 * κ ^ 2) ≤ h := by
      rw [div_le_iff₀ (by positivity)]
      have hden : (1 : ℝ) ≤ 4 * κ ^ 2 := by nlinarith
      nlinarith
    obtain ⟨htlo, hthi⟩ := abs_le.mp ht
    exact ⟨by linarith [hte.1], by linarith [hte.2]⟩
  let residual : Polynomial ℝ := trajRestrict (R0 - liftBase P) l - Polynomial.C cl
  have hres : ∀ s, residual.eval s = eval (xp l s) R0 -
      eval (fun i : Fin 3 => xp l s i.castSucc) P - cl := by
    intro s
    simp only [residual, Polynomial.eval_sub, Polynomial.eval_C, eval_trajRestrict,
      map_sub, eval_liftBase]
    rfl
  have hresdeg : residual.natDegree ≤ max D 2 := by
    refine (Polynomial.natDegree_sub_C).le.trans ?_
    exact (natDegree_trajRestrict_le _ _).trans (hdeg.trans (le_max_left _ _))
  have hresb : ∀ s ∈ Icc a (a + h), |residual.eval s| ≤ εfit := by
    intro s hs
    rw [hres]
    exact hfit s hs
  have hrest := hext residual a h εfit hresdeg hh hε hresb t htime
  rw [hres] at hrest
  have htestdeg : (trajRestrict Rc l).natDegree ≤ max D 2 :=
    (natDegree_trajRestrict_le _ _).trans (hRc.trans (le_max_right _ _))
  have htestb : ∀ s ∈ Icc a (a + h), |(trajRestrict Rc l).eval s| ≤ V := by
    intro s hs
    simpa only [eval_trajRestrict, xp_eq_trajPoint] using hval s hs
  have htest := hext (trajRestrict Rc l) a h V htestdeg hh hV htestb t htime
  have hclose0 := quadratic_hidden_derivative_close hR0 l hh hκ hB hder0 ht
  have hclosec := quadratic_hidden_derivative_close hRc l hh hκ hB hderc ht
  have hreg0abs : Bv / κ ≤ |eval (xp l te) (pderiv 3 R0)| := by
    have hσabs : |σ| = 1 := by
      have hs : |σ| ^ 2 = 1 := by rw [sq_abs]; exact hσ
      nlinarith [abs_nonneg σ, sq_nonneg (|σ| - 1), sq_nonneg (|σ| + 1)]
    have hs := le_abs_self (σ * eval (xp l te) (pderiv 3 R0))
    rw [abs_mul, hσabs, one_mul] at hs
    exact hreg0.trans hs
  obtain ⟨hlo0, hhi0⟩ := hidden_window_of_close hB hκ hreg0abs (hder0 te hte) hclose0
  obtain ⟨hloc, hhic⟩ := hidden_window_of_close hB hκ hregc (hderc te hte) hclosec
  have hsign := hidden_sign_of_close hB hκ0 hσ hreg0 hclose0
  have hpd : pderiv 3 (R0 - C c₀) = pderiv 3 R0 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change |eval (xp l t) (R0 - C c₀) - eval (fun i : Fin 3 => xp l t i.castSucc) P| ≤ _
    rw [map_sub, eval_C]
    calc
      |eval (xp l t) R0 - c₀ - eval (fun i : Fin 3 => xp l t i.castSucc) P|
          = |(eval (xp l t) R0 - eval (fun i : Fin 3 => xp l t i.castSucc) P - cl) +
              (cl - c₀)| := by ring_nf
      _ ≤ Cext * εfit + ω := (abs_add_le _ _).trans (add_le_add hrest hwin)
  · simpa only [graphPoint_eq_trajPoint, hpd, xp_eq_trajPoint] using hsign
  · simpa only [graphPoint_eq_trajPoint, hpd, xp_eq_trajPoint] using hlo0
  · simpa only [graphPoint_eq_trajPoint, hpd, xp_eq_trajPoint] using hhi0
  · exact hloc
  · exact hhic
  · simpa only [eval_trajRestrict, graphPoint_eq_trajPoint] using htest

/-- Specialization to an actual old chart. Only the fitted signal and its derivative
bound come from the parent; the small certificate value and its regularity come from `ch`. -/
theorem physicalGroupPoint_of_parent_chart (D : ℕ) :
    ∃ Cx : ℝ, 1 ≤ Cx ∧
    ∀ {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T : ℕ} {jj rr Bv : ℝ}
      {Evs : Set Ev} {c u : P2} {Qm : Matrix (Fin 2) (Fin 2) ℝ}
      {Rb : Po} {A : Set Ln} {F : Set Ev} {ex : Prop},
      ch Nk Mp Dp κ T jj rr Bv Evs c u Qm Rb A F ex → 1 ≤ κ → 0 < Bv →
    ∀ (R0 : Po) (P : MvPolynomial (Fin 3) ℝ), R0.totalDegree ≤ 2 →
      (R0 - liftBase P).totalDegree ≤ D →
    ∀ (l : Ln) (K cl c₀ εfit ω σ te : ℝ), κ ≤ K → 0 ≤ εfit →
      (∀ s ∈ Icc (jj / (2 : ℝ) ^ T) ((jj + 1) / (2 : ℝ) ^ T),
        |eval (xp l s) R0 - eval (fun i : Fin 3 => xp l s i.castSucc) P - cl| ≤ εfit) →
      (∀ s ∈ Icc (jj / (2 : ℝ) ^ T) ((jj + 1) / (2 : ℝ) ^ T),
        |eval (xp l s) (pderiv 3 R0)| ≤ K * Bv) →
      |cl - c₀| ≤ ω → σ ^ 2 = 1 → (l, te) ∈ F →
      Bv / K ≤ σ * eval (xp l te) (pderiv 3 R0) →
    ∀ t, |t - te| ≤ ((2 : ℝ) ^ T)⁻¹ / (4 * K ^ 2) →
      PhysicalGroupPoint Bv⁻¹ (R0 - C c₀) Rb P (Cx * εfit + ω) (2 * K) σ
        (Cx * (κ * δ Nk rr)) (graphPoint l t) := by
  obtain ⟨Cx, hCx, hgroup⟩ := physicalGroupPoint_near_event_of_independent_signal D
  refine ⟨Cx, hCx, ?_⟩
  intro Nk Mp Dp κ T jj rr Bv Evs c u Qm Rb A F ex hch hκ hB R0 P hR0 hdeg
    l K cl c₀ εfit ω σ te hκK hε hfit hparent hwin hσ hF hparentreg t ht
  obtain ⟨_, _, _, _, hRb, _, _, _, _, hA, hFdata, _⟩ := hch
  obtain ⟨_, hl, hte, hreg⟩ := hFdata (l, te) hF
  have hK : 1 ≤ K := hκ.trans hκK
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hclock : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hblock : (jj + 1) / (2 : ℝ) ^ T =
      jj / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ := by ring
  have hvals := (hA l hl).2.2
  rw [hblock] at hfit hparent hte hvals
  have hreg' : Bv / K ≤ |eval (xp l te) (pderiv 3 Rb)| := by
    exact (div_le_div_of_nonneg_left hB.le hκ0 hκK).trans hreg
  exact hgroup R0 Rb P hR0 hRb hdeg l (jj / (2 : ℝ) ^ T) ((2 : ℝ) ^ T)⁻¹ K Bv
    (κ * δ Nk rr) cl c₀ εfit ω σ te hclock hK hB (by
      have hδ := δ_pos Nk rr
      positivity) hε hfit (fun s hs => (hvals s hs).2.1) hparent (by
        intro s hs
        exact ((hvals s hs).2.2.1).trans (mul_le_mul_of_nonneg_right hκK hB.le))
      hwin hσ hte hparentreg hreg' t ht

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
