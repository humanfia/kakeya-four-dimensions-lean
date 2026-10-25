-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Extrapolation.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.QuadraticReplacement
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ChartVelocity
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.DirectPackaging
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.PhysicalGroupPoints
import Submission.Lib.K4HiddenQuadratic

/-!
# Group points along fitted trajectories, slightly beyond the block

The sampled exit asks for physical group points along a trajectory for all times within `τw` of
a counted incidence, possibly a little outside the old block. Along a trajectory, the chart test,
its hidden derivative and the own-intercept residual are polynomials in time of bounded degree.
A polynomial of degree at most `D` bounded by `E` on an interval of length `h` is bounded by
`C_D E` on the interval enlarged by `h` on both sides (`exists_extrapolation_constant`, by Taylor
expansion at the nearest point of the interval and the interval derivative bounds). The hidden
derivative is affine in time with slope at most `2 κ B / h`, so near a counted incidence it keeps
its sign and stays between `B / (2κ)` and `2 κ B`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open Set MvPolynomial
open Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

/-- **Extrapolation of bounded polynomials.** -/
theorem exists_extrapolation_constant (D : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : Polynomial ℝ) (a h E : ℝ), p.natDegree ≤ D → 0 < h → 0 ≤ E →
      (∀ t ∈ Icc a (a + h), |p.eval t| ≤ E) →
      ∀ t ∈ Icc (a - h) (a + 2 * h), |p.eval t| ≤ C * E := by
  obtain ⟨C₀, hC₀, hder⟩ := exists_iterate_derivative_bound D
  set S : ℝ := ∑ j ∈ Finset.range (D + 1), C₀ ^ j / (j.factorial : ℝ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨S + 1, by linarith, ?_⟩
  intro p a h E hp hh hE hb t ht
  set r : ℝ := max a (min t (a + h)) with hr
  have hra : a ≤ r := le_max_left _ _
  have hrb : r ≤ a + h := max_le (by linarith) (min_le_right _ _)
  have hrmem : r ∈ Icc a (a + h) := ⟨hra, hrb⟩
  have htr : |t - r| ≤ h := by
    rw [abs_le]
    obtain ⟨ht1, ht2⟩ := ht
    constructor
    · -- t - r ≥ -h
      rcases le_total t (a + h) with h1 | h1
      · have : min t (a + h) = t := min_eq_left h1
        rw [hr, this]
        rcases le_total a t with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; linarith
      · have : min t (a + h) = a + h := min_eq_right h1
        rw [hr, this, max_eq_right (by linarith)]; linarith
    · rcases le_total t (a + h) with h1 | h1
      · have : min t (a + h) = t := min_eq_left h1
        rw [hr, this]
        rcases le_total a t with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; linarith
      · have : min t (a + h) = a + h := min_eq_right h1
        rw [hr, this, max_eq_right (by linarith)]; linarith
  -- Taylor expansion at `r`
  have htay : p.eval t = ∑ j ∈ Finset.range (D + 1),
      (Polynomial.hasseDeriv j p).eval r * (t - r) ^ j := by
    have h1 := Polynomial.taylor_eval r p (t - r)
    rw [sub_add_cancel] at h1
    rw [← h1, Polynomial.eval_eq_sum_range' (n := D + 1)
      (by rw [Polynomial.natDegree_taylor]; omega)]
    simp only [Polynomial.taylor_coeff]
  have hhd : ∀ j, (Polynomial.hasseDeriv j p).eval r =
      (Polynomial.derivative^[j] p).eval r / (j.factorial : ℝ) := by
    intro j
    have h1 := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := j)) p
    rw [LinearMap.smul_apply] at h1
    rw [← h1, Polynomial.eval_smul, nsmul_eq_mul]
    field_simp
  rw [htay]
  calc |∑ j ∈ Finset.range (D + 1), (Polynomial.hasseDeriv j p).eval r * (t - r) ^ j|
      ≤ ∑ j ∈ Finset.range (D + 1), |(Polynomial.hasseDeriv j p).eval r * (t - r) ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (D + 1), C₀ ^ j / (j.factorial : ℝ) * E := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, hhd j, abs_div, abs_pow, Nat.abs_cast]
        have hfac : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
        have hd := hder p a h E hp hh hE hb j r hrmem
        have hpow : |t - r| ^ j ≤ h ^ j := pow_le_pow_left₀ (abs_nonneg _) htr j
        calc |(Polynomial.derivative^[j] p).eval r| / (j.factorial : ℝ) * |t - r| ^ j
            ≤ (C₀ ^ j * E / h ^ j) / (j.factorial : ℝ) * h ^ j := by
              gcongr
          _ = C₀ ^ j / (j.factorial : ℝ) * E := by
              have : h ^ j ≠ 0 := pow_ne_zero _ hh.ne'
              field_simp
    _ = S * E := by rw [hS, Finset.sum_mul]
    _ ≤ (S + 1) * E := by nlinarith

/-- An affine polynomial bounded by `E` on an interval of length `h` has slope at most
`2 E / h`. -/
lemma abs_eval_sub_le_of_affine (p : Polynomial ℝ) (hp : p.natDegree ≤ 1) {a h E : ℝ}
    (hh : 0 < h) (hb : ∀ t ∈ Icc a (a + h), |p.eval t| ≤ E) (s t : ℝ) :
    |p.eval s - p.eval t| ≤ 2 * E / h * |s - t| := by
  have he : ∀ x, p.eval x = p.coeff 0 + p.coeff 1 * x := by
    intro x
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ]
  have h1 := hb a ⟨le_rfl, by linarith⟩
  have h2 := hb (a + h) ⟨by linarith, le_rfl⟩
  rw [he a] at h1
  rw [he (a + h)] at h2
  have hslope : |p.coeff 1| * h ≤ 2 * E := by
    have : p.coeff 1 * h = (p.coeff 0 + p.coeff 1 * (a + h)) - (p.coeff 0 + p.coeff 1 * a) := by
      ring
    have h3 : |p.coeff 1 * h| ≤ 2 * E := by
      rw [this]
      calc _ ≤ |p.coeff 0 + p.coeff 1 * (a + h)| + |p.coeff 0 + p.coeff 1 * a| := abs_sub _ _
        _ ≤ 2 * E := by linarith
    rwa [abs_mul, abs_of_pos hh] at h3
  rw [he s, he t]
  have : p.coeff 0 + p.coeff 1 * s - (p.coeff 0 + p.coeff 1 * t) = p.coeff 1 * (s - t) := by ring
  rw [this, abs_mul]
  have hc : |p.coeff 1| ≤ 2 * E / h := by rw [le_div_iff₀ hh]; exact hslope
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)

lemma graphPoint_eq_trajPoint (l : Line) (t : ℝ) : graphPoint l t = trajPoint l t := rfl

lemma xp_eq_trajPoint (l : Ln) (t : ℝ) : xp l t = trajPoint l t := rfl

/-- **Group points along a fitted trajectory near a counted incidence.**  A trajectory of the
chart with a whole-block own-intercept fit, an intercept within `ω` of `c₀`, and a counted
incidence at time `te` where `σ ∂₃R_b ≥ B/κ`, gives physical group points of
`(R_b - c₀, R_b, P)` at all times within `h / (4κ²)` of `te`. -/
theorem physicalGroupPoint_near_event (D : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T : ℕ} {jj : ℝ} {rr Bv : ℝ} {Evs : Set Ev} {c u : P2}
      {Qm : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po} {A : Set Ln} {F : Set Ev} {ex : Prop},
      ch Nk Mp Dp κ T jj rr Bv Evs c u Qm Rb A F ex → 1 ≤ κ → 0 < Bv →
    ∀ (P : MvPolynomial (Fin 3) ℝ), (Rb - liftBase P).totalDegree ≤ D →
    ∀ (l : Ln) (cl c₀ εfit ω σ te : ℝ), l ∈ A → 0 ≤ εfit → 0 ≤ ω →
      (∀ t ∈ Icc (jj / (2:ℝ) ^ T) ((jj + 1) / (2:ℝ) ^ T),
        |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P - cl|
          ≤ εfit) →
      |cl - c₀| ≤ ω → σ ^ 2 = 1 →
      te ∈ Icc (jj / (2:ℝ) ^ T) ((jj + 1) / (2:ℝ) ^ T) →
      Bv / κ ≤ σ * MvPolynomial.eval (xp l te) (pderiv 3 Rb) →
      ∀ t, |t - te| ≤ ((2:ℝ) ^ T)⁻¹ / (4 * κ ^ 2) →
        PhysicalGroupPoint Bv⁻¹ (Rb - MvPolynomial.C c₀) Rb P (C * εfit + ω) (2 * κ) σ
          (C * (κ * δ Nk rr)) (graphPoint l t) := by
  obtain ⟨C, hC, hext⟩ := exists_extrapolation_constant (max D 2)
  refine ⟨C, hC, ?_⟩
  intro Nk Mp Dp κ T jj rr Bv Evs c u Qm Rb A F ex hch hκ hBv P hdeg l cl c₀ εfit ω σ te hl
    hε hω hfit hwin hσ hte hder t ht
  obtain ⟨_, _, _, _, hRdeg, _, _, _, _, hA, _, _⟩ := hch
  set h : ℝ := ((2:ℝ) ^ T)⁻¹ with hh
  have hh0 : 0 < h := by positivity
  set a : ℝ := jj / (2:ℝ) ^ T with ha
  have hblock : (jj + 1) / (2:ℝ) ^ T = a + h := by rw [ha, hh]; ring
  rw [hblock] at hfit hte
  have hlA := (hA l hl).2.2
  rw [hblock] at hlA
  have hκ0 : 0 < κ := by linarith
  -- the time `t` lies within `h` of the block
  have htmem : t ∈ Icc (a - h) (a + 2 * h) := by
    have hq : ((2:ℝ) ^ T)⁻¹ / (4 * κ ^ 2) ≤ h := by
      rw [hh, div_le_iff₀ (by positivity)]
      have : (1:ℝ) ≤ 4 * κ ^ 2 := by nlinarith
      nlinarith [show (0:ℝ) < ((2:ℝ) ^ T)⁻¹ by positivity]
    obtain ⟨h1, h2⟩ := abs_le.mp ht
    exact ⟨by linarith [hte.1], by linarith [hte.2]⟩
  -- the residual polynomial
  set F₁ : Polynomial ℝ := trajRestrict (Rb - liftBase P) l - Polynomial.C cl with hF₁
  have hF₁eval : ∀ s, F₁.eval s = MvPolynomial.eval (xp l s) Rb -
      MvPolynomial.eval (fun i => xp l s i.castSucc) P - cl := by
    intro s
    rw [hF₁, Polynomial.eval_sub, Polynomial.eval_C, eval_trajRestrict, map_sub, eval_liftBase]
    rfl
  have hF₁deg : F₁.natDegree ≤ max D 2 := by
    rw [hF₁]
    refine (Polynomial.natDegree_sub_C).le.trans ?_
    exact (natDegree_trajRestrict_le _ _).trans (hdeg.trans (le_max_left _ _))
  have hF₁b : ∀ s ∈ Icc a (a + h), |F₁.eval s| ≤ εfit := fun s hs => by
    rw [hF₁eval]; exact hfit s hs
  have hF₁t := hext F₁ a h εfit hF₁deg hh0 hε hF₁b t htmem
  rw [hF₁eval] at hF₁t
  -- the chart test
  set F₃ : Polynomial ℝ := trajRestrict Rb l with hF₃
  have hF₃deg : F₃.natDegree ≤ max D 2 :=
    (natDegree_trajRestrict_le _ _).trans (hRdeg.trans (le_max_right _ _))
  have hF₃b : ∀ s ∈ Icc a (a + h), |F₃.eval s| ≤ κ * δ Nk rr := fun s hs => by
    rw [hF₃, eval_trajRestrict]; exact (hlA s hs).2.1
  have hF₃t := hext F₃ a h (κ * δ Nk rr) hF₃deg hh0 (by have := δ_pos Nk rr; positivity)
    hF₃b t htmem
  rw [hF₃, eval_trajRestrict] at hF₃t
  -- the hidden derivative: affine in time
  set F₂ : Polynomial ℝ := trajRestrict (pderiv 3 Rb) l with hF₂
  have hF₂deg : F₂.natDegree ≤ 1 := by
    refine (natDegree_trajRestrict_le _ _).trans ?_
    have := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred Rb 3
    omega
  have hF₂b : ∀ s ∈ Icc a (a + h), |F₂.eval s| ≤ κ * Bv := fun s hs => by
    rw [hF₂, eval_trajRestrict]; exact (hlA s hs).2.2.1
  have hslope := abs_eval_sub_le_of_affine F₂ hF₂deg hh0 hF₂b t te
  rw [hF₂, eval_trajRestrict, eval_trajRestrict] at hslope
  have hdelta : 2 * (κ * Bv) / h * |t - te| ≤ Bv / (2 * κ) := by
    calc 2 * (κ * Bv) / h * |t - te| ≤ 2 * (κ * Bv) / h * (h / (4 * κ ^ 2)) := by
          gcongr
      _ = Bv / (2 * κ) := by field_simp; ring
  have hte' : |MvPolynomial.eval (xp l te) (pderiv 3 Rb)| ≤ κ * Bv :=
    (hlA te hte).2.2.1
  have hσabs : |σ| = 1 := by
    have : |σ| ^ 2 = 1 := by rw [sq_abs]; exact hσ
    nlinarith [abs_nonneg σ, sq_nonneg (|σ| - 1), sq_nonneg (|σ| + 1)]
  set dt := MvPolynomial.eval (trajPoint l t) (pderiv 3 Rb) with hdt
  set de := MvPolynomial.eval (trajPoint l te) (pderiv 3 Rb) with hde
  have hder' : Bv / κ ≤ σ * de := hder
  -- sign and window of the hidden derivative at `t`
  have hsig : Bv / (2 * κ) ≤ σ * dt := by
    have h1 : |σ * dt - σ * de| ≤ Bv / (2 * κ) := by
      rw [← mul_sub, abs_mul, hσabs, one_mul]; exact hslope.trans hdelta
    have : Bv / κ = Bv / (2 * κ) + Bv / (2 * κ) := by field_simp; ring
    linarith [(abs_le.mp h1).1]
  have hdt_le : |dt| ≤ 2 * κ * Bv := by
    have h1 : |dt| ≤ |de| + Bv / (2 * κ) := by
      have := abs_sub_abs_le_abs_sub dt de
      linarith [hslope.trans hdelta]
    have h2 : Bv / (2 * κ) ≤ κ * Bv := by
      rw [div_le_iff₀ (by positivity)]
      have hk2 : (1:ℝ) ≤ 2 * κ * κ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hk2 hBv.le]
    have hte'' : |de| ≤ κ * Bv := hte'
    linarith
  have hdt_ge : Bv / (2 * κ) ≤ |dt| := by
    have : σ * dt ≤ |σ * dt| := le_abs_self _
    rw [abs_mul, hσabs, one_mul] at this
    linarith
  have hBinv : 0 < Bv⁻¹ := inv_pos.mpr hBv
  have hwin_lo : (2 * κ)⁻¹ ≤ |Bv⁻¹ * dt| := by
    rw [abs_mul, abs_of_pos hBinv]
    rw [show (2 * κ)⁻¹ = Bv⁻¹ * (Bv / (2 * κ)) by field_simp]
    exact mul_le_mul_of_nonneg_left hdt_ge hBinv.le
  have hwin_hi : |Bv⁻¹ * dt| ≤ 2 * κ := by
    rw [abs_mul, abs_of_pos hBinv]
    rw [show 2 * κ = Bv⁻¹ * (2 * κ * Bv) by field_simp]
    exact mul_le_mul_of_nonneg_left hdt_le hBinv.le
  have hpd : pderiv 3 (Rb - MvPolynomial.C c₀) = pderiv 3 Rb := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the group equation
    rw [graphPoint_eq_trajPoint, map_sub, MvPolynomial.eval_C]
    have hfix : (fun i : Fin 3 => trajPoint l t i.castSucc) = fun i => xp l t i.castSucc := rfl
    rw [hfix]
    have hxt : trajPoint l t = xp l t := rfl
    rw [hxt]
    calc |MvPolynomial.eval (xp l t) Rb - c₀ - MvPolynomial.eval (fun i => xp l t i.castSucc) P|
        = |(MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
            cl) + (cl - c₀)| := by ring_nf
      _ ≤ C * εfit + ω := (abs_add_le _ _).trans (add_le_add hF₁t hwin)
  · rw [graphPoint_eq_trajPoint, hpd, ← hdt]
    have : Bv⁻¹ * dt * σ = Bv⁻¹ * (σ * dt) := by ring
    rw [this]
    exact mul_pos hBinv (lt_of_lt_of_le (by positivity) hsig)
  · rw [graphPoint_eq_trajPoint, hpd, ← hdt]; exact hwin_lo
  · rw [graphPoint_eq_trajPoint, hpd, ← hdt]; exact hwin_hi
  · rw [graphPoint_eq_trajPoint, ← hdt]; exact hwin_lo
  · rw [graphPoint_eq_trajPoint, ← hdt]; exact hwin_hi
  · rw [graphPoint_eq_trajPoint]; exact hF₃t

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
