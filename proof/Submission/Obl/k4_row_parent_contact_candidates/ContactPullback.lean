/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactPullback.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactValid

/-!
# Pulling zoomed candidates back to the original model

* `measurableSet_fit_line`: fit events of lines are measurable (closed in the
  coefficients);
* `pullback_floor`: zoomed mass floors of arbitrary measurable events become
  original floors `c 2^(-T) ν(A)`;
* `coeffL1_nPush_le`: coefficient budget of pushed, row-normalized tests;
* `ZoomSeq.candidate_pullback`: a zoomed candidate at depth `σ` (quadratic or
  strip) gives an original candidate at the grid depth `r + (j+1)δ` of its label,
  with `nLift` for quadratic tests and `strip_pullback` for strips, given
  explicit budget bounds at that index.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point skewSubst unskewSubst skewBudget)
open Submission.Lib.K4ChartLifting (coeffL1 coeffL1_nonneg coeffL1_X coeffL1_C coeffL1_add_le
  coeffL1_C_mul_le coeffL1_bind₁_le)

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Lines along which a test fits on a time set form a measurable set. -/
theorem measurableSet_fit_line {β : α → Fin 6 → ℝ} (hβ : Measurable β)
    (Q : MvPolynomial (Fin 4) ℝ) (I : Set ℝ) (H w : ℝ) :
    MeasurableSet {l : α | ∀ t ∈ I, |eval (point (β l) t) Q| ≤ H * w ∧
      |eval (point (β l) t) (pderiv (3 : Fin 4) Q)| ≤ H ∧
      |eval (point (β l) t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ H / w} := by
  have hc : ∀ (R : MvPolynomial (Fin 4) ℝ) (t : ℝ),
      Continuous (fun b : Fin 6 → ℝ => |eval (point b t) R|) := fun R t =>
    continuous_abs.comp ((MvPolynomial.continuous_eval R).comp (continuous_point_left t))
  have hC : IsClosed {b : Fin 6 → ℝ | ∀ t ∈ I, |eval (point b t) Q| ≤ H * w ∧
      |eval (point b t) (pderiv (3 : Fin 4) Q)| ≤ H ∧
      |eval (point b t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ H / w} := by
    have : {b : Fin 6 → ℝ | ∀ t ∈ I, |eval (point b t) Q| ≤ H * w ∧
        |eval (point b t) (pderiv (3 : Fin 4) Q)| ≤ H ∧
        |eval (point b t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ H / w} =
        ⋂ t ∈ I, ({b | |eval (point b t) Q| ≤ H * w} ∩
          ({b | |eval (point b t) (pderiv (3 : Fin 4) Q)| ≤ H} ∩
            {b | |eval (point b t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ H / w})) := by
      ext b; simp
    rw [this]
    exact isClosed_biInter fun t _ =>
      (isClosed_le (hc Q t) continuous_const).inter
        ((isClosed_le (hc _ t) continuous_const).inter (isClosed_le (hc _ t) continuous_const))
  exact hC.measurableSet.preimage hβ

/-- **Mass floors pull back** for arbitrary measurable zoomed events whose
zoom preimages (on the retained set) lie in the original event. -/
theorem pullback_floor {ν : Measure α} {ρ : Measure (α × ℝ)} {G : Set (α × ℝ)}
    (hG : MeasurableSet G) {AQ A : Set α} (hA : MeasurableSet A) (hAQ : A ⊆ AQ)
    (hν0 : ν AQ ≠ 0) (hνt : ν AQ ≠ ⊤) {T TQ : ℕ} (hTQ : TQ ≤ T) (t₀ : ℝ)
    {E' E : Set (α × ℝ)} (hE' : MeasurableSet E')
    (hsub : G ∩ zoomTime t₀ ((2 : ℝ) ^ (-(TQ : ℤ))) ⁻¹' E' ⊆ E) {c : ℝ}
    (hfloor : ENNReal.ofReal (c * (2 : ℝ) ^ (-((T - TQ : ℕ) : ℤ))) * condPrior ν AQ A ≤
      zoomLaw ρ G t₀ ((2 : ℝ) ^ (-(TQ : ℤ))) (ENNReal.ofReal ((2 : ℝ) ^ (-(TQ : ℤ))) * ν AQ) E') :
    ENNReal.ofReal (c * (2 : ℝ) ^ (-(T : ℤ))) * ν A ≤ ρ E := by
  rw [zoomLaw_apply ρ hG _ _ _ hE', condPrior_apply ν AQ A hA, inter_eq_left.mpr hAQ] at hfloor
  set qQ : ℝ := (2 : ℝ) ^ (-(TQ : ℤ))
  have hqQ : 0 < qQ := by positivity
  have hrel : (2 : ℝ) ^ (-((T - TQ : ℕ) : ℤ)) = (2 : ℝ) ^ (-(T : ℤ)) / qQ := rel_length hTQ
  have hW0 : ENNReal.ofReal qQ * ν AQ ≠ 0 := mul_ne_zero (by simp [hqQ]) hν0
  have hWt : ENNReal.ofReal qQ * ν AQ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνt
  have h2 := mul_le_mul_right hfloor (ENNReal.ofReal qQ * ν AQ)
  rw [← mul_assoc (ENNReal.ofReal qQ * ν AQ) _ (ρ (G ∩ zoomTime t₀ qQ ⁻¹' E')),
    ENNReal.mul_inv_cancel hW0 hWt, one_mul] at h2
  refine le_trans (le_of_eq ?_) (h2.trans (measure_mono hsub))
  rw [hrel]
  have hq0 : ENNReal.ofReal qQ ≠ 0 := by simp [hqQ]
  have hqt : ENNReal.ofReal qQ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [mul_div_assoc', ENNReal.ofReal_div_of_pos hqQ]
  have e1 : ENNReal.ofReal qQ * ν AQ *
      (ENNReal.ofReal (c * (2 : ℝ) ^ (-(T : ℤ))) / ENNReal.ofReal qQ * ((ν AQ)⁻¹ * ν A)) =
      ENNReal.ofReal (c * (2 : ℝ) ^ (-(T : ℤ))) * ν A *
        ((ENNReal.ofReal qQ * (ENNReal.ofReal qQ)⁻¹) * (ν AQ * (ν AQ)⁻¹)) := by
    rw [ENNReal.div_eq_inv_mul]; ring
  rw [e1, ENNReal.mul_inv_cancel hq0 hqt, ENNReal.mul_inv_cancel hν0 hνt, one_mul, mul_one]

/-- A coefficient budget for the inverse row normalization. -/
def unskewBudget (B : Fin 2 → ℝ) (lam : ℝ) : ℝ := 1 + |lam| + |B 0| + |B 1|

theorem one_le_unskewBudget (B : Fin 2 → ℝ) (lam : ℝ) : 1 ≤ unskewBudget B lam := by
  unfold unskewBudget; have := abs_nonneg lam; have := abs_nonneg (B 0)
  have := abs_nonneg (B 1); linarith

theorem coeffL1_unskewSubst (B : Fin 2 → ℝ) (lam : ℝ) (i : Fin 4) :
    coeffL1 (unskewSubst B lam i) ≤ unskewBudget B lam := by
  have h1 := one_le_unskewBudget B lam
  fin_cases i
  · simpa [unskewSubst, coeffL1_X] using h1
  · simpa [unskewSubst, coeffL1_X] using h1
  · change coeffL1 (C lam * X 2 + C (B 0) * X 0 + C (B 1) * X 1 : MvPolynomial (Fin 4) ℝ) ≤ _
    have hm : ∀ (u : ℝ) (j : Fin 4), coeffL1 (C u * X j : MvPolynomial (Fin 4) ℝ) ≤ |u| :=
      fun u j => (coeffL1_C_mul_le _ _).trans (by rw [coeffL1_X, mul_one])
    calc coeffL1 (C lam * X 2 + C (B 0) * X 0 + C (B 1) * X 1 : MvPolynomial (Fin 4) ℝ)
        ≤ coeffL1 (C lam * X 2 + C (B 0) * X 0 : MvPolynomial (Fin 4) ℝ) +
            coeffL1 (C (B 1) * X 1 : MvPolynomial (Fin 4) ℝ) := coeffL1_add_le _ _
      _ ≤ (coeffL1 (C lam * X 2 : MvPolynomial (Fin 4) ℝ) +
            coeffL1 (C (B 0) * X 0 : MvPolynomial (Fin 4) ℝ)) +
            coeffL1 (C (B 1) * X 1 : MvPolynomial (Fin 4) ℝ) :=
          add_le_add (coeffL1_add_le _ _) le_rfl
      _ ≤ (|lam| + |B 0|) + |B 1| := add_le_add (add_le_add (hm _ _) (hm _ _)) (hm _ _)
      _ ≤ unskewBudget B lam := by unfold unskewBudget; linarith
  · simpa [unskewSubst, coeffL1_X] using h1

/-- Coefficients of a pushed and row-normalized test. -/
theorem coeffL1_nPush_le (Z : Zoom) (B : Fin 2 → ℝ) (lam : ℝ) (F : MvPolynomial (Fin 4) ℝ)
    (hF : F.totalDegree ≤ 2) :
    coeffL1 (Zoom.nPush Z B lam F) ≤
      |Z.a⁻¹| * coeffL1 F * Z.pushBudget ^ 2 * unskewBudget B lam ^ 2 := by
  have hdeg : (Z.push F).totalDegree ≤ 2 := (Zoom.push_degree F).trans hF
  have h1 := coeffL1_bind₁_le (unskewSubst B lam) (unskewBudget B lam)
    (one_le_unskewBudget B lam) (coeffL1_unskewSubst B lam) (Z.push F)
  have h2 := Zoom.coeffL1_push_le (Z := Z) F hF
  calc coeffL1 (Zoom.nPush Z B lam F)
      ≤ coeffL1 (Z.push F) * unskewBudget B lam ^ (Z.push F).totalDegree := h1
    _ ≤ coeffL1 (Z.push F) * unskewBudget B lam ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_unskewBudget B lam) hdeg)
          (coeffL1_nonneg _)
    _ ≤ (|Z.a⁻¹| * coeffL1 F * Z.pushBudget ^ 2) * unskewBudget B lam ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)

/-- Fits survive widening the width by a bounded factor, at a proportional loss. -/
theorem Zoom.Fits.widen {Q : MvPolynomial (Fin 4) ℝ} {b : Fin 6 → ℝ} {I : Set ℝ} {H c c' L : ℝ}
    (h : Zoom.Fits Q b I H c) (hc : 0 < c) (hH : 0 ≤ H) (hL : 1 ≤ L) (h1 : c ≤ c')
    (h2 : c' ≤ L * c) : Zoom.Fits Q b I (L * H) c' := by
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := h t ht
  have hc' : 0 < c' := lt_of_lt_of_le hc h1
  refine ⟨?_, ?_, ?_⟩
  · calc |eval (point b t) Q| ≤ H * c := hv
      _ ≤ H * c' := mul_le_mul_of_nonneg_left h1 hH
      _ ≤ L * H * c' := by
          have h0 : 0 ≤ H * c' := mul_nonneg hH hc'.le
          nlinarith
  · nlinarith
  · calc |eval (point b t) (pderiv 3 (pderiv 3 Q))| ≤ H / c := hdd
      _ ≤ L * H / c' := by
          rw [div_le_div_iff₀ hc hc']
          nlinarith

/-- Fits are monotone in the height. -/
theorem Zoom.Fits.mono_height {Q : MvPolynomial (Fin 4) ℝ} {b : Fin 6 → ℝ} {I : Set ℝ}
    {H H' c : ℝ} (h : Zoom.Fits Q b I H c) (hc : 0 < c) (hH : H ≤ H') :
    Zoom.Fits Q b I H' c := by
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := h t ht
  refine ⟨hv.trans (mul_le_mul_of_nonneg_right hH hc.le), hd.trans hH,
    hdd.trans (div_le_div_of_nonneg_right hH hc.le)⟩

namespace ZoomSeq

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} {Z : ZoomSeq p a r}

set_option maxHeartbeats 1600000 in
/-- **Pullback of one zoomed candidate** to an original candidate at the grid
depth of its label. -/
theorem candidate_pullback (hp : p.Valid) (ha : a.Valid p) (hZ : Z.Good) (m : ℕ)
    {R' ε R'' ε'' Bd c₀ : ℝ} (hR' : 1 < R') (hε : 0 < ε)
    (hR''r : R''⁻¹ ≤ r) (hR'' : r + R' ≤ R'')
    (hδR : (Z.I m).δ ≤ R'⁻¹) (hδε : ε + (Z.I m).δ ≤ ε'')
    (hM₁ε : Z.M₁ m * p.N (Z.I m).k ^ ε ≤ p.N (Z.I m).k ^ ε'')
    (hzbd : p.K (Z.I m).k + Z.M₁ m + Z.M₁ m * p.N (Z.I m).k ^ R' ≤ p.N (Z.I m).k ^ R'')
    (hsB : skewBudget (Z.I m).B (Z.I m).lam ≤ Bd) (hlB : (Z.I m).Z.liftBudget ≤ Bd)
    (hpB : (Z.I m).Z.pushBudget ≤ Bd) (huB : unskewBudget (Z.I m).B (Z.I m).lam ≤ Bd)
    (haB : |(Z.I m).Z.a⁻¹| ≤ Bd)
    (hBdN : 81 ^ 2 * Bd ^ 4 * p.N (Z.I m).k ^ R' * (Bd ^ 5 + p.N (Z.I m).k ^ c₀) ^ R' ≤
      p.N (Z.I m).k ^ R'')
    (hsheet : ∀ (j : Fin (Z.I m).M) (x : (Z.I m).Ret j),
      1 + coeffL1 (Z.I m).Pn ≤ p.N (Z.I m).k ^ c₀ *
        ((1 + coeffL1 (a.F (Z.I m).k ((Z.I m).depth j) x.1.1)) + coeffL1 (a.P (Z.I m).k)))
    (hc : Z.model.Candidate Z.params R' ε m) :
    a.Candidate p R'' ε'' (Z.I m).k := by
  obtain ⟨σ, v, i, hσ1, hσ2, hv1, hv2, hσv, hcase⟩ := hc
  set J := Z.I m with hJ
  have hr := hZ.r_pos
  have hcommon := ha.1
  have := hcommon.prob J.k
  have hN0 : 0 < p.N J.k := by linarith [hp.1 J.k]
  have hN1 : 1 ≤ p.N J.k := by linarith [hp.1 J.k]
  have hK1 := hp.2.2.1.1 J.k
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hδ := hZ.δ_pos m
  have hR'pos : 0 < R' := by linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (inv_pos.mpr hR'pos) hσ1
  have hvpos : 0 < v := lt_of_lt_of_le (inv_pos.mpr hR'pos) hv1
  have hσv' : σ + v ≤ Z.U' := hσv
  have hσU : σ ≤ ((J.M : ℝ) + 1) * J.δ := by
    have := hZ.U'_le m; linarith
  obtain ⟨hg1, hg2⟩ := J.lev_gap (Z.hM m) hδ (hδR.trans hσ1) hσU
  set jσ := J.lev (Z.hM m) σ with hjσ
  set x := (Fintype.equivFin (J.Ret jσ)).symm i with hx
  set s := J.depth jσ with hs
  have hsr : s - r = (((jσ : ℕ) : ℝ) + 1) * J.δ := by simp only [s, ZoomInput.depth]; ring
  have hs1 : r ≤ s := by
    have : 0 ≤ (((jσ : ℕ) : ℝ) + 1) * J.δ := by positivity
    linarith
  have hs2 : s ≤ r + σ := by linarith
  have hs3 : r + σ - J.δ ≤ s := by linarith
  have hR'R'' : R' ≤ R'' := by linarith
  have hatr := hZ.atlas_r m
  have hats := hZ.atlas_depth m
  have hkeep := J.measurable_keep hats (hZ.G_meas m)
  have hTQ := level_le_of_interval_subset (J.block_sub x)
  have hA := (hats jσ).measurable_A x.1.1
  have hAQ := J.prior_sub x
  have hν0 := hatr.prior_pos hp J.Q
  have hνt : a.nu J.k (a.A J.k r J.Q) ≠ ⊤ := measure_ne_top _ _
  have hb := (hcommon J.k).1
  have hβ : Measurable (fun l => Zoom.nCoeff J.Z J.B J.lam (a.b J.k l)) :=
    J.continuous_nCoeff.measurable.comp hb
  have hpow : ∀ c : ℝ, c / (2 : ℝ) ^ (a.T J.k s - a.T J.k r) =
      c * (2 : ℝ) ^ (-((a.T J.k s - a.T J.k r : ℕ) : ℤ)) := by
    intro c; rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  have hpowT : ∀ c : ℝ, c / (2 : ℝ) ^ a.T J.k s = c * (2 : ℝ) ^ (-(a.T J.k s : ℤ)) := by
    intro c; rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  refine ⟨s, v, x.1.1, hR''r.trans hs1, by linarith, (inv_anti₀ hR'pos hR'R'').trans hv1,
    hv2.trans hR'R'', ?_, ?_⟩
  · have := hZ.depth_le m
    have := hZ.U'_le m
    linarith
  rcases hcase with ⟨Q', hQdeg, hQcoeff, hQfloor⟩ | ⟨z, hz, hzfloor⟩
  · left
    have hFdeg : (a.F J.k s x.1.1).totalDegree ≤ 2 := ((hats jσ).2.2.2.2.1 x.1.1).2.2.2.2.1
    refine ⟨Zoom.nLift J.Z J.B J.lam Q', (Zoom.nLift_degree Q').trans hQdeg, ?_, ?_⟩
    · -- coefficients
      intro e
      set F := a.F J.k s x.1.1 with hFdef
      set F' := Zoom.nPush J.Z J.B J.lam F with hF'def
      set Pn := J.Pn with hPndef
      set Ψ := (1 + coeffL1 F) + coeffL1 (a.P J.k) with hΨ
      have hQ' : ∀ e, |Q'.coeff e| ≤ p.N J.k ^ R' * ((1 + coeffL1 F') + coeffL1 Pn) ^ R' :=
        fun e => hQcoeff e
      set X' := (1 + coeffL1 F') + coeffL1 Pn with hX'
      have hF0 := coeffL1_nonneg F
      have hP0 := coeffL1_nonneg (a.P J.k)
      have hF'0 := coeffL1_nonneg F'
      have hPn0 := coeffL1_nonneg Pn
      have hΨ1 : 1 ≤ Ψ := by linarith
      have hX'0 : 0 ≤ X' := by linarith
      have hBd1 : 1 ≤ Bd := (Submission.Lib.K4ContactNormalization.one_le_skewBudget _ _).trans hsB
      have hBd0 : 0 ≤ Bd := by linarith
      have hL1Q : coeffL1 Q' ≤ 81 * (p.N J.k ^ R' * X' ^ R') := by
        have := Submission.Lib.K4ChartLifting.coeffL1_le_of_coeff_le Q' hQdeg _ hQ'
        norm_num at this
        exact this
      have hF' : coeffL1 F' ≤ Bd ^ 5 * coeffL1 F := by
        have h1 := coeffL1_nPush_le J.Z J.B J.lam F hFdeg
        have hpB0 : 0 ≤ J.Z.pushBudget := le_trans zero_le_one (Zoom.one_le_pushBudget)
        have huB0 : 0 ≤ unskewBudget J.B J.lam := le_trans zero_le_one (one_le_unskewBudget _ _)
        calc coeffL1 F' ≤ |J.Z.a⁻¹| * coeffL1 F * J.Z.pushBudget ^ 2 *
              unskewBudget J.B J.lam ^ 2 := h1
          _ ≤ Bd * coeffL1 F * Bd ^ 2 * Bd ^ 2 := by gcongr
          _ = Bd ^ 5 * coeffL1 F := by ring
      have hsh := hsheet jσ x
      have hX'le : X' ≤ (Bd ^ 5 + p.N J.k ^ c₀) * Ψ := by
        have hN0c : 0 ≤ p.N J.k ^ c₀ := by positivity
        have hB5 : 0 ≤ Bd ^ 5 := by positivity
        calc X' = coeffL1 F' + (1 + coeffL1 Pn) := by rw [hX']; ring
          _ ≤ Bd ^ 5 * coeffL1 F + p.N J.k ^ c₀ * Ψ := add_le_add hF' hsh
          _ ≤ Bd ^ 5 * Ψ + p.N J.k ^ c₀ * Ψ := by
              gcongr
              linarith
          _ = (Bd ^ 5 + p.N J.k ^ c₀) * Ψ := by ring
      have hcoef := Zoom.coeff_nLift_le (Z := J.Z) (B := J.B) (lam := J.lam) Q' hQdeg e
      have h81 : (((2 + 1) ^ 4 : ℕ) : ℝ) = 81 := by norm_num
      rw [h81] at hcoef
      have ha1 : |J.Z.a| ≤ 1 := by
        rw [J.Z_a, abs_of_pos (width_pos p hp J.k r)]
        unfold width
        exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      have hR'0 : 0 ≤ R' := hR'pos.le
      have hXp : X' ^ R' ≤ (Bd ^ 5 + p.N J.k ^ c₀) ^ R' * Ψ ^ R' := by
        rw [← Real.mul_rpow (by positivity) (by linarith)]
        exact Real.rpow_le_rpow hX'0 hX'le hR'0
      have hΨp : Ψ ^ R' ≤ Ψ ^ R'' := Real.rpow_le_rpow_of_exponent_le hΨ1 hR'R''
      have hsB0 : 0 ≤ skewBudget J.B J.lam := le_trans zero_le_one (Submission.Lib.K4ContactNormalization.one_le_skewBudget _ _)
      have hlB0 : 0 ≤ J.Z.liftBudget := le_trans zero_le_one Zoom.one_le_liftBudget
      show |(Zoom.nLift J.Z J.B J.lam Q').coeff e| ≤ p.N J.k ^ R'' * Ψ ^ R''
      calc |(Zoom.nLift J.Z J.B J.lam Q').coeff e|
          ≤ |J.Z.a| * (coeffL1 Q' * skewBudget J.B J.lam ^ 2 * (((2 + 1) ^ 4 : ℕ) : ℝ)) *
              J.Z.liftBudget ^ 2 := hcoef
        _ ≤ 1 * ((81 * (p.N J.k ^ R' * X' ^ R')) * Bd ^ 2 * 81) * Bd ^ 2 := by
            have hcQ : coeffL1 Q' * skewBudget J.B J.lam ^ 2 * 81 ≤
                (81 * (p.N J.k ^ R' * X' ^ R')) * Bd ^ 2 * 81 :=
              mul_le_mul_of_nonneg_right (mul_le_mul hL1Q (pow_le_pow_left₀ hsB0 hsB 2)
                (by positivity) (by positivity)) (by norm_num)
            have hA0 : 0 ≤ coeffL1 Q' * skewBudget J.B J.lam ^ 2 * 81 :=
              mul_nonneg (mul_nonneg (coeffL1_nonneg _) (by positivity)) (by norm_num)
            exact mul_le_mul (mul_le_mul ha1 hcQ hA0 zero_le_one)
              (pow_le_pow_left₀ hlB0 hlB 2) (by positivity) (by positivity)
        _ = 81 ^ 2 * Bd ^ 4 * p.N J.k ^ R' * X' ^ R' := by ring
        _ ≤ 81 ^ 2 * Bd ^ 4 * p.N J.k ^ R' * ((Bd ^ 5 + p.N J.k ^ c₀) ^ R' * Ψ ^ R') := by
            gcongr
        _ = (81 ^ 2 * Bd ^ 4 * p.N J.k ^ R' * (Bd ^ 5 + p.N J.k ^ c₀) ^ R') * Ψ ^ R' := by ring
        _ ≤ p.N J.k ^ R'' * Ψ ^ R'' := by
            gcongr
    · -- the floor
      have hq' : ENNReal.ofReal (p.N J.k ^ (-p.d * v - ε) / (2 : ℝ) ^ (a.T J.k s - a.T J.k r)) *
          condPrior (a.nu J.k) (a.A J.k r J.Q) (a.A J.k s x.1.1) ≤
          zoomLaw (a.rho J.k) J.keep J.Z.t₀ J.Z.q J.W
            {w | w.1 ∈ a.B J.k s x.1.1 ∧ w.2 ∈ J.zblock x ∧
              Zoom.Fits Q' (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) (J.zblock x)
                (p.N J.k ^ ε) (p.N J.k ^ (-σ - v)) ∧
              p.N J.k ^ (-ε) ≤ |eval (point (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) w.2)
                (pderiv 3 Q')|} := hQfloor
      rw [hpow] at hq'
      have hE' : MeasurableSet {w : α × ℝ | w.1 ∈ a.B J.k s x.1.1 ∧ w.2 ∈ J.zblock x ∧
          Zoom.Fits Q' (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) (J.zblock x)
            (p.N J.k ^ ε) (p.N J.k ^ (-σ - v)) ∧
          p.N J.k ^ (-ε) ≤ |eval (point (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) w.2)
            (pderiv 3 Q')|} := by
        refine ((hats jσ).measurable_B _ |>.preimage measurable_fst).inter
          ((measurableSet_Icc.preimage measurable_snd).inter
            (MeasurableSet.inter ?_ ?_))
        · exact (measurableSet_fit_line hβ Q' (J.zblock x) _ _).preimage measurable_fst
        · exact measurableSet_le measurable_const (J.measurable_eval_line hb _).abs
      have hfl := pullback_floor (ν := a.nu J.k) (ρ := a.rho J.k) hkeep hA hAQ hν0 hνt hTQ
        J.Z.t₀ hE' (E := {w | w.1 ∈ a.B J.k s x.1.1 ∧ w.2 ∈ a.block J.k s x.1.1 ∧
          a.fit J.k (p.N J.k ^ ε'') (p.N J.k ^ (-s - v)) (Zoom.nLift J.Z J.B J.lam Q') w.1
            (a.block J.k s x.1.1) ∧
          p.N J.k ^ (-ε'') ≤ |eval (a.x J.k w.1 w.2) (pderiv 3 (Zoom.nLift J.Z J.B J.lam Q'))|})
        ?_ hq'
      · refine le_trans ?_ hfl
        rw [hpowT]
        gcongr
        first
          | linarith only [hδε, hδ]
          | exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδε, hδ])
      · rintro w ⟨_, hwB, hwI, hwF, hwD⟩
        refine ⟨hwB, (J.mem_zblock x w.2).mpr hwI, ?_, ?_⟩
        · have h1 := Zoom.nLift_fits (B := J.B) (lam := J.lam) (J.Z_ok hp)
            (width_pos p hp J.k r) hwF
          have h2 : Zoom.Fits (Zoom.nLift J.Z J.B J.lam Q') (a.b J.k w.1) (a.block J.k s x.1.1)
              (p.N J.k ^ ε) (J.Z.a * p.N J.k ^ (-σ - v)) := by
            intro t ht
            exact h1 t ((J.mem_zblock x t).mp ht)
          have hca : J.Z.a * p.N J.k ^ (-σ - v) = p.N J.k ^ (-r - σ - v) := by
            rw [J.Z_a]; simp only [width]; rw [← Real.rpow_add hN0]; ring_nf
          rw [hca] at h2
          have h3 := h2.widen (Real.rpow_pos_of_pos hN0 _) (by positivity)
            (Real.one_le_rpow hN1 hδ.le) (c' := p.N J.k ^ (-s - v))
            (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hs2]))
            (by
              rw [← Real.rpow_add hN0]
              exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hs3]))
          have h4 := h3.mono_height (Real.rpow_pos_of_pos hN0 _)
            (H' := p.N J.k ^ ε'') (by
              rw [← Real.rpow_add hN0]
              exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδε]))
          exact h4
        · have he := Zoom.eval_pderiv_nLift (B := J.B) (lam := J.lam) Q' (J.Z_ok hp)
            (a.b J.k w.1) w.2
          simp only [PreparedModel.x]
          rw [he]
          refine le_trans ?_ hwD
          exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδε, hδ])
  · right
    have hg := narrow_pos p hp J.k r
    have hg1 : narrow p J.k r ≤ 1 := by
      unfold narrow
      apply Real.rpow_le_one_of_one_le_of_nonpos hN1
      nlinarith
    have hwq : J.Z.w / J.Z.q = narrow p J.k r := by
      rw [J.Z_w, J.Z_q]; field_simp [(q_pos a J.k r).ne']
    have hc := (hatr.2.2.2.2.1 J.Q).2.2.2.1
    refine ⟨![J.Z.c₃ + J.Z.w / J.Z.q * (J.B 0 + J.lam * z 0),
      J.Z.c₄ + J.Z.w / J.Z.q * (J.B 1 + J.lam * z 1)], ?_, ?_⟩
    · have hB0 : |J.B 0| ≤ Z.M₁ m := by
        have := hZ.B_le m; have := abs_nonneg (J.B 1); linarith
      have hB1 : |J.B 1| ≤ Z.M₁ m := by
        have := hZ.B_le m; have := abs_nonneg (J.B 0); linarith
      have hlam := hZ.lam_le m
      have hM₁0 : 0 ≤ Z.M₁ m := le_trans zero_le_one (hZ.M₁_ge m)
      have key : ∀ (c Bv zv : ℝ), |c| ≤ p.K J.k → |Bv| ≤ Z.M₁ m → |zv| ≤ p.N J.k ^ R' →
          |c + J.Z.w / J.Z.q * (Bv + J.lam * zv)| ≤ p.N J.k ^ R'' := by
        intro c Bv zv hc' hB' hz'
        rw [hwq]
        calc |c + narrow p J.k r * (Bv + J.lam * zv)|
            ≤ |c| + narrow p J.k r * (|Bv| + |J.lam| * |zv|) := by
              refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
              rw [abs_mul, abs_of_pos hg]
              refine mul_le_mul_of_nonneg_left ?_ hg.le
              exact (abs_add_le _ _).trans (by rw [abs_mul])
          _ ≤ p.K J.k + 1 * (Z.M₁ m + Z.M₁ m * p.N J.k ^ R') := by
              gcongr
          _ ≤ p.N J.k ^ R'' := by linarith
      intro e
      fin_cases e
      · exact key _ _ _ (hc 3) hB0 (hz 0)
      · exact key _ _ _ (hc 4) hB1 (hz 1)
    · -- the floor
      have hz' : ENNReal.ofReal (p.N J.k ^ (-ε) / (2 : ℝ) ^ (a.T J.k s - a.T J.k r)) *
          condPrior (a.nu J.k) (a.A J.k r J.Q) (a.A J.k s x.1.1) ≤
          zoomLaw (a.rho J.k) J.keep J.Z.t₀ J.Z.q J.W
            {w | w.1 ∈ a.B J.k s x.1.1 ∧ w.2 ∈ J.zblock x ∧
              |Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1) 4 - z 0 -
                z 1 * Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1) 3| ≤
                p.N J.k ^ ε * p.N J.k ^ (-p.ell * σ - v)} := hzfloor
      rw [hpow] at hz'
      have hE' : MeasurableSet {w : α × ℝ | w.1 ∈ a.B J.k s x.1.1 ∧ w.2 ∈ J.zblock x ∧
          |Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1) 4 - z 0 -
            z 1 * Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1) 3| ≤
            p.N J.k ^ ε * p.N J.k ^ (-p.ell * σ - v)} := by
        refine ((hats jσ).measurable_B _ |>.preimage measurable_fst).inter
          ((measurableSet_Icc.preimage measurable_snd).inter ?_)
        have h4 : Measurable (fun l => Zoom.nCoeff J.Z J.B J.lam (a.b J.k l) 4) :=
          (measurable_pi_apply 4).comp hβ
        have h3 : Measurable (fun l => Zoom.nCoeff J.Z J.B J.lam (a.b J.k l) 3) :=
          (measurable_pi_apply 3).comp hβ
        exact (measurableSet_le (((h4.sub_const _).sub (h3.const_mul _)).abs)
          measurable_const).preimage measurable_fst
      have hfl := pullback_floor (ν := a.nu J.k) (ρ := a.rho J.k) hkeep hA hAQ hν0 hνt hTQ
        J.Z.t₀ hE' (E := {w | w.1 ∈ a.B J.k s x.1.1 ∧ w.2 ∈ a.block J.k s x.1.1 ∧
          |a.b J.k w.1 4 - (J.Z.c₃ + J.Z.w / J.Z.q * (J.B 0 + J.lam * z 0)) -
            (J.Z.c₄ + J.Z.w / J.Z.q * (J.B 1 + J.lam * z 1)) * a.b J.k w.1 3| ≤
            p.N J.k ^ ε'' * p.N J.k ^ (-p.ell * s - v)}) ?_ hz'
      · refine le_trans ?_ hfl
        rw [hpowT]
        gcongr
        first
          | linarith only [hδε, hδ]
          | exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδε, hδ])
      · rintro w ⟨_, hwB, hwI, hwS⟩
        refine ⟨hwB, (J.mem_zblock x w.2).mpr hwI, ?_⟩
        have h1 := strip_pullback (J.Z_ok hp) (hZ.lam_ne m) hwS
        refine h1.trans ?_
        rw [hwq, abs_mul, abs_of_pos hg]
        have hlam := hZ.lam_le m
        have hNs : p.N J.k ^ (-p.ell * r) * p.N J.k ^ (-p.ell * σ - v) ≤
            p.N J.k ^ (-p.ell * s - v) := by
          rw [← Real.rpow_add hN0]
          apply Real.rpow_le_rpow_of_exponent_le hN1
          have := mul_le_mul_of_nonneg_left hs2 hℓ.le
          linarith only [this]
        have hg' : narrow p J.k r = p.N J.k ^ (-p.ell * r) := rfl
        calc narrow p J.k r * |J.lam| * (p.N J.k ^ ε * p.N J.k ^ (-p.ell * σ - v))
            = |J.lam| * p.N J.k ^ ε * (p.N J.k ^ (-p.ell * r) * p.N J.k ^ (-p.ell * σ - v)) := by
              rw [hg']; ring
          _ ≤ Z.M₁ m * p.N J.k ^ ε * p.N J.k ^ (-p.ell * s - v) := by
              gcongr
              exact mul_nonneg (le_trans zero_le_one (hZ.M₁_ge m)) (by positivity)
          _ ≤ p.N J.k ^ ε'' * p.N J.k ^ (-p.ell * s - v) :=
              mul_le_mul_of_nonneg_right hM₁ε (by positivity)

end ZoomSeq

end

end Submission.Obl.k4_row_parent_contact_candidates
