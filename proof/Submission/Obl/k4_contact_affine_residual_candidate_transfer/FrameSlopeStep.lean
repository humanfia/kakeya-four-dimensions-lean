import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameBoxes

/-!
# One calibration step on a residual label

The box calibration applied to the incidence law of one residual label: an
affine function small on the label's incidences has small box-adapted slopes,
given the label's mass and capped base cells.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4MovingMeshBoxes
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- The incidence set of a residual label. -/
def Frame.labelSet (f : Frame D k s₀ U') (h : ℕ) (i : Fin (f.retained h).card) :
    Set (α × ℝ) :=
  (f.level h).B i ×ˢ Data.I (f.level h).T ((f.level h).j i)

/-- The incidence law of a residual label. -/
def Frame.nodeLaw (f : Frame D k s₀ U') (h : ℕ) (i : Fin (f.retained h).card) :
    Measure (α × ℝ) :=
  f.resμ.restrict (f.labelSet h i)

/-- The box constant. -/
def boxK (K K₂ : ℝ) : ℝ := 50 * K ^ 4 * K₂ ^ 2

theorem FrameGood.measurable_coeff (hg : FrameGood f Rk θ K₂ e₀') (e : Fin 6)
    (he : e ≠ 2 ∧ e ≠ 5) : Measurable (fun l => f.coeff l e) := by
  have hb (e' : Fin 6) : Measurable (fun l => D.b k l e') :=
    (measurable_pi_apply e').comp hg.bmeas
  have h0 := hb 0; have h1 := hb 1; have h3 := hb 3; have h4 := hb 4
  have : (fun l => f.coeff l e) =
      fun l => contactChartCoeff f.t₀ f.q₀ f.Z₀ f.Y₀ (D.b k l) e := by
    funext l; exact f.coeff_base l e he
  rw [this]
  fin_cases e <;> simp only [contactChartCoeff] <;> simp at he ⊢ <;> fun_prop

theorem FrameGood.measurable_resBase (hg : FrameGood f Rk θ K₂ e₀') :
    Measurable f.resBase := by
  have h0 := hg.measurable_coeff 0 (by decide)
  have h1 := hg.measurable_coeff 1 (by decide)
  have h3 := hg.measurable_coeff 3 (by decide)
  have h4 := hg.measurable_coeff 4 (by decide)
  apply measurable_pi_lambda
  intro e
  fin_cases e
  · exact measurable_snd
  · simp only [resBase, point, Matrix.cons_val_one, Matrix.head_cons]
    exact (h0.comp measurable_fst).add (measurable_snd.mul (h3.comp measurable_fst))
  · simp only [resBase, point, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact (h1.comp measurable_fst).add (measurable_snd.mul (h4.comp measurable_fst))

theorem one_le_boxK {K K₂ : ℝ} (hK : 1 ≤ K) (hK₂ : 1 ≤ K₂) : 1 ≤ boxK K K₂ := by
  unfold boxK
  have h1 := one_le_pow₀ (n := 4) hK
  have h2 := one_le_pow₀ (n := 2) hK₂
  nlinarith

theorem FrameGood.measurableSet_labelSet (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ}
    (hh : h ≤ f.m) (i : Fin (f.retained h).card) : MeasurableSet (f.labelSet h i) :=
  (hg.measurableSet_hist hh _ _).prod measurableSet_Icc

theorem FrameGood.nodeLaw_finite (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) : IsFiniteMeasure (f.nodeLaw h i) := by
  have := hg.νprob
  refine ⟨?_⟩
  rw [Frame.nodeLaw, Measure.restrict_apply_univ,
    f.resμ_apply (hg.measurableSet_labelSet hh i) hg.core_meas,
    show f.toChart ⁻¹' f.labelSet h i = _ from hg.preimage_label hh i]
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hg.scale_pos) ?_
  calc D.μ k (f.event h (f.node h i).1 (f.node h i).2 ∩ f.core)
      ≤ D.μ k (f.event h (f.node h i).1 (f.node h i).2) := measure_mono inter_subset_left
    _ ≤ (ENNReal.ofReal (D.K k) • (D.ν k).prod volume)
        (f.event h (f.node h i).1 (f.node h i).2) := hg.dom _
    _ < ⊤ := by
      rw [Measure.smul_apply, smul_eq_mul, event, Measure.prod_prod]
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top
        (measure_lt_top _ _) ?_)
      rw [f.block_eq_Icc, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top

theorem Frame.resMid_mem (f : Frame D k s₀ U') (h : ℕ) (i : Fin (f.retained h).card) :
    0 ≤ f.resMid h i ∧ f.resMid h i ≤ 1 := by
  have hj : ((f.level h).j i : ℕ) < 2 ^ f.resT h := ((f.level h).j i).isLt
  have hjr : ((((f.level h).j i : ℕ)) : ℝ) + 1 ≤ 2 ^ f.resT h := by
    exact_mod_cast hj
  simp only [resMid, resq, zpow_neg, zpow_natCast]
  have h2 : (0 : ℝ) < 2 ^ f.resT h := by positivity
  constructor
  · positivity
  · rw [← div_eq_mul_inv, div_le_one h2]; linarith

theorem Frame.resq_le_one (f : Frame D k s₀ U') (h : ℕ) : f.resq h ≤ 1 := by
  simp only [resq, zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- One box calibration on the incidences of a residual label. -/
theorem FrameGood.node_slopes (hg : FrameGood f Rk θ K₂ e₀') {A₀ : ℝ}
    (hA : BoxCalibration A₀) {h : ℕ} (hh : h ≤ f.m) (i : Fin (f.retained h).card)
    (L : Fin 4 → ℝ) {E C m δh : ℝ} (hE : 0 ≤ E) (hC : 0 < C) (hm : 0 < m)
    (hδh : 0 < δh)
    (habs : A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
      (1 + boxBeta (boxK (D.K k) K₂) C (f.resq h) / m) ^ (6 : ℕ) * δh ≤ 1 / 2)
    (hmass : ENNReal.ofReal m ≤ f.nodeLaw h i univ)
    (hcap : ∀ c : Fin 3 → ℤ, f.nodeLaw h i {p | baseMesh (f.resq h ^ 2 * δh) (f.resBase p) = c} ≤
      ENNReal.ofReal (C * (f.resq h ^ 2 * δh) ^ 3))
    (hval : ∀ l ∈ (f.level h).B i, ∀ τ ∈ Data.I (f.level h).T ((f.level h).j i),
      |L 0 + L 1 * τ + L 2 * point (f.coeff l) τ 1 + L 3 * point (f.coeff l) τ 2| ≤ E) :
    f.resq h * |L 1 - f.boxZ h i * L 3| ≤ A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
        (1 + boxBeta (boxK (D.K k) K₂) C (f.resq h) / m) ^ (6 : ℕ) * E ∧
      f.resq h * |L 2 + f.resMid h i * L 3| ≤ A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
        (1 + boxBeta (boxK (D.K k) K₂) C (f.resq h) / m) ^ (6 : ℕ) * E ∧
      f.resq h ^ 2 * |L 3| ≤ A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
        (1 + boxBeta (boxK (D.K k) K₂) C (f.resq h) / m) ^ (6 : ℕ) * E := by
  have hK : 1 ≤ D.K k := hg.K_ge
  have hK₂ : 1 ≤ K₂ := hg.K₂_ge
  have hbK := one_le_boxK hK hK₂
  haveI := hg.nodeLaw_finite hh i
  have hmid := f.resMid_mem h i
  have hK2 : 1 ≤ D.K k ^ 2 := one_le_pow₀ hK
  have hK4 : D.K k ^ 2 ≤ D.K k ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hK₂2 : K₂ ≤ K₂ ^ 2 := le_self_pow₀ hK₂ (by norm_num)
  have htc : |f.resMid h i| ≤ boxK (D.K k) K₂ := by
    rw [abs_of_nonneg hmid.1]; linarith [hmid.2]
  have hZc : |f.boxZ h i| ≤ boxK (D.K k) K₂ := by
    have h0 := hg.res_cbound hh i 0
    have h1 := hg.res_cbound hh i 1
    calc |f.boxZ h i| ≤ |(f.level h).c i 0| + |f.resMid h i| * |(f.level h).c i 1| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 20 * D.K k ^ 2 * K₂ + 1 * (20 * D.K k ^ 2 * K₂) := by
          gcongr
          · rw [abs_of_nonneg hmid.1]; exact hmid.2
      _ ≤ boxK (D.K k) K₂ := by
          unfold boxK
          have : D.K k ^ 2 * K₂ ≤ D.K k ^ 4 * K₂ ^ 2 :=
            mul_le_mul hK4 hK₂2 (by linarith) (by positivity)
          nlinarith
  apply hA (α × ℝ) (f.nodeLaw h i) f.resBase hg.measurable_resBase (f.resMid h i)
    (f.boxZ h i) (f.boxY h i) (f.resq h) δh (boxK (D.K k) K₂) C m E L (f.resq_pos h)
    (f.resq_le_one h) hδh hbK hC hm hE htc hZc habs hmass hcap
  rw [Frame.nodeLaw, ae_restrict_iff' (hg.measurableSet_labelSet hh i)]
  refine Filter.Eventually.of_forall fun p hp => ⟨fun e => ?_, ?_⟩
  · refine (hg.box_mem hh i p.1 hp.1 p.2 hp.2 e).trans ?_
    unfold boxK
    have : 0 ≤ D.K k ^ 4 * K₂ ^ 2 := by positivity
    linarith
  · exact hval p.1 hp.1 p.2 hp.2

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
