import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.ChartReturn
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameLabels
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameScales
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameLaw
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FramePriors

/-!
# Pulling residual candidates back to shifted candidates

At an index with a good frame, a polynomial or velocity candidate of the
residual model at a residual label of grid level `h` gives a shifted candidate
of the original data at the original label of the label's node, at the grid
depth `depth h = s₀ + h * U' / m`:

* the residual law of a set is the core mass of its chart preimage divided by
  the parent reference (`resρ_eq`, the chart being a measurable equivalence);
* the residual witness set lies in the original shifted witness set, with the
  shift by the parent's original affine entry and the polynomial returned by
  `shiftedChartPullback (chartSubst f) a₀`;
* the residual mass denominator `q' * ν'(A')` multiplied by the parent
  reference is `q_h * ν(history)`, and the history keeps `θ / K` of the
  original label.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted

open MeasureTheory Set Filter MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {Rk θ K₂ e₀' : ℝ} {f : Frame D k s₀ U'}

/-- The parent chart as a measurable equivalence. -/
def chartEquiv (f : Frame D k s₀ U') : (α × ℝ) ≃ᵐ (α × ℝ) where
  toFun := f.toChart
  invFun := fun p => (p.1, f.t₀ + f.q₀ * p.2)
  left_inv := by
    intro p
    have hq := f.q₀_pos
    simp only [Frame.toChart]
    ext
    · rfl
    · simp only; field_simp; ring
  right_inv := by
    intro p
    have hq := f.q₀_pos
    simp only [Frame.toChart]
    ext
    · rfl
    · simp only; field_simp; ring
  measurable_toFun := f.measurable_toChart
  measurable_invFun := measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))

theorem resρ_eq (hg : FrameGood f Rk θ K₂ e₀') (E : Set (α × ℝ)) :
    f.resρ E = f.scale⁻¹ * D.ρ k (f.toChart ⁻¹' E ∩ f.core) := by
  rw [Frame.resρ, Measure.smul_apply, smul_eq_mul]
  have hemb : MeasurableEmbedding f.toChart := (chartEquiv f).measurableEmbedding
  rw [hemb.map_apply, Measure.restrict_apply' hg.core_meas]

theorem scale_mul_resρ (hg : FrameGood f Rk θ K₂ e₀') (E : Set (α × ℝ)) :
    f.scale * f.resρ E = D.ρ k (f.toChart ⁻¹' E ∩ f.core) := by
  rw [resρ_eq hg, ← mul_assoc, ENNReal.mul_inv_cancel hg.scale_pos.ne' hg.scale_ne_top, one_mul]

/-- The parent reference times a residual reference is the original reference
of the history. -/
theorem scale_mul_reference (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    {X : Set α} (hX : MeasurableSet X) (hXP : X ⊆ f.parentSet) {c : ℝ} (hc : 0 ≤ c) :
    f.scale * (ENNReal.ofReal (c / (2 : ℝ) ^ f.resT h) * cond (D.ν k) f.parentSet X) =
      ENNReal.ofReal (c / (2 : ℝ) ^ f.Tl h) * D.ν k X := by
  haveI := hg.νprob
  have hP : 0 < (D.ν k).real f.parentSet := ENNReal.toReal_pos hg.parent_pos.ne' hg.parent_ne_top
  have hq := f.q₀_pos
  have hscale : f.scale = ENNReal.ofReal (f.q₀ * (D.ν k).real f.parentSet) := f.scale_eq_ofReal
  have hres : (2 : ℝ) ^ (-(f.resT h : ℤ)) = f.ql h / f.q₀ := hg.resq hh
  rw [hscale, hg.cond_eq hX hXP, ← ofReal_measureReal (μ := D.ν k) (s := X),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e1 : c / (2 : ℝ) ^ f.resT h = c * (f.ql h / f.q₀) := by
    rw [← hres, zpow_neg, zpow_natCast, div_eq_mul_inv]
  have e2 : c / (2 : ℝ) ^ f.Tl h = c * f.ql h := by
    simp [Frame.ql, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [e1, e2]
  field_simp

/-- The original reference of a node's history dominates `θ / K` of its
original label. -/
theorem reference_of_history (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) {c c' : ℝ} (hc : 0 ≤ c) (hcc : c * D.K k ≤ c' * θ) :
    ENNReal.ofReal (c / (2 : ℝ) ^ f.Tl h) * D.ν k (D.A k (f.depth h) (f.node h i).1) ≤
      ENNReal.ofReal (c' / (2 : ℝ) ^ f.Tl h) *
        D.ν k (f.hist h (f.node h i).1 (f.node h i).2) := by
  have hprior := hg.prior_floor hh _ _ (f.node_retained h i)
  have hθ := hg.θ_pos
  have hK : 1 ≤ D.K k := hg.K_ge
  have h2 : (0 : ℝ) < 2 ^ f.Tl h := by positivity
  have hc' : 0 ≤ c' := by
    by_contra hneg; push_neg at hneg
    have : c' * θ < 0 := mul_neg_of_neg_of_pos hneg hθ
    nlinarith [mul_nonneg hc (by linarith : (0 : ℝ) ≤ D.K k)]
  calc
    ENNReal.ofReal (c / (2 : ℝ) ^ f.Tl h) * D.ν k (D.A k (f.depth h) (f.node h i).1) =
        ENNReal.ofReal (c / (2 : ℝ) ^ f.Tl h / θ) *
          (ENNReal.ofReal θ * D.ν k (D.A k (f.depth h) (f.node h i).1)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
    _ ≤ ENNReal.ofReal (c / (2 : ℝ) ^ f.Tl h / θ) *
          (ENNReal.ofReal (D.K k) * D.ν k (f.hist h (f.node h i).1 (f.node h i).2)) :=
      mul_le_mul_right hprior _
    _ = ENNReal.ofReal (c * D.K k / θ / (2 : ℝ) ^ f.Tl h) *
          D.ν k (f.hist h (f.node h i).1 (f.node h i).2) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
    _ ≤ _ := by
      gcongr
      rw [div_le_iff₀ hθ]
      linarith

/-- Original label membership of a residual label's witnesses. -/
theorem witness_original (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) (p : α × ℝ)
    (hp1 : p.1 ∈ (f.level h).B i)
    (hp2 : (f.toChart p).2 ∈ Data.I (f.level h).T ((f.level h).j i)) :
    p.1 ∈ D.B k (f.depth h) (f.node h i).1 ∧
      p.2 ∈ Data.I (D.T k (f.depth h)) (D.j k (f.depth h) (f.node h i).1) := by
  refine ⟨f.entry_subset_B h _ _ (f.hist_subset_entry h _ _ hp1), ?_⟩
  exact (f.mem_resBlock_iff (hg.inside hh i).1 p).mp hp2

/-- An original time of a residual label is a residual time in parent units. -/
theorem time_of_original (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) {t : ℝ}
    (ht : t ∈ Data.I (D.T k (f.depth h)) (D.j k (f.depth h) (f.node h i).1)) :
    (t - f.t₀) / f.q₀ ∈ Data.I (f.level h).T ((f.level h).j i) ∧
      (t - f.t₀) / f.q₀ ∈ Icc (0 : ℝ) 1 := by
  refine ⟨(f.mem_resBlock_time (hg.inside hh i).1 t).mpr ht, ?_⟩
  have hb := (hg.inside hh i).1 ht
  rw [f.parent_block] at hb
  have hq := f.q₀_pos
  constructor
  · apply div_nonneg _ hq.le; linarith [hb.1]
  · rw [div_le_one hq]; linarith [hb.2]

/-- The shifted hidden coordinate is `a₀` times the residual one. -/
theorem shifted_hidden (f : Frame D k s₀ U') (hN : 0 < D.N k) (l : α) (t : ℝ) :
    shiftedPoint D k (parentL f) l t 3 = f.a₀ * point (f.coeff l) ((t - f.t₀) / f.q₀) 3 := by
  have h := congrFun (eval_chartSubst f l t) 3
  simp only [chartSubst] at h
  have ha := f.a₀_pos hN
  rw [← h]
  simp only [Fin.isValue, Matrix.cons_val, eval_mul, eval_C, eval_X]
  field_simp

/-- Pull back a residual polynomial candidate. -/
theorem poly_pullback (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) {s' v ε ε' R B C : ℝ}
    (Q : MvPolynomial (Fin 4) ℝ) (hQdeg : Q.totalDegree ≤ 2)
    (hQ : ∀ e, |Q.coeff e| ≤ D.N k ^ C) (hB : 0 ≤ B)
    (hσ : ∀ j, coeffL1 (chartSubst f j) ≤ D.N k ^ B) (hR : 0 + C + 2 * B + 7 ≤ R)
    (hgrid : f.depth h ≤ s₀ + s') (hgap : s₀ + s' + ε' ≤ f.depth h + ε) (hεε : ε' ≤ ε)
    (hs₀ : 0 ≤ s₀) (hHa : f.H * f.a₀ ≤ 1) (hθK : D.N k ^ (-D.d * v - ε) * D.K k ≤ D.N k ^ (-D.d * v - ε') * θ)
    (hcand : ENNReal.ofReal (D.N k ^ (-D.d * v - ε') / (2 : ℝ) ^ (f.level h).T) *
        cond (D.ν k) f.parentSet ((f.level h).A i) ≤
      f.resρ {p | p.1 ∈ (f.level h).B i ∧ p.2 ∈ Data.I (f.level h).T ((f.level h).j i) ∧
        (∀ τ ∈ Data.I (f.level h).T ((f.level h).j i),
          |eval (point (f.coeff p.1) τ) Q| ≤ D.N k ^ ε' * D.N k ^ (-s' - v) ∧
          |eval (point (f.coeff p.1) τ) (pderiv 3 Q)| ≤ D.N k ^ ε' ∧
          |eval (point (f.coeff p.1) τ) (pderiv 3 (pderiv 3 Q))| ≤
            D.N k ^ ε' / D.N k ^ (-s' - v)) ∧
        D.N k ^ (-ε') ≤ |eval (point (f.coeff p.1) p.2) (pderiv 3 Q)|}) :
    ShiftedPoly D k R ε (f.depth h) v (f.node h i).1 := by
  have hN2 : 2 ≤ D.N k := hg.N_ge
  have hN : 0 < D.N k := lt_of_lt_of_le two_pos hN2
  have hN1 : 1 ≤ D.N k := le_trans one_le_two hN2
  have ha := f.a₀_pos hN
  have hq := f.q₀_pos
  set G := shiftedChartPullback (chartSubst f) f.a₀ Q with hG
  have hσd := pderiv_chartSubst f
  refine ⟨parentL f, G, ?_, ?_, ?_⟩
  · exact (shiftedChartPullback_degree _ (chartSubst_degree f) _ Q).trans hQdeg
  · intro e
    have ha1 : f.a₀ ≤ 1 := by
      rw [Frame.a₀, hg.depth_zero]
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hc := coeff_shiftedChartPullback_power (chartSubst f) f.a₀ (D.N k) 0 B C hN2 hB
      (by rw [Real.rpow_zero, abs_of_pos ha]; exact ha1)
      hσ Q hQdeg hQ e
    exact hc.trans (Real.rpow_le_rpow_of_exponent_le hN1 hR)
  · -- the residual witness set returns into the shifted witness set
    set E' := {p : α × ℝ | p.1 ∈ (f.level h).B i ∧ p.2 ∈ Data.I (f.level h).T ((f.level h).j i) ∧
        (∀ τ ∈ Data.I (f.level h).T ((f.level h).j i),
          |eval (point (f.coeff p.1) τ) Q| ≤ D.N k ^ ε' * D.N k ^ (-s' - v) ∧
          |eval (point (f.coeff p.1) τ) (pderiv 3 Q)| ≤ D.N k ^ ε' ∧
          |eval (point (f.coeff p.1) τ) (pderiv 3 (pderiv 3 Q))| ≤
            D.N k ^ ε' / D.N k ^ (-s' - v)) ∧
        D.N k ^ (-ε') ≤ |eval (point (f.coeff p.1) p.2) (pderiv 3 Q)|} with hE'
    have hsub : f.toChart ⁻¹' E' ∩ f.core ⊆ {p | p.1 ∈ D.B k (f.depth h) (f.node h i).1 ∧
        p.2 ∈ Data.I (D.T k (f.depth h)) (D.j k (f.depth h) (f.node h i).1) ∧
        (∀ t ∈ Data.I (D.T k (f.depth h)) (D.j k (f.depth h) (f.node h i).1),
          |(shiftedPoint D k (parentL f) p.1 t) 3| ≤ 1 ∧
          |eval (shiftedPoint D k (parentL f) p.1 t) G| ≤
            D.N k ^ ε * D.N k ^ (-(f.depth h) - v) ∧
          |eval (shiftedPoint D k (parentL f) p.1 t) (pderiv (3 : Fin 4) G)| ≤ D.N k ^ ε ∧
          |eval (shiftedPoint D k (parentL f) p.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤
            D.N k ^ ε / D.N k ^ (-(f.depth h) - v)) ∧
        D.N k ^ (-ε) ≤ |eval (shiftedPoint D k (parentL f) p.1 p.2) (pderiv (3 : Fin 4) G)|} := by
      intro p hp
      obtain ⟨⟨hp1, hp2, hpfit, hpder⟩, hpcore⟩ := hp
      change p.1 ∈ (f.level h).B i at hp1
      have hlP : p.1 ∈ f.parentSet := (hg.inside hh i).2 hp1
      obtain ⟨hB', hI'⟩ := witness_original hg hh i p hp1 hp2
      refine ⟨hB', hI', fun t ht => ?_, ?_⟩
      · obtain ⟨hτ, hτu⟩ := time_of_original hg hh i ht
        obtain ⟨f1, f2, f3⟩ := hpfit _ hτ
        have hev : (fun j => eval (shiftedPoint D k (parentL f) p.1 t) (chartSubst f j)) =
            point (f.coeff p.1) ((t - f.t₀) / f.q₀) := eval_chartSubst f p.1 t
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [shifted_hidden f hN, abs_mul, abs_of_pos ha]
          have hb := f.parent_residual_bound hN p.1 hlP _ hτu
          calc
            f.a₀ * |point (f.coeff p.1) ((t - f.t₀) / f.q₀) 3| ≤ f.a₀ * f.H :=
              mul_le_mul_of_nonneg_left hb ha.le
            _ ≤ 1 := by linarith
        · rw [hG, eval_shiftedChartPullback, hev, abs_mul, abs_of_pos ha]
          have e1 : f.a₀ * D.N k ^ (-s' - v) ≤ D.N k ^ (-(f.depth h) - v) := by
            rw [Frame.a₀, hg.depth_zero, ← Real.rpow_add hN]
            apply Real.rpow_le_rpow_of_exponent_le hN1
            linarith
          calc
            f.a₀ * |eval (point (f.coeff p.1) ((t - f.t₀) / f.q₀)) Q| ≤
                f.a₀ * (D.N k ^ ε' * D.N k ^ (-s' - v)) := mul_le_mul_of_nonneg_left f1 ha.le
            _ = D.N k ^ ε' * (f.a₀ * D.N k ^ (-s' - v)) := by ring
            _ ≤ D.N k ^ ε * D.N k ^ (-(f.depth h) - v) :=
              mul_le_mul (Real.rpow_le_rpow_of_exponent_le hN1 hεε) e1 (by positivity)
                (by positivity)
        · rw [hG, eval_pderiv_shiftedChartPullback _ ha.ne' hσd, hev]
          exact f2.trans (Real.rpow_le_rpow_of_exponent_le hN1 hεε)
        · rw [hG, eval_second_pderiv_shiftedChartPullback _ ha.ne' hσd, hev, abs_mul,
            abs_of_pos (inv_pos.mpr ha)]
          have hpos : 0 < D.N k ^ (-s' - v) := Real.rpow_pos_of_pos hN _
          have hpos' : 0 < D.N k ^ (-(f.depth h) - v) := Real.rpow_pos_of_pos hN _
          calc
            f.a₀⁻¹ * |eval (point (f.coeff p.1) ((t - f.t₀) / f.q₀)) (pderiv 3 (pderiv 3 Q))| ≤
                f.a₀⁻¹ * (D.N k ^ ε' / D.N k ^ (-s' - v)) :=
              mul_le_mul_of_nonneg_left f3 (inv_pos.mpr ha).le
            _ = D.N k ^ (ε' + s₀ + s' + v) := by
              rw [Frame.a₀, hg.depth_zero, ← Real.rpow_neg hN.le, div_eq_mul_inv,
                ← Real.rpow_neg hN.le, ← Real.rpow_add hN, ← Real.rpow_add hN]
              congr 1; ring
            _ ≤ D.N k ^ (ε + f.depth h + v) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
            _ = D.N k ^ ε / D.N k ^ (-(f.depth h) - v) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg hN.le, ← Real.rpow_add hN]
              congr 1; ring
      · rw [hG, eval_pderiv_shiftedChartPullback _ ha.ne' hσd, eval_chartSubst f p.1 p.2]
        exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hpder
    have hX : MeasurableSet (f.hist h (f.node h i).1 (f.node h i).2) :=
      hg.measurableSet_hist hh _ _
    have hXP := (hg.inside hh i).2
    calc
      ENNReal.ofReal (D.N k ^ (-D.d * v - ε) / (2 : ℝ) ^ D.T k (f.depth h)) *
          D.ν k (D.A k (f.depth h) (f.node h i).1) ≤
          ENNReal.ofReal (D.N k ^ (-D.d * v - ε') / (2 : ℝ) ^ f.Tl h) *
            D.ν k (f.hist h (f.node h i).1 (f.node h i).2) :=
        reference_of_history hg hh i (by positivity) hθK
      _ = f.scale * (ENNReal.ofReal (D.N k ^ (-D.d * v - ε') / (2 : ℝ) ^ (f.level h).T) *
            cond (D.ν k) f.parentSet ((f.level h).A i)) :=
        (scale_mul_reference hg hh hX hXP (by positivity)).symm
      _ ≤ f.scale * f.resρ E' := mul_le_mul_right hcand _
      _ = D.ρ k (f.toChart ⁻¹' E' ∩ f.core) := scale_mul_resρ hg E'
      _ ≤ _ := measure_mono hsub

/-- Pull back a residual velocity candidate. The major velocity is unchanged
by the chart; the strip pulls back with `z₀ = q₀ * z 0 - Z₀`,
`z₁ = t₀ + q₀ * z 1`. -/
theorem velocity_pullback (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) {s' v ε ε' R R' : ℝ} (z : Fin 2 → ℝ)
    (hz : ∀ e, |z e| ≤ D.N k ^ R') (hzR : D.N k ^ R' + 2 * D.K k ≤ D.N k ^ R)
    (hgrid : f.depth h ≤ s₀ + s') (hKε : D.K k * D.N k ^ ε' ≤ D.N k ^ ε)
    (hθK : D.N k ^ (-ε) * D.K k ≤ D.N k ^ (-ε') * θ)
    (hcand : ENNReal.ofReal (D.N k ^ (-ε') / (2 : ℝ) ^ (f.level h).T) *
        cond (D.ν k) f.parentSet ((f.level h).A i) ≤
      f.resρ {p | p.1 ∈ (f.level h).B i ∧ p.2 ∈ Data.I (f.level h).T ((f.level h).j i) ∧
        |f.coeff p.1 4 - z 0 - z 1 * f.coeff p.1 3| ≤ D.N k ^ ε' * D.N k ^ (-D.κ * s' - v)}) :
    ShiftedVelocity D k R ε (f.depth h) v (f.node h i).1 := by
  have hN2 : 2 ≤ D.N k := hg.N_ge
  have hN : 0 < D.N k := lt_of_lt_of_le two_pos hN2
  have hN1 : 1 ≤ D.N k := le_trans one_le_two hN2
  have hq := f.q₀_pos
  have hK : 1 ≤ D.K k := hg.K_ge
  -- parent constants
  have hq1 : f.q₀ ≤ 1 := by
    unfold Frame.q₀; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have ht₀ : |f.t₀| ≤ 1 := by
    have hb := f.parent_block
    have h0 : f.t₀ ∈ f.block 0 f.i₀ := by
      rw [hb]; exact ⟨le_rfl, by linarith⟩
    have : f.block 0 f.i₀ ⊆ Icc (0 : ℝ) 1 := by
      intro t ht
      simp only [Frame.block, Data.I, mem_Icc] at ht
      have hj : (((D.j k (f.depth 0) f.i₀ : ℕ) : ℝ) + 1) ≤ (2 : ℝ) ^ f.Tl 0 := by
        exact_mod_cast (D.j k (f.depth 0) f.i₀).isLt
      have h2 : (0 : ℝ) < 2 ^ f.Tl 0 := by positivity
      constructor
      · exact le_trans (by positivity) ht.1
      · exact ht.2.trans ((div_le_one h2).mpr hj)
    have := this h0
    rw [abs_of_nonneg this.1]; exact this.2
  have hZ₀ : |f.Z₀| ≤ 2 * D.K k := by
    have hc0 := hg.cbound 0 (Nat.zero_le _) f.i₀ 0
    have hc1 := hg.cbound 0 (Nat.zero_le _) f.i₀ 1
    unfold Frame.Z₀
    calc
      _ ≤ |D.c k (f.depth 0) f.i₀ 0| + |f.t₀| * |D.c k (f.depth 0) f.i₀ 1| := by
        rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ D.K k + 1 * D.K k := add_le_add hc0 (mul_le_mul ht₀ hc1 (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  set zo : Fin 2 → ℝ := ![f.q₀ * z 0 - f.Z₀, f.t₀ + f.q₀ * z 1] with hzo
  refine ⟨zo, ?_, ?_⟩
  · intro e
    have hz0 := hz 0
    have hz1 := hz 1
    have hpow : 0 ≤ D.N k ^ R' := by positivity
    fin_cases e
    · change |f.q₀ * z 0 - f.Z₀| ≤ _
      calc
        _ ≤ |f.q₀ * z 0| + |f.Z₀| := abs_sub _ _
        _ ≤ 1 * D.N k ^ R' + 2 * D.K k := by
          rw [abs_mul, abs_of_pos hq]
          exact add_le_add (mul_le_mul hq1 hz0 (abs_nonneg _) zero_le_one) hZ₀
        _ ≤ _ := by linarith
    · change |f.t₀ + f.q₀ * z 1| ≤ _
      calc
        _ ≤ |f.t₀| + |f.q₀ * z 1| := abs_add_le _ _
        _ ≤ 1 + 1 * D.N k ^ R' := by
          rw [abs_mul, abs_of_pos hq]
          exact add_le_add ht₀ (mul_le_mul hq1 hz1 (abs_nonneg _) zero_le_one)
        _ ≤ _ := by linarith
  · set E' := {p : α × ℝ | p.1 ∈ (f.level h).B i ∧
        p.2 ∈ Data.I (f.level h).T ((f.level h).j i) ∧
        |f.coeff p.1 4 - z 0 - z 1 * f.coeff p.1 3| ≤
          D.N k ^ ε' * D.N k ^ (-D.κ * s' - v)} with hE'
    have hqK : f.q₀ ≤ D.K k * D.N k ^ (-D.κ * s₀) := by
      have h1 := hg.q₀_le_K.1
      have hA : 0 < D.N k ^ (D.κ * s₀) := Real.rpow_pos_of_pos hN _
      rw [div_le_iff₀ (by linarith), ← div_le_iff₀' (by positivity)] at h1
      rw [show -D.κ * s₀ = -(D.κ * s₀) by ring, Real.rpow_neg hN.le]
      calc
        f.q₀ = 1 / f.q₀⁻¹ := by field_simp
        _ ≤ 1 / (D.N k ^ (D.κ * s₀) / D.K k) := by
          apply one_div_le_one_div_of_le (by positivity)
          rw [div_le_iff₀ (by linarith)]
          rw [div_le_iff₀ (by positivity)] at h1
          linarith
        _ = _ := by field_simp
    have hsub : f.toChart ⁻¹' E' ∩ f.core ⊆ {p | p.1 ∈ D.B k (f.depth h) (f.node h i).1 ∧
        p.2 ∈ Data.I (D.T k (f.depth h)) (D.j k (f.depth h) (f.node h i).1) ∧
        |D.b k p.1 4 - zo 0 - zo 1 * D.b k p.1 3| ≤
          D.N k ^ ε * D.N k ^ (-D.ℓ * (f.depth h) - v)} := by
      intro p hp
      obtain ⟨⟨hp1, hp2, hpz⟩, -⟩ := hp
      change p.1 ∈ (f.level h).B i at hp1
      obtain ⟨hB', hI'⟩ := witness_original hg hh i p hp1 hp2
      refine ⟨hB', hI', ?_⟩
      have hid := contactChart_strip_identity f.t₀ f.q₀ f.Z₀ f.Y₀ hq.ne' (D.b k p.1) z
      have h3 : f.coeff p.1 3 = contactChartCoeff f.t₀ f.q₀ f.Z₀ f.Y₀ (D.b k p.1) 3 := rfl
      have h4 : f.coeff p.1 4 = contactChartCoeff f.t₀ f.q₀ f.Z₀ f.Y₀ (D.b k p.1) 4 := rfl
      change |D.b k p.1 4 - (f.q₀ * z 0 - f.Z₀) - (f.t₀ + f.q₀ * z 1) * D.b k p.1 3| ≤ _
      rw [hid, ← h3, ← h4, abs_mul, abs_of_pos hq, hg.ℓ_eq]
      have hexp : D.N k ^ (-D.κ * s₀) * D.N k ^ (-D.κ * s' - v) ≤
          D.N k ^ (-D.κ * f.depth h - v) := by
        rw [← Real.rpow_add hN]
        apply Real.rpow_le_rpow_of_exponent_le hN1
        nlinarith [hg.κ_pos]
      calc
        f.q₀ * |f.coeff p.1 4 - z 0 - z 1 * f.coeff p.1 3| ≤
            (D.K k * D.N k ^ (-D.κ * s₀)) * (D.N k ^ ε' * D.N k ^ (-D.κ * s' - v)) :=
          mul_le_mul hqK hpz (abs_nonneg _) (by positivity)
        _ = (D.K k * D.N k ^ ε') * (D.N k ^ (-D.κ * s₀) * D.N k ^ (-D.κ * s' - v)) := by ring
        _ ≤ D.N k ^ ε * D.N k ^ (-D.κ * f.depth h - v) :=
          mul_le_mul hKε hexp (by positivity) (by positivity)
    have hX : MeasurableSet (f.hist h (f.node h i).1 (f.node h i).2) :=
      hg.measurableSet_hist hh _ _
    have hXP := (hg.inside hh i).2
    calc
      ENNReal.ofReal (D.N k ^ (-ε) / (2 : ℝ) ^ D.T k (f.depth h)) *
          D.ν k (D.A k (f.depth h) (f.node h i).1) ≤
          ENNReal.ofReal (D.N k ^ (-ε') / (2 : ℝ) ^ f.Tl h) *
            D.ν k (f.hist h (f.node h i).1 (f.node h i).2) :=
        reference_of_history hg hh i (by positivity) hθK
      _ = f.scale * (ENNReal.ofReal (D.N k ^ (-ε') / (2 : ℝ) ^ (f.level h).T) *
            cond (D.ν k) f.parentSet ((f.level h).A i)) :=
        (scale_mul_reference hg hh hX hXP (by positivity)).symm
      _ ≤ f.scale * f.resρ E' := mul_le_mul_right hcand _
      _ = D.ρ k (f.toChart ⁻¹' E' ∩ f.core) := scale_mul_resρ hg E'
      _ ≤ _ := measure_mono hsub

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted
