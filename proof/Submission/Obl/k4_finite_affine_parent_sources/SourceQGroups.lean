-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceGroups
import Submission.Obl.k4_finite_affine_parent_sources.SourcePureCaps
import Submission.Obl.k4_finite_affine_parent_sources.ModelEH1
import Submission.Obl.k4_finite_affine_parent_sources.Original

/-!
# Native points of a label in its own frame

`framePoint Φ x` is the native point `(τ, z, W)` of an original incidence in the normalisation of
a frame `Φ` (time, planar position, hidden coordinate rescaled by `Φ.sc`). For a label whose
frame keeps the PARENT's hidden scale (`Φ.sc = B / δp`), the label's own test `RQ` (thickness
`δQ`) pushed by `δp` and the parent's test `R0` pushed by `δp` satisfy the hypotheses of the
accepted oscillation partition at thickness `δQ / δp`, at every counted incidence of the label in
the parent tube: `framePoint_good`.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable section

/-- The native point of an original incidence in the normalisation of a frame. -/
def framePoint (Φ : PFrame) (x : Incidence) : NativePoint :=
  pointS Φ.eb (tnorm Φ.F.t₀ Φ.F.q x)

theorem measurable_framePoint (Φ : PFrame) : Measurable (framePoint Φ) :=
  (measurable_pointS Φ.measurable_eb).comp (measurable_tnorm _ _)

theorem framePoint_apply (Φ : PFrame) (x : Incidence) (i : Fin 4) :
    framePoint Φ x i = exS Φ.eb x.1 ((x.2 - Φ.F.t₀) / Φ.F.q) i := rfl

theorem value_framePoint (Φ : PFrame) (P : MvPolynomial (Fin 4) ℝ) (x : Incidence) :
    value P (framePoint Φ x) = eval (exS Φ.eb x.1 ((x.2 - Φ.F.t₀) / Φ.F.q)) P := rfl

theorem value_normTest_framePoint (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    (hsc : Φ.sc ≠ 0) (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) (x : Incidence) :
    value (Φ.normTest δ R) (framePoint Φ x) = δ⁻¹ * eval (gx x.1 x.2) R := by
  rw [value_framePoint, Φ.eval_normTest hq.ne' hD hsc δ R x.1 x.2]

theorem value_pderiv_normTest_framePoint (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    (hsc : Φ.sc ≠ 0) (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) (x : Incidence) :
    value (pderiv (3 : Fin 4) (Φ.normTest δ R)) (framePoint Φ x) =
      Φ.sc⁻¹ * (δ⁻¹ * eval (gx x.1 x.2) (pderiv (3 : Fin 4) R)) := by
  rw [value_framePoint, Φ.pderiv_normTest, smul_eval, Φ.eval_normTest hq.ne' hD hsc]

theorem curvature_normTest (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    (hsc : Φ.sc ≠ 0) (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (x : Incidence) :
    curvature (Φ.normTest δ R) 3 =
      Φ.sc⁻¹ * Φ.sc⁻¹ * (δ⁻¹ * eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R))) := by
  have hdeg : (Φ.normTest δ R).totalDegree ≤ 2 := (Φ.totalDegree_normTest_le δ R).trans hR
  have h := second_pderiv_eq_curvature (Φ.normTest δ R) hdeg 3
  have h2 := congrArg (eval (exS Φ.eb x.1 ((x.2 - Φ.F.t₀) / Φ.F.q))) h
  rw [eval_C] at h2
  rw [← h2, Φ.pderiv_normTest, Derivation.map_smul, Φ.pderiv_normTest, smul_smul, smul_eval,
    Φ.eval_normTest hq.ne' hD hsc]

theorem norm_three_le (a b c : ℝ) :
    ‖(WithLp.toLp 2 ![a, b, c] : EuclideanSpace ℝ (Fin 3))‖ ≤ |a| + |b| + |c| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left]
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
    nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, sq_abs a, sq_abs b, sq_abs c,
      mul_nonneg (abs_nonneg a) (abs_nonneg b), mul_nonneg (abs_nonneg a) (abs_nonneg c),
      mul_nonneg (abs_nonneg b) (abs_nonneg c)]
  · positivity

/-- **Native hypotheses of a label in its own frame.** -/
theorem framePoint_good (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    {B δp δQ κ : ℝ} (hB : 0 < B) (hδp : 0 < δp) (hδQ : 0 < δQ) (hsc : Φ.sc = B / δp)
    (hκ : 1 ≤ κ) (RQ R0 : MvPolynomial (Fin 4) ℝ) (hRQ : RQ.totalDegree ≤ 2)
    (hR0 : R0.totalDegree ≤ 2) (x : Incidence)
    (hτ : (x.2 - Φ.F.t₀) / Φ.F.q ∈ Icc (0 : ℝ) 1)
    (hpos : ‖Matrix.toEuclideanLin Φ.F.D⁻¹ (gy x.1 x.2 - Φ.F.c - x.2 • Φ.F.u)‖ ≤ 3 * κ)
    (hQ1 : |eval (gx x.1 x.2) RQ| ≤ κ * δQ)
    (hQ2 : B / κ ≤ |eval (gx x.1 x.2) (pderiv (3 : Fin 4) RQ)|)
    (hQ2' : |eval (gx x.1 x.2) (pderiv (3 : Fin 4) RQ)| ≤ κ * B)
    (hQ3 : |eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) RQ))| ≤ κ * B ^ 2 / δQ)
    (h01 : |eval (gx x.1 x.2) R0| ≤ κ * δp)
    (h02 : |eval (gx x.1 x.2) (pderiv (3 : Fin 4) R0)| ≤ κ * B)
    (h03 : |eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R0))| ≤ κ * B ^ 2 / δp) :
    framePoint Φ x ∈ goodSet (7 * κ) (δQ / δp) (Φ.normTest δp RQ) (Φ.normTest δp R0) := by
  have hsc0 : Φ.sc ≠ 0 := by rw [hsc]; positivity
  have hscinv : Φ.sc⁻¹ = δp / B := by rw [hsc, inv_div]
  have hκ0 : 0 < κ := by linarith
  have hB0 := hB.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the base
    have hbase : nativeBase (framePoint Φ x) = WithLp.toLp 2
        ![(x.2 - Φ.F.t₀) / Φ.F.q,
          Φ.eb x.1 0 + (x.2 - Φ.F.t₀) / Φ.F.q * Φ.eb x.1 3,
          Φ.eb x.1 1 + (x.2 - Φ.F.t₀) / Φ.F.q * Φ.eb x.1 4] := by
      simp only [nativeBase, framePoint_apply, exS]
      rfl
    rw [hbase]
    have hoff := Φ.toEuclideanLin_offset hq.ne' x.1 x.2
    rw [hoff] at hpos
    have hz1 := (PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb x.1 0 + (x.2 - Φ.F.t₀) / Φ.F.q * Φ.eb x.1 3,
        Φ.eb x.1 1 + (x.2 - Φ.F.t₀) / Φ.F.q * Φ.eb x.1 4]) 0).trans hpos
    have hz2 := (PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb x.1 0 + (x.2 - Φ.F.t₀) / Φ.F.q * Φ.eb x.1 3,
        Φ.eb x.1 1 + (x.2 - Φ.F.t₀) / Φ.F.q * Φ.eb x.1 4]) 1).trans hpos
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Real.norm_eq_abs] at hz1 hz2
    have hτ1 : |(x.2 - Φ.F.t₀) / Φ.F.q| ≤ 1 := by
      rw [abs_of_nonneg hτ.1]; exact hτ.2
    exact (norm_three_le _ _ _).trans (by linarith)
  · -- the value of the label test
    rw [value_normTest_framePoint Φ hq hD hsc0, abs_mul, abs_inv, abs_of_pos hδp]
    rw [inv_mul_le_iff₀ hδp]
    calc |eval (gx x.1 x.2) RQ| ≤ κ * δQ := hQ1
      _ ≤ δp * (7 * κ * (δQ / δp)) := by
          field_simp
          nlinarith
  · -- lower derivative
    rw [value_pderiv_normTest_framePoint Φ hq hD hsc0, hscinv]
    have heq : δp / B * (δp⁻¹ * eval (gx x.1 x.2) (pderiv (3 : Fin 4) RQ)) =
        eval (gx x.1 x.2) (pderiv (3 : Fin 4) RQ) / B := by
      field_simp
    rw [heq, abs_div, abs_of_pos hB, le_div_iff₀ hB]
    calc (7 * κ)⁻¹ * B ≤ B / κ := by
          rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) hκ0]
          nlinarith
      _ ≤ _ := hQ2
  · -- upper derivative
    rw [value_pderiv_normTest_framePoint Φ hq hD hsc0, hscinv]
    have heq : δp / B * (δp⁻¹ * eval (gx x.1 x.2) (pderiv (3 : Fin 4) RQ)) =
        eval (gx x.1 x.2) (pderiv (3 : Fin 4) RQ) / B := by
      field_simp
    rw [heq, abs_div, abs_of_pos hB, div_le_iff₀ hB]
    nlinarith
  · -- curvature of the label test
    rw [curvature_normTest Φ hq hD hsc0 δp RQ hRQ x, hscinv]
    have heq : δp / B * (δp / B) * (δp⁻¹ *
        eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) RQ))) =
        δp / B ^ 2 * eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) RQ)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    calc δp / B ^ 2 * |eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) RQ))|
        ≤ δp / B ^ 2 * (κ * B ^ 2 / δQ) := by gcongr
      _ = κ / (δQ / δp) := by field_simp
      _ ≤ 7 * κ / (δQ / δp) := by
          apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  · -- the value of the parent test
    rw [value_normTest_framePoint Φ hq hD hsc0, abs_mul, abs_inv, abs_of_pos hδp,
      inv_mul_le_iff₀ hδp]
    nlinarith
  · -- its derivative
    rw [value_pderiv_normTest_framePoint Φ hq hD hsc0, hscinv]
    have heq : δp / B * (δp⁻¹ * eval (gx x.1 x.2) (pderiv (3 : Fin 4) R0)) =
        eval (gx x.1 x.2) (pderiv (3 : Fin 4) R0) / B := by
      field_simp
    rw [heq, abs_div, abs_of_pos hB, div_le_iff₀ hB]
    nlinarith
  · -- its curvature
    rw [curvature_normTest Φ hq hD hsc0 δp R0 hR0 x, hscinv]
    have heq : δp / B * (δp / B) * (δp⁻¹ *
        eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R0))) =
        δp / B ^ 2 * eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R0)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    calc δp / B ^ 2 * |eval (gx x.1 x.2) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R0))|
        ≤ δp / B ^ 2 * (κ * B ^ 2 / δp) := by gcongr
      _ = κ := by field_simp
      _ ≤ 7 * κ := by linarith

theorem nativeBase_pointS_eq {α : Type} (b : α → Fin 6 → ℝ) (y : α × ℝ) :
    nativeBase (pointS b y) = (signalObservation (fun p : α × ℝ => exS b p.1 p.2) 1 y).1 := by
  ext e
  fin_cases e <;> rfl

/-- **Base density of a law in a frame**, from its raw ceiling and a regular test. -/
theorem base_density_of_ceiling {α : Type} [MeasurableSpace α] (μ : Measure (α × ℝ))
    {b : α → Fin 6 → ℝ} (hb : Measurable b) {a κ : ℝ} (ha : 0 < a) (hκ : 0 < κ)
    (D : ENNReal) (hcap : μ.map (obsS b a) ≤ D • (volume.prod Measure.count))
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (htest : ∀ᵐ y ∂μ, |eval (exS b y.1 y.2) P| ≤ κ * a ∧
      κ⁻¹ ≤ |eval (exS b y.1 y.2) (pderiv (3 : Fin 4) P)|) :
    μ.map (nativeBase ∘ pointS b) ≤
      (D * ENNReal.ofReal (16 * (1 + κ ^ 2))) • volume := by
  have hpt := measurable_exS hb
  have hsig := signalObservation_exS b a
  have hcap' : μ.map (signalObservation (fun p : α × ℝ => exS b p.1 p.2) a) ≤
      D • (volume.prod Measure.count) := by rw [hsig]; exact hcap
  have hnb : Measurable (nativeBase ∘ pointS b) :=
    measurable_nativeBase.comp (measurable_pointS hb)
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.map_apply hnb hA, Measure.smul_apply, smul_eq_mul]
  have hE : MeasurableSet ((nativeBase ∘ pointS b) ⁻¹' A) := hnb hA
  have h := quadratic_signal_cap μ (fun p : α × ℝ => exS b p.1 p.2) hpt P hP A hA
    ((nativeBase ∘ pointS b) ⁻¹' A) hE a κ D ha hκ hcap' ?_ ?_
  · calc μ ((nativeBase ∘ pointS b) ⁻¹' A)
        ≤ D * (volume A * ENNReal.ofReal (16 * (1 + κ ^ 2))) := h
      _ = D * ENNReal.ofReal (16 * (1 + κ ^ 2)) * volume A := by ring
  · intro y hy
    have : nativeBase (pointS b y) =
        (signalObservation (fun p : α × ℝ => exS b p.1 p.2) a y).1 := by
      ext e
      fin_cases e <;> rfl
    rw [← this]
    exact hy
  · filter_upwards [htest] with y hy _
    exact hy

/-- **Groups of a law in a frame.** The raw ceiling at the test thickness (test constant `κt`)
and a floor of the law give the base density hypothesis of the accepted partition. -/
theorem frame_groups (A : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {α : Type} [MeasurableSpace α] (μ : Measure (α × ℝ))
      [IsFiniteMeasure μ], μ univ ≠ 0 →
      ∀ {b : α → Fin 6 → ℝ}, Measurable b →
      ∀ (K κt a : ℝ) (P S : MvPolynomial (Fin 4) ℝ),
      2 ≤ K → 0 < κt → 0 < a → a ≤ 1 → P.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      ∀ D : ENNReal, μ.map (obsS b a) ≤ D • (volume.prod Measure.count) →
      D * ENNReal.ofReal (16 * (1 + κt ^ 2)) ≤ ENNReal.ofReal K * μ univ →
      (∀ᵐ y ∂μ, |eval (exS b y.1 y.2) P| ≤ κt * a ∧
        κt⁻¹ ≤ |eval (exS b y.1 y.2) (pderiv (3 : Fin 4) P)|) →
      (∀ᵐ y ∂μ, pointS b y ∈ goodSet K a P S) →
      ∃ (n : ℕ) (E : Fin n → Set (α × ℝ)), (n : ℝ) ≤ K ^ C ∧
        (∀ i, MeasurableSet (E i)) ∧
        (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) * μ univ ∧
        ∀ i y, y ∈ E i → ∀ y', y' ∈ E i →
          |value S (pointS b y) - value S (pointS b y')| ≤
            K ^ C * (a + ‖nativeBase (pointS b y) - nativeBase (pointS b y')‖) := by
  obtain ⟨C, hC, hgroups⟩ := finite_native_groups A
  refine ⟨C, hC, ?_⟩
  intro α _ μ _ hμ b hb K κt a P S hK hκt ha ha1 hP hS D hcap hD htest hgood
  have hdens := base_density_of_ceiling μ hb ha hκt D hcap P hP htest
  have hbase : μ.map (nativeBase ∘ pointS b) ≤ (ENNReal.ofReal K * μ univ) • volume := by
    refine hdens.trans (Measure.le_iff'.mpr fun U => ?_)
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_left hD _
  exact hgroups μ hμ (pointS b) (measurable_pointS hb) K a P S hK ha ha1 hP hS hbase hgood

theorem goodSet_mono {K K' a : ℝ} (hK : 0 < K) (hKK' : K ≤ K') (ha : 0 < a)
    {P S : MvPolynomial (Fin 4) ℝ} {p : NativePoint} (h : p ∈ goodSet K a P S) :
    p ∈ goodSet K' a P S := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hK' : 0 < K' := lt_of_lt_of_le hK hKK'
  refine ⟨h1.trans hKK', h2.trans (by gcongr), ?_, h4.trans hKK', h5.trans (by gcongr),
    h6.trans hKK', h7.trans hKK', h8.trans hKK'⟩
  exact (inv_anti₀ hK hKK').trans h3

/-- The uniform conclusion of `frame_groups` for one exponent pair. -/
def GroupsProp (A C : ℕ) : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (μ : Measure (α × ℝ))
      [IsFiniteMeasure μ], μ univ ≠ 0 →
      ∀ {b : α → Fin 6 → ℝ}, Measurable b →
      ∀ (K κt a : ℝ) (P S : MvPolynomial (Fin 4) ℝ),
      2 ≤ K → 0 < κt → 0 < a → a ≤ 1 → P.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      ∀ D : ENNReal, μ.map (obsS b a) ≤ D • (volume.prod Measure.count) →
      D * ENNReal.ofReal (16 * (1 + κt ^ 2)) ≤ ENNReal.ofReal K * μ univ →
      (∀ᵐ y ∂μ, |eval (exS b y.1 y.2) P| ≤ κt * a ∧
        κt⁻¹ ≤ |eval (exS b y.1 y.2) (pderiv (3 : Fin 4) P)|) →
      (∀ᵐ y ∂μ, pointS b y ∈ goodSet K a P S) →
      ∃ (n : ℕ) (E : Fin n → Set (α × ℝ)), (n : ℝ) ≤ K ^ C ∧
        (∀ i, MeasurableSet (E i)) ∧
        (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) * μ univ ∧
        ∀ i y, y ∈ E i → ∀ y', y' ∈ E i →
          |value S (pointS b y) - value S (pointS b y')| ≤
            K ^ C * (a + ‖nativeBase (pointS b y) - nativeBase (pointS b y')‖)

theorem exists_groupsProp (A : ℕ) : ∃ C : ℕ, 1 ≤ C ∧ GroupsProp A C := frame_groups A

end

end Submission.Obl.k4_finite_affine_parent_sources
