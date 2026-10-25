import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Interface
import Submission.Obl.k4_general_parent_wide_layer_candidates.CalibratedReturn
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
# Applying Scalar to a ready native frame

Scalar's angular conclusion gives one full-width quadratic in normalized
`(u, y)`; composing it with the frame normalization and adding the background
gives a quadratic in the original base `(t, Z, Y)` predicting the native signal
throughout the original true block. Its mass is measured in the original
residual `ρ` through the frame's original domination.
-/

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

theorem eval_bind₁_real {σ τ : Type*} (x : τ → ℝ) (h : σ → MvPolynomial τ ℝ)
    (φ : MvPolynomial σ ℝ) :
    eval x (bind₁ h φ) = eval (fun i => eval x (h i)) φ :=
  eval₂Hom_bind₁ (RingHom.id ℝ) x h φ

/-- The affine normalization `(t, Z, Y) ↦ ((t - t₀)/q, (Z - z₀ - zv t)/q)`. -/
def frameMap (t₀ q z₀ zv : ℝ) : Fin 2 → MvPolynomial (Fin 3) ℝ :=
  ![C q⁻¹ * (X 0 - C t₀), C q⁻¹ * (X 1 - C z₀ - C zv * X 0)]

theorem frameMap_degree (t₀ q z₀ zv : ℝ) (i : Fin 2) :
    (frameMap t₀ q z₀ zv i).totalDegree ≤ 1 := by
  fin_cases i
  · simp only [frameMap, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_X, totalDegree_C]
    norm_num
  · simp only [frameMap, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_sub _ _).trans ?_
    refine max_le ((totalDegree_sub _ _).trans ?_) ?_
    · rw [totalDegree_X, totalDegree_C]
      norm_num
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, totalDegree_X]

theorem eval_frameMap (t₀ q z₀ zv : ℝ) (x : Fin 3 → ℝ) :
    (fun i => eval x (frameMap t₀ q z₀ zv i)) =
      ![(x 0 - t₀) / q, (x 1 - z₀ - zv * x 0) / q] := by
  funext i
  fin_cases i
  · simp [frameMap, div_eq_inv_mul]
  · simp [frameMap, div_eq_inv_mul]

/-- The restored full-base predictor. -/
def restoredPredictor (background : MvPolynomial (Fin 3) ℝ) (t₀ q z₀ zv : ℝ)
    (F : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  background + bind₁ (frameMap t₀ q z₀ zv) F

theorem restoredPredictor_degree {background : MvPolynomial (Fin 3) ℝ}
    (hb : background.totalDegree ≤ 2) (t₀ q z₀ zv : ℝ) {F : MvPolynomial (Fin 2) ℝ}
    (hF : F.totalDegree ≤ 2) :
    (restoredPredictor background t₀ q z₀ zv F).totalDegree ≤ 2 := by
  refine (totalDegree_add _ _).trans (max_le hb ?_)
  exact (Submission.Lib.K4ChartLifting.totalDegree_bind₁_le_of_le_one _
    (frameMap_degree t₀ q z₀ zv) F).trans hF

theorem eval_restoredPredictor (background : MvPolynomial (Fin 3) ℝ) (t₀ q z₀ zv : ℝ)
    (F : MvPolynomial (Fin 2) ℝ) (x : Fin 3 → ℝ) :
    eval x (restoredPredictor background t₀ q z₀ zv F) =
      eval x background + eval ![(x 0 - t₀) / q, (x 1 - z₀ - zv * x 0) / q] F := by
  rw [restoredPredictor, map_add, eval_bind₁_real, eval_frameMap]

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem base_zero (k : ℕ) (l : α) (t : ℝ) : p.base k l t 0 = t := rfl

theorem base_one (k : ℕ) (l : α) (t : ℝ) : p.base k l t 1 = p.x k l t 1 := rfl

namespace ReadyFrame

variable {p} {k : ℕ} {r v m C₀ S₀ U₀ height η : ℝ}
  (f : p.ReadyFrame k r v m C₀ S₀ U₀ height η)

/-- A whole-time scalar fit of a good trajectory is a full-block native
prediction by the restored base polynomial. -/
theorem predicts_of_scalarFit {F : MvPolynomial (Fin 2) ℝ} {error : ℝ}
    {l : α} (hl : l ∈ f.good)
    (hfit : f.coeff l ∈ Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarFit F error)
    {t : ℝ} (ht : t ∈ block (p.T k r) (p.j k r f.parent)) :
    |eval (p.x k l t) (p.P k) -
      eval (p.x k l t ∘ Fin.castSucc) (restoredPredictor f.background f.t₀ f.q f.z₀ f.zv F)| ≤
      error := by
  have hq := f.q_pos
  rw [f.time_eq] at ht
  set u := (t - f.t₀) / f.q with hu
  have htu : f.t₀ + f.q * u = t := by
    rw [hu]
    field_simp
    ring
  have hu0 : 0 ≤ u := div_nonneg (by linarith [ht.1]) hq.le
  have hu1 : u ≤ 1 := (div_le_one hq).mpr (by linarith [ht.2])
  have h := hfit u ⟨hu0, hu1⟩
  have hX : Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarX (f.coeff l) u =
      p.signal k l (f.t₀ + f.q * u) -
        MvPolynomial.eval (p.base k l (f.t₀ + f.q * u)) f.background := f.scalarX_eq l hl u
  have hY : Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarY (f.coeff l) u =
      (p.x k l (f.t₀ + f.q * u) 1 - f.z₀ - f.zv * (f.t₀ + f.q * u)) / f.q :=
    f.scalarY_eq l hl u
  rw [hX, hY, htu] at h
  rw [eval_restoredPredictor]
  have hb0 : (p.x k l t ∘ Fin.castSucc) 0 = t := rfl
  have hb1 : (p.x k l t ∘ Fin.castSucc) 1 = p.x k l t 1 := rfl
  rw [hb0, hb1, ← hu]
  have heq : eval (p.x k l t) (p.P k) - (eval (p.x k l t ∘ Fin.castSucc) f.background +
      eval ![u, (p.x k l t 1 - f.z₀ - f.zv * t) / f.q] F) =
      p.signal k l t - eval (p.base k l t) f.background -
        eval ![u, (p.x k l t 1 - f.z₀ - f.zv * t) / f.q] F := by
    simp only [signal, base]
    ring
  rw [heq]
  exact h

end ReadyFrame

/-- **Scalar application.** Readiness at fixed depth, gain and Scalar
parameters gives the native full-base predictors of the frozen return. -/
theorem nativePredictors_of_readiness
    (hscalar : Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarMeshProjection)
    (h : p.Valid) {r v m C₀ S₀ U₀ height : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hrvm : r + v < m)
    (hC₀ : 0 < C₀) (hS₀ : 0 < S₀) (hU₀ : 0 < U₀) (hU₀m : U₀ < m)
    (ready : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      Nonempty (p.ReadyFrame k r v m C₀ S₀ U₀ height η)) :
    p.NativePredictors r v := by
  intro ε hε
  let ε' := ε / 4
  have hε' : 0 < ε' := by dsimp [ε']; positivity
  have hrv : 0 < r + v := by linarith
  obtain ⟨η, hη, N₀, hN₀, hcand⟩ :=
    Submission.Obl.k4_fixed_budget_quadratic_recovery.scalar_candidate_of_mesh hscalar
      h.dimension_nonneg h.dimension_lt_one hrv hrvm hC₀ hS₀ hU₀ hU₀m hε'
  have hlarge : ∀ᶠ k in atTop, N₀ ≤ p.N k := h.scale_limit.eventually_ge_atTop N₀
  apply Filter.Eventually.frequently
  filter_upwards [ready η hη, hlarge] with k hk hNk
  obtain ⟨f⟩ := hk
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [h.scale k]
  obtain ⟨F, hF⟩ := hcand (p.N k) hNk α f.prior f.law f.coeff (p.N k ^ (p.d * r))
    f.admissible f.mass_lower
  let G := restoredPredictor f.background f.t₀ f.q f.z₀ f.zv F.P
  refine ⟨f.parent, G, restoredPredictor_degree f.background_degree _ _ _ _ F.degree, ?_⟩
  -- the scalar fit is contained in the pulled-back predictor event
  let τ : α × ℝ → α × ℝ := fun ω => (ω.1, f.t₀ + f.q * ω.2)
  have hτ : Measurable τ := by dsimp [τ]; fun_prop
  have hsub : F.fit f.coeff ∩ {ω | ω.1 ∈ f.good} ⊆
      τ ⁻¹' p.PredictorEvent k r v ε f.parent G := by
    rintro ω ⟨hfit, hgood⟩
    have hgood : ω.1 ∈ f.good := hgood
    have hu : ω.2 ∈ Icc (0 : ℝ) 1 := hfit.2
    have hfitω : f.coeff ω.1 ∈ Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarFit
        F.P (p.N k ^ ε' * p.N k ^ (-(r + v))) := hfit.1
    refine ⟨f.good_subset hgood, ?_, ?_⟩
    · rw [f.time_eq]
      exact ⟨by nlinarith [f.q_pos, hu.1], by nlinarith [f.q_pos, hu.2]⟩
    · intro t ht
      apply (f.predicts_of_scalarFit hgood hfitω ht).trans
      have hε'v : ε' = ε / 4 := rfl
      have hpow : p.N k ^ ε' ≤ p.N k ^ ε :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have hexp : -(r + v) = -r - v := by ring
      rw [hexp]
      exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hN.le _)
  have hgood_full : f.law (F.fit f.coeff) = f.law (F.fit f.coeff ∩ {ω | ω.1 ∈ f.good}) :=
    (measure_inter_conull f.good_ae).symm
  have hlaw : ENNReal.ofReal
      (Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCandidateFloor (p.N k)
        (p.N k ^ (p.d * r)) p.d (r + v) ε') ≤
      (f.law.map τ) (p.PredictorEvent k r v ε f.parent G) := by
    apply hF.trans
    rw [hgood_full]
    exact (measure_mono hsub).trans (Measure.le_map_apply hτ.aemeasurable _)
  -- the floor is N^(-dv-2ε') with the original time factor
  have hfloor : Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCandidateFloor (p.N k)
      (p.N k ^ (p.d * r)) p.d (r + v) ε' = p.N k ^ (-p.d * v - 2 * ε') := by
    simp only [Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCandidateFloor]
    rw [← Real.rpow_mul hN.le, div_eq_mul_inv, ← Real.rpow_neg hN.le, ← Real.rpow_add hN,
      ← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  rw [hfloor] at hlaw
  have hT : ((2 : ℝ) ^ p.T k r)⁻¹ = f.q := f.q_eq.symm
  calc
    ENNReal.ofReal (p.N k ^ (-p.d * v - ε) / (2 : ℝ) ^ p.T k r) * p.ν k (p.A k r f.parent)
        = ENNReal.ofReal f.q * p.ν k (p.A k r f.parent) *
            ENNReal.ofReal (p.N k ^ (-p.d * v - ε)) := by
          rw [div_eq_mul_inv, hT, ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)]
          ring
    _ ≤ ENNReal.ofReal f.q * p.ν k (p.A k r f.parent) *
          ENNReal.ofReal (p.N k ^ (-p.d * v - 2 * ε')) := by
          have hε'v : ε' = ε / 4 := rfl
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)))
    _ ≤ ENNReal.ofReal f.q * p.ν k (p.A k r f.parent) *
          (f.law.map τ) (p.PredictorEvent k r v ε f.parent G) := by
          gcongr
    _ = ((ENNReal.ofReal f.q * p.ν k (p.A k r f.parent)) • f.law.map τ)
          (p.PredictorEvent k r v ε f.parent G) := by
          rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ p.ρ k (p.PredictorEvent k r v ε f.parent G) := f.original_domination _

/-- Readiness supplies the frozen candidate conclusion through the calibrated
return of `CalibratedReturn`. -/
theorem candidates_of_readiness
    (hscalar : Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarMeshProjection)
    (h : p.Valid) (hready : p.ScalarReadiness) : p.Candidates := by
  obtain ⟨r, v, m, C₀, S₀, U₀, height, hr, hv, hrvU, hrvm, hC₀, hS₀, hU₀, hU₀m, _, ready⟩ :=
    hready
  exact p.candidates_of_native_predictors h hr hv hrvU
    (p.nativePredictors_of_readiness hscalar h hr hv hrvm hC₀ hS₀ hU₀ hU₀m ready)

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
