import Submission.Obl.k4_oss_unit_decay.Defs

/-!
# The Cauchy–Schwarz chain (Fourier side of `k4_oss_unit_decay`)

(x0074)

* `prodLaw k μ`: the law of `x₀ ⋯ x_{k-1}` (`xⱼ ~ μ j` independent), built recursively;
  `map_prod_pi_eq_prodLaw`: it is the push-forward of `Measure.pi μ` by the product.
* `prodLaw_isProb`, `prodLaw_support`: a probability law on `[1, 2^r]` when every `μ j` is a
  probability law on `[1,2]`.
* `integral_pi_eq_start`: `T(μ)(ξ) = ∫ e(2ξ z w) d(halfLaw μ₀ ⊗ prodLaw (m+1) (μ ∘ succ))`.
* `integral_prodLaw_succ`: `∫ e(ζ z w) d(λ ⊗ prodLaw (r+1) μ) = ∫_v ∫ e(ζ v z y) d(λ ⊗ μ 0) dν(v)`,
  `ν = prodLaw r (μ ∘ succ)`.
* `cs_step`: `‖∫ e(ζ z w) d(λ ⊗ prodLaw (r+1) μ)‖² ≤ ‖∫ e(4ζ m w) d(mix λ (μ 0) ⊗ prodLaw r (μ ∘ succ))‖`.
* `flat_bound`: if `‖∫ e(ζ w z y) d(λ ⊗ μ 0)‖ ≤ B` for all `w ∈ [1, 2^r]`, then
  `‖∫ e(ζ z w) d(λ ⊗ prodLaw (r+1) μ)‖ ≤ B`.
-/

open MeasureTheory

namespace Submission.Obl.k4_oss_unit_decay


noncomputable def prodLaw : (k : ℕ) → (Fin k → Measure ℝ) → Measure ℝ
  | 0, _ => Measure.dirac 1
  | k + 1, μ => Measure.map (fun p : ℝ × ℝ => p.1 * p.2)
      ((μ 0).prod (prodLaw k (fun j => μ j.succ)))

theorem prodLaw_isProb : ∀ (r : ℕ) (μ : Fin r → Measure ℝ),
    (∀ j, IsProbabilityMeasure (μ j)) → IsProbabilityMeasure (prodLaw r μ)
  | 0, μ, _ => by rw [prodLaw]; infer_instance
  | r + 1, μ, hμ => by
      have := prodLaw_isProb r (fun j => μ j.succ) (fun j => hμ j.succ)
      have := hμ 0
      rw [prodLaw]
      infer_instance

theorem prodLaw_support : ∀ (r : ℕ) (μ : Fin r → Measure ℝ),
    (∀ j, IsProbabilityMeasure (μ j)) → (∀ j, μ j (Set.Icc (1 : ℝ) 2)ᶜ = 0) →
    prodLaw r μ (Set.Icc (1 : ℝ) (2 ^ r))ᶜ = 0
  | 0, μ, _, _ => by
      rw [prodLaw, Measure.dirac_apply' _ measurableSet_Icc.compl]
      simp
  | r + 1, μ, hμ, hsupp => by
      have := prodLaw_isProb r (fun j => μ j.succ) (fun j => hμ j.succ)
      have := hμ 0
      have ih := prodLaw_support r (fun j => μ j.succ) (fun j => hμ j.succ) (fun j => hsupp j.succ)
      have h0 : ∀ᵐ y ∂(μ 0), y ∈ Set.Icc (1 : ℝ) 2 := hsupp 0
      have h1 : ∀ᵐ w ∂(prodLaw r (fun j => μ j.succ)), w ∈ Set.Icc (1 : ℝ) (2 ^ r) := ih
      have hp : ∀ᵐ p ∂((μ 0).prod (prodLaw r (fun j => μ j.succ))),
          p.1 ∈ Set.Icc (1 : ℝ) 2 ∧ p.2 ∈ Set.Icc (1 : ℝ) (2 ^ r) := by
        apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
        filter_upwards [h0] with y hy
        filter_upwards [h1] with w hw
        exact ⟨hy, hw⟩
      change ∀ᵐ z ∂(prodLaw (r + 1) μ), z ∈ Set.Icc (1 : ℝ) (2 ^ (r + 1))
      rw [prodLaw]
      apply (ae_map_iff (by fun_prop) (show MeasurableSet {z : ℝ | z ∈ Set.Icc (1 : ℝ) (2 ^ (r + 1))}
        from measurableSet_Icc)).2
      filter_upwards [hp] with p hp
      obtain ⟨⟨hy1, hy2⟩, ⟨hw1, hw2⟩⟩ := hp
      refine ⟨by nlinarith, ?_⟩
      rw [pow_succ]
      nlinarith


theorem map_prod_pi_eq_prodLaw : ∀ (k : ℕ) (μ : Fin k → Measure ℝ),
    (∀ j, IsProbabilityMeasure (μ j)) →
    Measure.map (fun x : Fin k → ℝ => ∏ j, x j) (Measure.pi μ) = prodLaw k μ
  | 0, μ, _ => by
      rw [Measure.pi_of_empty, Measure.map_dirac' (by fun_prop), prodLaw]
      simp
  | k + 1, μ, hμ => by
      have := hμ
      have ih := map_prod_pi_eq_prodLaw k (fun j => μ j.succ) (fun j => hμ j.succ)
      have hmp := measurePreserving_piFinSuccAbove μ 0
      have hfac : (fun x : Fin (k + 1) → ℝ => ∏ j, x j) =
          (fun p : ℝ × ℝ => p.1 * p.2) ∘ (Prod.map id (fun y : Fin k → ℝ => ∏ j, y j)) ∘
            (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0) := by
        funext x
        simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove, Fin.tail]
      rw [hfac, ← Measure.map_map (by fun_prop) (by fun_prop),
        ← Measure.map_map (by fun_prop) (by fun_prop), hmp.map_eq]
      simp only [Fin.succAbove_zero]
      rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, ih, prodLaw]


theorem norm_phase (ξ t : ℝ) : ‖phase ξ t‖ = 1 := by
  unfold phase
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_phase (ξ : ℝ) : Continuous (phase ξ) := by
  unfold phase
  fun_prop

theorem integrable_phase_comp {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    {f : α → ℝ} (hf : Measurable f) (ζ : ℝ) : Integrable (fun a => phase ζ (f a)) P :=
  Integrable.of_bound ((continuous_phase ζ).comp_aestronglyMeasurable hf.aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun a => (norm_phase ζ (f a)).le)

theorem aesm_phase_mul (ζ : ℝ) (P : Measure (ℝ × ℝ)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => phase ζ (p.1 * p.2)) P :=
  ((continuous_phase ζ).comp (continuous_fst.mul continuous_snd)).aestronglyMeasurable

theorem integral_pi_eq_start (m : ℕ) (μ : Fin (m + 2) → Measure ℝ)
    (hμ : ∀ j, IsProbabilityMeasure (μ j)) (ξ : ℝ) :
    ∫ x : Fin (m + 2) → ℝ, phase ξ (∏ j, x j) ∂(Measure.pi μ) =
      ∫ p : ℝ × ℝ, phase (2 * ξ) (p.1 * p.2)
        ∂((halfLaw (μ 0)).prod (prodLaw (m + 1) (fun j => μ j.succ))) := by
  have := hμ
  have hν := prodLaw_isProb (m + 1) (fun j => μ j.succ) (fun j => hμ j.succ)
  have h1 : ∫ x : Fin (m + 2) → ℝ, phase ξ (∏ j, x j) ∂(Measure.pi μ) =
      ∫ w, phase ξ w ∂(Measure.map (fun x : Fin (m + 2) → ℝ => ∏ j, x j) (Measure.pi μ)) :=
    (integral_map (by fun_prop) (continuous_phase ξ).aestronglyMeasurable).symm
  rw [h1, map_prod_pi_eq_prodLaw _ _ hμ, prodLaw,
    integral_map (by fun_prop) (continuous_phase ξ).aestronglyMeasurable]
  have h2 : (halfLaw (μ 0)).prod (prodLaw (m + 1) (fun j => μ j.succ)) =
      Measure.map (Prod.map (fun x : ℝ => x / 2) id) ((μ 0).prod (prodLaw (m + 1) (fun j => μ j.succ))) := by
    rw [halfLaw, ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
  rw [h2, integral_map (by fun_prop) (aesm_phase_mul _ _)]
  congr 1
  funext p
  simp only [phase, Prod.map_fst, Prod.map_snd, id]
  congr 3
  ring

theorem integral_prodLaw_succ (r : ℕ) (lam : Measure ℝ) [IsProbabilityMeasure lam]
    (μ : Fin (r + 1) → Measure ℝ) (hμ : ∀ j, IsProbabilityMeasure (μ j)) (ζ : ℝ) :
    ∫ p : ℝ × ℝ, phase ζ (p.1 * p.2) ∂(lam.prod (prodLaw (r + 1) μ)) =
      ∫ v, (∫ p : ℝ × ℝ, phase (ζ * v) (p.1 * p.2) ∂(lam.prod (μ 0)))
        ∂(prodLaw r (fun j => μ j.succ)) := by
  have := hμ
  have hν := prodLaw_isProb r (fun j => μ j.succ) (fun j => hμ j.succ)
  set ν := prodLaw r (fun j => μ j.succ) with hνdef
  have h1 : lam.prod (prodLaw (r + 1) μ) =
      Measure.map (Prod.map id (fun p : ℝ × ℝ => p.1 * p.2)) (lam.prod ((μ 0).prod ν)) := by
    rw [prodLaw, ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
  calc ∫ p : ℝ × ℝ, phase ζ (p.1 * p.2) ∂(lam.prod (prodLaw (r + 1) μ))
      = ∫ q : ℝ × (ℝ × ℝ), phase ζ (q.1 * (q.2.1 * q.2.2)) ∂(lam.prod ((μ 0).prod ν)) := by
        rw [h1, integral_map (by fun_prop) (aesm_phase_mul _ _)]
        rfl
    _ = ∫ q : (ℝ × ℝ) × ℝ, phase ζ (q.1.1 * (q.1.2 * q.2)) ∂((lam.prod (μ 0)).prod ν) :=
        ((measurePreserving_prodAssoc lam (μ 0) ν).integral_comp'
          (fun q : ℝ × (ℝ × ℝ) => phase ζ (q.1 * (q.2.1 * q.2.2)))).symm
    _ = ∫ v, ∫ p : ℝ × ℝ, phase ζ (p.1 * (p.2 * v)) ∂(lam.prod (μ 0)) ∂ν :=
        integral_prod_symm _ (integrable_phase_comp (by fun_prop) ζ)
    _ = ∫ v, (∫ p : ℝ × ℝ, phase (ζ * v) (p.1 * p.2) ∂(lam.prod (μ 0))) ∂ν := by
        congr 1
        funext v
        congr 1
        funext p
        simp only [phase]
        congr 3
        ring


theorem flat_bound (r : ℕ) (lam : Measure ℝ) [IsProbabilityMeasure lam] (μ : Fin (r + 1) → Measure ℝ)
    (hμ : ∀ j, IsProbabilityMeasure (μ j)) (hsupp : ∀ j, μ j (Set.Icc (1 : ℝ) 2)ᶜ = 0)
    (ζ B : ℝ)
    (hB : ∀ w : ℝ, 1 ≤ w → w ≤ 2 ^ r →
      ‖∫ p : ℝ × ℝ, phase (ζ * w) (p.1 * p.2) ∂(lam.prod (μ 0))‖ ≤ B) :
    ‖∫ p : ℝ × ℝ, phase ζ (p.1 * p.2) ∂(lam.prod (prodLaw (r + 1) μ))‖ ≤ B := by
  have := hμ
  have hν := prodLaw_isProb r (fun j => μ j.succ) (fun j => hμ j.succ)
  have hs := prodLaw_support r (fun j => μ j.succ) (fun j => hμ j.succ) (fun j => hsupp j.succ)
  rw [integral_prodLaw_succ r lam μ hμ ζ]
  have hsupp' : ∀ᵐ v ∂(prodLaw r (fun j => μ j.succ)), v ∈ Set.Icc (1 : ℝ) (2 ^ r) := hs
  have hae : ∀ᵐ v ∂(prodLaw r (fun j => μ j.succ)),
      ‖∫ p : ℝ × ℝ, phase (ζ * v) (p.1 * p.2) ∂(lam.prod (μ 0))‖ ≤ B := by
    filter_upwards [hsupp'] with v hv
    exact hB v hv.1 hv.2
  calc _ ≤ B * (prodLaw r (fun j => μ j.succ)).real Set.univ := norm_integral_le_of_norm_le_const hae
    _ = B := by simp

theorem phase_mul_conj (a x y : ℝ) :
    phase a x * starRingEnd ℂ (phase a y) = phase a (x - y) := by
  unfold phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Cauchy–Schwarz for a probability law: `‖∫ g‖² ≤ ∫ ‖g‖²`. -/
theorem norm_integral_sq_le {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {g : α → ℂ} (hg : Integrable g ν) (hg2 : Integrable (fun v => ‖g v‖ ^ 2) ν) :
    ‖∫ v, g v ∂ν‖ ^ 2 ≤ ∫ v, ‖g v‖ ^ 2 ∂ν := by
  have h1 : ‖∫ v, g v ∂ν‖ ≤ ∫ v, ‖g v‖ ∂ν := norm_integral_le_integral_norm g
  have h2 : (∫ v, ‖g v‖ ∂ν) ^ 2 ≤ ∫ v, ‖g v‖ ^ 2 ∂ν :=
    (Even.convexOn_pow (𝕜 := ℝ) even_two).map_integral_le (continuous_pow 2).continuousOn
      isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hg.norm hg2
  calc ‖∫ v, g v ∂ν‖ ^ 2 ≤ (∫ v, ‖g v‖ ∂ν) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2


theorem continuous_phase₂ : Continuous (fun q : ℝ × ℝ => phase q.1 q.2) := by
  unfold phase
  fun_prop

theorem norm_integral_phase_le {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (f : α → ℝ) (ζ : ℝ) : ‖∫ a, phase ζ (f a) ∂P‖ ≤ 1 := by
  calc _ ≤ 1 * P.real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun a => (norm_phase ζ (f a)).le)
    _ = 1 := by simp

theorem cs_step (r : ℕ) (lam : Measure ℝ) [IsProbabilityMeasure lam] (μ : Fin (r + 1) → Measure ℝ)
    (hμ : ∀ j, IsProbabilityMeasure (μ j)) (ζ : ℝ) :
    ‖∫ p : ℝ × ℝ, phase ζ (p.1 * p.2) ∂(lam.prod (prodLaw (r + 1) μ))‖ ^ 2 ≤
      ‖∫ p : ℝ × ℝ, phase (4 * ζ) (p.1 * p.2)
        ∂((mix lam (μ 0)).prod (prodLaw r (fun j => μ j.succ)))‖ := by
  have := hμ
  have hν := prodLaw_isProb r (fun j => μ j.succ) (fun j => hμ j.succ)
  set ν := prodLaw r (fun j => μ j.succ) with hνdef
  set P := lam.prod (μ 0) with hPdef
  set g : ℝ → ℂ := fun v => ∫ p : ℝ × ℝ, phase (ζ * v) (p.1 * p.2) ∂P with hgdef
  have key : ∀ v : ℝ, (((‖g v‖ ^ 2 : ℝ)) : ℂ) = ∫ m, phase (4 * ζ) (m * v) ∂(mix lam (μ 0)) := by
    intro v
    have hm : AEStronglyMeasurable (fun m : ℝ => phase (4 * ζ) (m * v)) (mix lam (μ 0)) :=
      ((continuous_phase _).comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hgdef, ← integral_conj, ← integral_prod_mul,
      mix, integral_map (by fun_prop) hm]
    congr 1
    funext q
    rw [phase_mul_conj]
    simp only [phase]
    congr 3
    ring
  have hgm : AEStronglyMeasurable g ν :=
    (continuous_phase₂.comp ((continuous_const.mul continuous_fst).prodMk
      ((continuous_fst.comp continuous_snd).mul (continuous_snd.comp continuous_snd)))).aestronglyMeasurable.integral_prod_right'
  have hg1 : ∀ v, ‖g v‖ ≤ 1 := fun v => norm_integral_phase_le P (fun p => p.1 * p.2) (ζ * v)
  have hgi : Integrable g ν := Integrable.of_bound hgm 1 (Filter.Eventually.of_forall hg1)
  have hg2i : Integrable (fun v => ‖g v‖ ^ 2) ν :=
    Integrable.of_bound (hgm.norm.pow 2) 1 (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (norm_nonneg _) (hg1 v))
  have hmix : IsProbabilityMeasure (mix lam (μ 0)) := by
    unfold mix
    infer_instance
  have hR : ∫ p : ℝ × ℝ, phase (4 * ζ) (p.1 * p.2) ∂((mix lam (μ 0)).prod ν) =
      ((∫ v, ‖g v‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [integral_prod_symm _ (integrable_phase_comp (by fun_prop) _), ← integral_complex_ofReal]
    congr 1
    funext v
    rw [key v]
  rw [integral_prodLaw_succ r lam μ hμ ζ, hR, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun v => by positivity)]
  exact norm_integral_sq_le hgi hg2i

end Submission.Obl.k4_oss_unit_decay
