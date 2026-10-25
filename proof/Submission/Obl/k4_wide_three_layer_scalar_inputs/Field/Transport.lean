/- Time rescaling lemmas adapted within this LOT tree from o218/x0764, commit
a57aabc6806d303a53728cab0d5e6ea27469d825,
`Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/BlockRescale.lean`
(as ported to o250 by x0879, `Submission/Obl/k4_horizontal_wide_interval_return/BlockRescale.lean`).
The rest is new. -/
import Mathlib

set_option linter.unusedVariables false

/-!
# The common-field principle applied inside one true block

`FieldAt S C₀ A θ ε η N` is the finite statement of the frozen common-field principle at fixed
parameters.  `field_transport` applies it to an incidence law `lam` supported in one true block
`A × [t₀, t₀ + q]`, written in the ORIGINAL coordinates: time `t`, prior `ν`, palette `π`, the
original velocity `b 3` and intercept `b 0`.  The law is rescaled to unit time and normalized by
`q ν(A)`; the normalized intercept is `(b 0 + t₀ b 3 - c₀ - t₀ c₁)/q` and the velocity shift is
`v₀ = c₁`, so the field coordinate `z₁` is exactly `zZ = (b 0 + t b 3 - c₀ - t c₁)/q`.
All hypotheses and the conclusion are stated for `lam` itself, with masses relative to `q ν(A)`.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Field

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- The frozen common-field principle at fixed parameters `S, C₀, A, θ, ε, η, N`. -/
def FieldAt (S C₀ A θ ε η N : ℝ) : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (π : MeasureTheory.Measure ℝ) (b v : α → ℝ) (v₀ χb χv : ℝ) (f : α × ℝ → Fin 2 → ℝ) (L : (ℤ × ℤ) → Finset (Fin 3 → ℝ)), (fun (δ e : ℝ) => (fun (z : α × ℝ → Fin 2 → ℝ) => (fun (state : α × ℝ → Fin 4 → ℤ) => Measurable b → Measurable v → Measurable f → MeasureTheory.IsProbabilityMeasure ν → MeasureTheory.IsProbabilityMeasure π → N ^ (-A) ≤ χb → χb ≤ 1 → N ^ (-A) ≤ χv → χv ≤ 1 → (∀ l, |b l| + |v l| + |v₀| ≤ N ^ η) → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ᵐ p ∂μ, ∀ i, |f p i| ≤ N ^ η) → (∀ q : Fin 2 → ℤ, μ {p | (fun i => ⌊z p i / δ⌋) = q} ≤ ENNReal.ofReal (N ^ η * δ ^ 2)) → (∀ x r : ℝ, δ ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (q : Fin 4 → ℤ) (j : ℤ), μ {p | state p = q ∧ ⌊v p.1 / δ⌋ = j} ≤ ENNReal.ofReal (N ^ η) * μ {p | state p = q} * π (Set.Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ))) → (∀ q, ((L q).card : ℝ) ≤ N ^ η) → (∀ q, ∀ a ∈ L q, ∀ i, |a i| ≤ N ^ η) → (∀ᵐ p ∂μ, ∃ a ∈ L (⌊b p.1 / χb⌋, ⌊v p.1 / χv⌋), |f p 0 - a 0 - a 1 * p.2| ≤ N ^ η * e ∧ |f p 1 - a 2| ≤ N ^ η * e) → ∃ C : Fin 4 → ℝ, (∀ i, |C i| ≤ N ^ ε) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | |f p 0 - C 0 - C 1 * z p 0 - C 2 * z p 1| ≤ N ^ ε * e ∧ |f p 1 - C 3| ≤ N ^ ε * e}) (fun p => ![⌊z p 0 / δ⌋, ⌊z p 1 / δ⌋, ⌊f p 0 / e⌋, ⌊f p 1 / e⌋])) (fun p => ![p.2, b p.1 + p.2 * (v p.1 - v₀)])) (N ^ (-(C₀ * (A + θ)))) (N ^ (-θ))


/-! ### Rescaling one time block (adapted, see the header) -/

section Rescale

variable {α : Type*} [MeasurableSpace α]

/-- The affine rescaling of the time block `[t₀, t₀ + q]` to unit time. -/
def blockRescale (t₀ q : ℝ) (p : α × ℝ) : α × ℝ := (p.1, (p.2 - t₀) / q)

theorem measurable_blockRescale (t₀ q : ℝ) : Measurable (blockRescale (α := α) t₀ q) :=
  measurable_fst.prodMk ((measurable_snd.sub_const t₀).div_const q)

omit [MeasurableSpace α] in
theorem blockRescale_eq_prodMap (t₀ q : ℝ) :
    blockRescale (α := α) t₀ q = Prod.map id (fun t : ℝ => (t - t₀) / q) := rfl

/-- Lebesgue measure pushed through `t ↦ (t - t₀)/q` is `q` times Lebesgue measure. -/
theorem map_volume_block (t₀ q : ℝ) (hq : 0 < q) :
    (volume : Measure ℝ).map (fun t => (t - t₀) / q) = ENNReal.ofReal q • volume := by
  have h1 : (fun t : ℝ => (t - t₀) / q) = (fun x => q⁻¹ * x) ∘ (fun t => t + -t₀) := by
    funext t; simp [div_eq_inv_mul, sub_eq_add_neg]
  rw [h1, ← Measure.map_map (measurable_const_mul _) (measurable_add_const (-t₀)),
    Measure.IsAddRightInvariant.map_add_right_eq_self (-t₀),
    Real.map_volume_mul_left (inv_ne_zero hq.ne'), inv_inv, abs_of_pos hq]

/-- A law supported on `A × ℝ` and dominated by `C · ν ⊗ dt`, rescaled in time from a block of
length `q`, is dominated by `C q · ν|_A ⊗ dt`. -/
theorem map_blockRescale_le (ν : Measure α) [SFinite ν] {A : Set α} (hA : MeasurableSet A)
    (t₀ q : ℝ) (hq : 0 < q) (lam : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hlam : lam ≤ C • ν.prod volume) (hsupp : ∀ᵐ p ∂lam, p.1 ∈ A) :
    lam.map (blockRescale t₀ q) ≤ (C * ENNReal.ofReal q) • (ν.restrict A).prod volume := by
  have hres : lam = lam.restrict (A ×ˢ univ) :=
    (Measure.restrict_eq_self_of_ae_mem (by
      filter_upwards [hsupp] with p hp using ⟨hp, mem_univ _⟩)).symm
  have h1 : lam ≤ C • (ν.restrict A).prod volume := by
    have h2 := Measure.restrict_mono (subset_refl (A ×ˢ (univ : Set ℝ))) hlam
    rw [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ] at h2
    rw [hres]
    exact h2
  calc lam.map (blockRescale t₀ q)
      ≤ (C • (ν.restrict A).prod volume).map (blockRescale t₀ q) :=
        Measure.map_mono h1 (measurable_blockRescale t₀ q)
    _ = C • ((ν.restrict A).map id).prod ((volume : Measure ℝ).map fun t => (t - t₀) / q) := by
        rw [Measure.map_smul C (measurable_blockRescale t₀ q).aemeasurable, blockRescale_eq_prodMap,
          ← Measure.map_prod_map (f := id) (g := fun t : ℝ => (t - t₀) / q) _ _ measurable_id
            ((measurable_sub_const t₀).div_const q)]
    _ = (C * ENNReal.ofReal q) • (ν.restrict A).prod volume := by
        rw [Measure.map_id, map_volume_block t₀ q hq, Measure.prod_smul_right, smul_smul]

/-- The conditional prior `ν(· | A) = ν(A)⁻¹ ν|_A` is a probability measure when
`0 < ν A < ∞`. -/
theorem isProbabilityMeasure_cond (ν : Measure α) {A : Set α} (h0 : ν A ≠ 0) (htop : ν A ≠ ∞) :
    IsProbabilityMeasure ((ν A)⁻¹ • ν.restrict A) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
    ENNReal.inv_mul_cancel h0 htop]

/-- Rescaled and normalized by `q ν(A)`, a law dominated by `C · ν ⊗ dt` and supported on
`A × ℝ` is dominated by `C` times the conditional prior times Lebesgue measure. -/
theorem normalized_blockRescale_le (ν : Measure α) [SFinite ν] {A : Set α} (hA : MeasurableSet A)
    (h0 : ν A ≠ 0) (htop : ν A ≠ ∞) (t₀ q : ℝ) (hq : 0 < q) (lam : Measure (α × ℝ))
    (C : ℝ≥0∞) (hlam : lam ≤ C • ν.prod volume) (hsupp : ∀ᵐ p ∂lam, p.1 ∈ A) :
    (ENNReal.ofReal q * ν A)⁻¹ • lam.map (blockRescale t₀ q) ≤
      C • ((ν A)⁻¹ • ν.restrict A).prod volume := by
  have hq' : ENNReal.ofReal q ≠ 0 := by simpa using hq
  calc (ENNReal.ofReal q * ν A)⁻¹ • lam.map (blockRescale t₀ q)
      ≤ (ENNReal.ofReal q * ν A)⁻¹ • ((C * ENNReal.ofReal q) • (ν.restrict A).prod volume) :=
        smul_le_smul_left _ (map_blockRescale_le ν hA t₀ q hq lam C hlam hsupp)
    _ = C • ((ν A)⁻¹ • ν.restrict A).prod volume := by
        rw [Measure.prod_smul_left, smul_smul, smul_smul]
        congr 1
        rw [ENNReal.mul_inv (Or.inl hq') (Or.inl ENNReal.ofReal_ne_top)]
        calc (ENNReal.ofReal q)⁻¹ * (ν A)⁻¹ * (C * ENNReal.ofReal q)
            = C * ((ENNReal.ofReal q)⁻¹ * ENNReal.ofReal q) * (ν A)⁻¹ := by ring
          _ = C * (ν A)⁻¹ := by
            rw [ENNReal.inv_mul_cancel hq' ENNReal.ofReal_ne_top, mul_one]

/-- The block rescaling as a measurable equivalence. -/
def rescaleEquiv (t₀ q : ℝ) (hq : q ≠ 0) : α × ℝ ≃ᵐ α × ℝ :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl α)
    ((MeasurableEquiv.addRight (-t₀)).trans (MeasurableEquiv.mulLeft₀ q⁻¹ (inv_ne_zero hq)))

theorem rescaleEquiv_apply (t₀ q : ℝ) (hq : q ≠ 0) (p : α × ℝ) :
    rescaleEquiv t₀ q hq p = blockRescale t₀ q p := by
  simp [rescaleEquiv, blockRescale, MeasurableEquiv.prodCongr, MeasurableEquiv.trans,
    MeasurableEquiv.mulLeft₀, MeasurableEquiv.addRight, div_eq_inv_mul, sub_eq_add_neg]
  rfl

theorem coe_rescaleEquiv (t₀ q : ℝ) (hq : q ≠ 0) :
    (rescaleEquiv (α := α) t₀ q hq : α × ℝ → α × ℝ) = blockRescale t₀ q :=
  funext (rescaleEquiv_apply t₀ q hq)

theorem rescaleEquiv_symm_apply (t₀ q : ℝ) (hq : q ≠ 0) (p : α × ℝ) :
    (rescaleEquiv t₀ q hq).symm p = (p.1, t₀ + q * p.2) := by
  apply (rescaleEquiv (α := α) t₀ q hq).injective
  rw [MeasurableEquiv.apply_symm_apply, rescaleEquiv_apply]
  simp only [blockRescale]
  ext
  · rfl
  · field_simp; ring

end Rescale


/-! ### Clamping and ENNReal bookkeeping -/

/-- Clamp to `[-B, B]`. -/
def clampB (B x : ℝ) : ℝ := max (-B) (min B x)

theorem clampB_of_abs_le {B x : ℝ} (h : |x| ≤ B) : clampB B x = x := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  unfold clampB
  rw [min_eq_right h2, max_eq_right h1]

theorem abs_clampB_le {B : ℝ} (x : ℝ) (hB : 0 ≤ B) : |clampB B x| ≤ B := by
  unfold clampB
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem le_inv_mul_of_mul_le {x y c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (h : x * c ≤ y) :
    x ≤ c⁻¹ * y :=
  calc x = c⁻¹ * (x * c) := by
        rw [mul_comm x c, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    _ ≤ c⁻¹ * y := mul_le_mul_right h _

theorem mul_le_of_le_inv_mul {x y c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (h : x ≤ c⁻¹ * y) :
    x * c ≤ y :=
  calc x * c ≤ c⁻¹ * y * c := mul_le_mul_left h _
    _ = y := by rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]

theorem inv_mul_le_of_le_mul {x y c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (h : y ≤ x * c) :
    c⁻¹ * y ≤ x :=
  calc c⁻¹ * y ≤ c⁻¹ * (x * c) := mul_le_mul_right h _
    _ = x := by rw [mul_comm x c, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-! ### The common field inside one true block -/

section Transport

variable {α : Type} [MeasurableSpace α]

/-- **The common-field principle in the original coordinates of one true block.**

The incidence law `lam` lives in the block `A × [t₀, t₀ + q]`; the normalized time is
`(t - t₀)/q`, the normalized intercept coordinate is `(b 0 + t b 3 - c₀ - t c₁)/q`, the coarse
charts are the bins of the normalized intercept `(b 0 + t₀ b 3 - c₀ - t₀ c₁)/q` (width `χb`)
and of the original velocity `b 3` (width `χv`), and the fine states use the original velocity
bins of width `δ` against the original palette `π`.  Masses are relative to `q ν(A)`. -/
theorem field_transport {S C₀ A θF ε η N δ e : ℝ} (hF : FieldAt S C₀ A θF ε η N) (hN : 0 < N)
    (hδ : δ = N ^ (-(C₀ * (A + θF)))) (he : e = N ^ (-θF))
    (ν : Measure α) [IsProbabilityMeasure ν] (π : Measure ℝ) [IsProbabilityMeasure π]
    (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (Aset : Set α) (hA : MeasurableSet Aset) (hA0 : ν Aset ≠ 0)
    (t₀ q c0 c1 χb χv K₀ : ℝ) (hq : 0 < q)
    (lam : Measure (α × ℝ)) (f : α × ℝ → Fin 2 → ℝ) (hf : Measurable f)
    (L : (ℤ × ℤ) → Finset (Fin 3 → ℝ))
    (hχb : N ^ (-A) ≤ χb) (hχb1 : χb ≤ 1) (hχv : N ^ (-A) ≤ χv) (hχv1 : χv ≤ 1)
    (hc1 : |c1| ≤ N ^ η / 3) (hK₀ : K₀ ≤ N ^ η)
    (hdom : lam ≤ ENNReal.ofReal K₀ • ν.prod volume)
    (hsupp : ∀ᵐ p ∂lam, p.1 ∈ Aset ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
      |(b p.1 0 + t₀ * b p.1 3 - c0 - t₀ * c1) / q| ≤ N ^ η / 3 ∧ |b p.1 3| ≤ N ^ η / 3)
    (hmass : ENNReal.ofReal (N ^ (-η)) * (ENNReal.ofReal q * ν Aset) ≤ lam univ)
    (hfb : ∀ᵐ p ∂lam, ∀ i, |f p i| ≤ N ^ η)
    (hcell : ∀ Q : Fin 2 → ℤ, lam {p | ⌊(p.2 - t₀) / q / δ⌋ = Q 0 ∧
      ⌊(b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q / δ⌋ = Q 1} ≤
        ENNReal.ofReal (N ^ η * δ ^ 2) * (ENNReal.ofReal q * ν Aset))
    (hfrost : ∀ x r : ℝ, δ ≤ r → r ≤ 1 →
      π (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S))
    (hstate : ∀ (Q : Fin 4 → ℤ) (j : ℤ),
      lam {p | ![⌊(p.2 - t₀) / q / δ⌋, ⌊(b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q / δ⌋,
          ⌊f p 0 / e⌋, ⌊f p 1 / e⌋] = Q ∧ ⌊b p.1 3 / δ⌋ = j} ≤
        ENNReal.ofReal (N ^ η) *
          lam {p | ![⌊(p.2 - t₀) / q / δ⌋, ⌊(b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q / δ⌋,
            ⌊f p 0 / e⌋, ⌊f p 1 / e⌋] = Q} *
          π (Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ)))
    (hLcard : ∀ Q, ((L Q).card : ℝ) ≤ N ^ η) (hLbd : ∀ Q, ∀ a ∈ L Q, ∀ i, |a i| ≤ N ^ η)
    (hfit : ∀ᵐ p ∂lam, ∃ a ∈ L (⌊(b p.1 0 + t₀ * b p.1 3 - c0 - t₀ * c1) / q / χb⌋,
        ⌊b p.1 3 / χv⌋), |f p 0 - a 0 - a 1 * ((p.2 - t₀) / q)| ≤ N ^ η * e ∧
          |f p 1 - a 2| ≤ N ^ η * e) :
    ∃ C : Fin 4 → ℝ, (∀ i, |C i| ≤ N ^ ε) ∧
      ENNReal.ofReal (N ^ (-ε)) * (ENNReal.ofReal q * ν Aset) ≤
        lam {p | |f p 0 - C 0 - C 1 * ((p.2 - t₀) / q) -
            C 2 * ((b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q)| ≤ N ^ ε * e ∧
          |f p 1 - C 3| ≤ N ^ ε * e} := by
  subst hδ he
  have hq0 : q ≠ 0 := hq.ne'
  have hAtop : ν Aset ≠ ∞ := measure_ne_top ν Aset
  set Φ : α × ℝ ≃ᵐ α × ℝ := rescaleEquiv t₀ q hq0 with hΦdef
  set c : ℝ≥0∞ := ENNReal.ofReal q * ν Aset with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero (by simpa using hq) hA0
  have hctop : c ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAtop
  set μ' : Measure (α × ℝ) := c⁻¹ • lam.map Φ with hμ'
  have hμ'_apply : ∀ E, μ' E = c⁻¹ * lam (Φ ⁻¹' E) := by
    intro E; rw [hμ', Measure.smul_apply, MeasurableEquiv.map_apply, smul_eq_mul]
  set ν' : Measure α := (ν Aset)⁻¹ • ν.restrict Aset with hν'
  have : IsProbabilityMeasure ν' := isProbabilityMeasure_cond ν hA0 hAtop
  set B : ℝ := N ^ η / 3 with hBdef
  have hB0 : 0 ≤ B := by positivity
  set y0 : α → ℝ := fun l => (b l 0 + t₀ * b l 3 - c0 - t₀ * c1) / q with hy0
  set b' : α → ℝ := fun l => clampB B (y0 l) with hb'
  set v' : α → ℝ := fun l => clampB B (b l 3) with hv'
  set f' : α × ℝ → Fin 2 → ℝ := fun p => f (Φ.symm p) with hf'
  -- measurability
  have hbi : ∀ i, Measurable fun l => b l i := fun i => (measurable_pi_apply i).comp hb
  have hy0m : Measurable y0 :=
    ((((hbi 0).add ((hbi 3).const_mul t₀)).sub_const c0).sub_const (t₀ * c1)).div_const q
  have hb'm : Measurable b' := measurable_const.max (measurable_const.min hy0m)
  have hv'm : Measurable v' := measurable_const.max (measurable_const.min (hbi 3))
  have hf'm : Measurable f' := hf.comp Φ.symm.measurable
  -- pointwise identities
  have hΦ : ∀ p : α × ℝ, Φ p = (p.1, (p.2 - t₀) / q) := fun p => rescaleEquiv_apply t₀ q hq0 p
  have hf'Φ : ∀ p, f' (Φ p) = f p := by
    intro p; simp only [hf', MeasurableEquiv.symm_apply_apply]
  have hgood : ∀ᵐ p ∂lam, p.1 ∈ Aset ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧ b' p.1 = y0 p.1 ∧
      v' p.1 = b p.1 3 := by
    filter_upwards [hsupp] with p hp
    exact ⟨hp.1, hp.2.1, clampB_of_abs_le hp.2.2.1, clampB_of_abs_le hp.2.2.2⟩
  have hzΦ : ∀ p : α × ℝ, b' p.1 = y0 p.1 → v' p.1 = b p.1 3 →
      b' (Φ p).1 + (Φ p).2 * (v' (Φ p).1 - c1) =
        (b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q := by
    intro p h1 h2
    rw [hΦ]
    simp only
    rw [h1, h2, hy0]
    field_simp
    ring
  -- the hypotheses of the field principle for the normalized law
  have hbound : ∀ l, |b' l| + |v' l| + |c1| ≤ N ^ η := by
    intro l
    have h1 := abs_clampB_le (y0 l) hB0
    have h2 := abs_clampB_le (b l 3) hB0
    simp only [hb', hv']
    linarith
  have hdom' : μ' ≤ ENNReal.ofReal (N ^ η) • ν'.prod volume := by
    have hmap : lam.map Φ = lam.map (blockRescale t₀ q) := by
      rw [hΦdef, coe_rescaleEquiv]
    have h1 : μ' ≤ ENNReal.ofReal K₀ • ν'.prod volume := by
      rw [hμ', hmap, hcdef, hν']
      exact normalized_blockRescale_le ν hA hA0 hAtop t₀ q hq lam _ hdom
        (hsupp.mono fun p hp => hp.1)
    refine h1.trans ?_
    intro E
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hK₀) _
  have hsupp' : μ' (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [hμ'_apply]
    have : lam (Φ ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hsupp] with p hp
      simp only [mem_preimage, mem_compl_iff, mem_prod, mem_univ, true_and, not_not, hΦ,
        mem_Icc]
      obtain ⟨h0, h1⟩ := hp.2.1
      refine ⟨div_nonneg (by linarith) hq.le, ?_⟩
      rw [div_le_iff₀ hq]; linarith
    rw [this, mul_zero]
  have hmass' : ENNReal.ofReal (N ^ (-η)) ≤ μ' univ := by
    rw [hμ'_apply, preimage_univ]
    exact le_inv_mul_of_mul_le hc0 hctop hmass
  have hfb' : ∀ᵐ p ∂μ', ∀ i, |f' p i| ≤ N ^ η := by
    refine Measure.ae_smul_measure ?_ _
    rw [Φ.measurableEmbedding.ae_map_iff]
    filter_upwards [hfb] with p hp
    rw [hf'Φ]; exact hp
  have hcell' : ∀ Q : Fin 2 → ℤ,
      μ' {p | (fun i => ⌊(![p.2, b' p.1 + p.2 * (v' p.1 - c1)] : Fin 2 → ℝ) i /
          N ^ (-(C₀ * (A + θF)))⌋) = Q} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-(C₀ * (A + θF)))) ^ 2) := by
    intro Q
    rw [hμ'_apply]
    have hset : lam (Φ ⁻¹' {p | (fun i => ⌊(![p.2, b' p.1 + p.2 * (v' p.1 - c1)] : Fin 2 → ℝ) i /
          N ^ (-(C₀ * (A + θF)))⌋) = Q}) =
        lam {p | ⌊(p.2 - t₀) / q / N ^ (-(C₀ * (A + θF)))⌋ = Q 0 ∧
          ⌊(b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q / N ^ (-(C₀ * (A + θF)))⌋ = Q 1} := by
      apply measure_congr
      refine Filter.Eventually.set_eq ?_
      filter_upwards [hgood] with p hp
      simp only [mem_preimage, mem_ofPred_eq, funext_iff, Fin.forall_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hzΦ p hp.2.2.1 hp.2.2.2, hΦ]
    rw [hset]
    exact inv_mul_le_of_le_mul hc0 hctop (hcell Q)
  have hΦ1 : ∀ p : α × ℝ, (Φ p).1 = p.1 := fun p => by rw [hΦ]
  have hΦ2 : ∀ p : α × ℝ, (Φ p).2 = (p.2 - t₀) / q := fun p => by rw [hΦ]
  have hstate' : ∀ (Q : Fin 4 → ℤ) (j : ℤ),
      μ' {p | ![⌊p.2 / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊(b' p.1 + p.2 * (v' p.1 - c1)) / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊f' p 0 / N ^ (-θF)⌋, ⌊f' p 1 / N ^ (-θF)⌋] = Q ∧
          ⌊v' p.1 / N ^ (-(C₀ * (A + θF)))⌋ = j} ≤
        ENNReal.ofReal (N ^ η) *
          μ' {p | ![⌊p.2 / N ^ (-(C₀ * (A + θF)))⌋,
            ⌊(b' p.1 + p.2 * (v' p.1 - c1)) / N ^ (-(C₀ * (A + θF)))⌋,
            ⌊f' p 0 / N ^ (-θF)⌋, ⌊f' p 1 / N ^ (-θF)⌋] = Q} *
          π (Ico ((j : ℝ) * N ^ (-(C₀ * (A + θF)))) (((j : ℝ) + 1) * N ^ (-(C₀ * (A + θF))))) := by
    intro Q j
    rw [hμ'_apply, hμ'_apply]
    have h1 : lam (Φ ⁻¹' {p | ![⌊p.2 / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊(b' p.1 + p.2 * (v' p.1 - c1)) / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊f' p 0 / N ^ (-θF)⌋, ⌊f' p 1 / N ^ (-θF)⌋] = Q ∧
          ⌊v' p.1 / N ^ (-(C₀ * (A + θF)))⌋ = j}) =
        lam {p | ![⌊(p.2 - t₀) / q / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊(b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊f p 0 / N ^ (-θF)⌋, ⌊f p 1 / N ^ (-θF)⌋] = Q ∧
          ⌊b p.1 3 / N ^ (-(C₀ * (A + θF)))⌋ = j} := by
      apply measure_congr
      refine Filter.Eventually.set_eq ?_
      filter_upwards [hgood] with p hp
      simp only [mem_preimage, mem_ofPred_eq]
      rw [hzΦ p hp.2.2.1 hp.2.2.2, hf'Φ, hΦ1, hΦ2, hp.2.2.2]
    have h2 : lam (Φ ⁻¹' {p | ![⌊p.2 / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊(b' p.1 + p.2 * (v' p.1 - c1)) / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊f' p 0 / N ^ (-θF)⌋, ⌊f' p 1 / N ^ (-θF)⌋] = Q}) =
        lam {p | ![⌊(p.2 - t₀) / q / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊(b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q / N ^ (-(C₀ * (A + θF)))⌋,
          ⌊f p 0 / N ^ (-θF)⌋, ⌊f p 1 / N ^ (-θF)⌋] = Q} := by
      apply measure_congr
      refine Filter.Eventually.set_eq ?_
      filter_upwards [hgood] with p hp
      simp only [mem_preimage, mem_ofPred_eq]
      rw [hzΦ p hp.2.2.1 hp.2.2.2, hf'Φ, hΦ2]
    rw [h1, h2]
    calc c⁻¹ * lam _ ≤ c⁻¹ * (ENNReal.ofReal (N ^ η) * lam _ *
          π (Ico ((j : ℝ) * N ^ (-(C₀ * (A + θF)))) (((j : ℝ) + 1) * N ^ (-(C₀ * (A + θF)))))) :=
          mul_le_mul_right (hstate Q j) _
      _ = _ := by ring
  have hfit' : ∀ᵐ p ∂μ', ∃ a ∈ L (⌊b' p.1 / χb⌋, ⌊v' p.1 / χv⌋),
      |f' p 0 - a 0 - a 1 * p.2| ≤ N ^ η * N ^ (-θF) ∧ |f' p 1 - a 2| ≤ N ^ η * N ^ (-θF) := by
    refine Measure.ae_smul_measure ?_ _
    rw [Φ.measurableEmbedding.ae_map_iff]
    filter_upwards [hfit, hgood] with p hp hg
    rw [hf'Φ, hΦ1, hΦ2, hg.2.2.1, hg.2.2.2]
    exact hp
  obtain ⟨C, hC, hCm⟩ : ∃ C : Fin 4 → ℝ, (∀ i, |C i| ≤ N ^ ε) ∧
      ENNReal.ofReal (N ^ (-ε)) ≤ μ' {p | |f' p 0 - C 0 - C 1 * p.2 -
        C 2 * (b' p.1 + p.2 * (v' p.1 - c1))| ≤ N ^ ε * N ^ (-θF) ∧
          |f' p 1 - C 3| ≤ N ^ ε * N ^ (-θF)} :=
    hF α ν' μ' π b' v' c1 χb χv f' L hb'm hv'm hf'm this inferInstance hχb hχb1 hχv hχv1
      hbound hdom' hsupp' hmass' hfb' hcell' hfrost hstate' hLcard hLbd hfit'
  refine ⟨C, hC, ?_⟩
  rw [hμ'_apply] at hCm
  have hset : lam (Φ ⁻¹' {p | |f' p 0 - C 0 - C 1 * p.2 -
        C 2 * (b' p.1 + p.2 * (v' p.1 - c1))| ≤ N ^ ε * N ^ (-θF) ∧
          |f' p 1 - C 3| ≤ N ^ ε * N ^ (-θF)}) =
      lam {p | |f p 0 - C 0 - C 1 * ((p.2 - t₀) / q) -
            C 2 * ((b p.1 0 + p.2 * b p.1 3 - c0 - p.2 * c1) / q)| ≤ N ^ ε * N ^ (-θF) ∧
          |f p 1 - C 3| ≤ N ^ ε * N ^ (-θF)} := by
    apply measure_congr
    refine Filter.Eventually.set_eq ?_
    filter_upwards [hgood] with p hp
    simp only [mem_preimage, mem_ofPred_eq]
    rw [hzΦ p hp.2.2.1 hp.2.2.2, hf'Φ, hΦ2]
  rw [hset] at hCm
  exact mul_le_of_le_inv_mul hc0 hctop hCm

end Transport

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Field
