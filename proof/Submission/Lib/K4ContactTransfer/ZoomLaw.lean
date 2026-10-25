import Mathlib
import Submission.Lib.K4ChartLifting.Mass

/-!
# Zoomed laws of a parent

The contact instance built inside a parent label `Q` uses

* the prior conditioned on the parent assignment, `ν' = ν(A_Q)⁻¹ ν|_{A_Q}`;
* the incidence law restricted to a retained set `S` of the parent box, with
  time rescaled to the unit block, `t' = (t - t₀)/q`, and divided by the
  parent weight `W = q ν(A_Q)`.

This file proves that the zoomed law is dominated by the same constant times
the conditioned prior and Lebesgue measure, is supported in unit time, and
transfers events exactly. Nothing depends on the shape of `S`.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Time rescaling of incidences. -/
def zoomTime (t₀ q : ℝ) (p : α × ℝ) : α × ℝ := (p.1, (p.2 - t₀) / q)

theorem measurable_zoomTime (t₀ q : ℝ) : Measurable (zoomTime (α := α) t₀ q) :=
  measurable_fst.prodMk ((measurable_snd.sub_const _).div_const _)

/-- The prior conditioned on a set. -/
def condPrior (ν : Measure α) (A : Set α) : Measure α := (ν A)⁻¹ • ν.restrict A

theorem condPrior_apply (ν : Measure α) (A : Set α) (E : Set α) (hE : MeasurableSet E) :
    condPrior ν A E = (ν A)⁻¹ * ν (E ∩ A) := by
  rw [condPrior, Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul]

theorem condPrior_isProbability (ν : Measure α) (A : Set α) (h0 : ν A ≠ 0) (htop : ν A ≠ ⊤) :
    IsProbabilityMeasure (condPrior ν A) := by
  constructor
  rw [condPrior, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel h0 htop]

/-- The zoomed, normalized law of a restriction. -/
def zoomLaw (μ : Measure (α × ℝ)) (S : Set (α × ℝ)) (t₀ q : ℝ) (W : ℝ≥0∞) :
    Measure (α × ℝ) :=
  W⁻¹ • Measure.map (zoomTime t₀ q) (μ.restrict S)

theorem zoomLaw_apply (μ : Measure (α × ℝ)) {S : Set (α × ℝ)} (hS : MeasurableSet S)
    (t₀ q : ℝ) (W : ℝ≥0∞) {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    zoomLaw μ S t₀ q W E = W⁻¹ * μ (S ∩ zoomTime t₀ q ⁻¹' E) := by
  rw [zoomLaw, Measure.smul_apply, Measure.map_apply (measurable_zoomTime t₀ q) hE,
    Measure.restrict_apply' hS, smul_eq_mul, inter_comm]

theorem zoomLaw_univ (μ : Measure (α × ℝ)) {S : Set (α × ℝ)} (hS : MeasurableSet S)
    (t₀ q : ℝ) (W : ℝ≥0∞) : zoomLaw μ S t₀ q W univ = W⁻¹ * μ S := by
  rw [zoomLaw_apply μ hS t₀ q W MeasurableSet.univ, preimage_univ, inter_univ]

theorem zoomLaw_mono_set (μ : Measure (α × ℝ)) {S S' : Set (α × ℝ)} (hSS : S ⊆ S')
    (t₀ q : ℝ) (W : ℝ≥0∞) : zoomLaw μ S t₀ q W ≤ zoomLaw μ S' t₀ q W := by
  unfold zoomLaw
  gcongr
  exact measurable_zoomTime t₀ q

theorem zoomLaw_mono_measure {μ ρ : Measure (α × ℝ)} (h : ρ ≤ μ) (S : Set (α × ℝ))
    (t₀ q : ℝ) (W : ℝ≥0∞) : zoomLaw ρ S t₀ q W ≤ zoomLaw μ S t₀ q W := by
  unfold zoomLaw
  gcongr
  exact measurable_zoomTime t₀ q

/-- The zoomed law lives in unit time when the retained set lies in the block. -/
theorem zoomLaw_compl_unit (μ : Measure (α × ℝ)) {S : Set (α × ℝ)} (hS : MeasurableSet S)
    {t₀ q : ℝ} (hq : 0 < q) (W : ℝ≥0∞) (hSb : S ⊆ univ ×ˢ Icc t₀ (t₀ + q)) :
    zoomLaw μ S t₀ q W (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [zoomLaw_apply μ hS t₀ q W ((MeasurableSet.univ.prod measurableSet_Icc).compl)]
  have : S ∩ zoomTime t₀ q ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_prod, mem_univ, true_and,
      mem_Icc, zoomTime, mem_empty_iff_false, iff_false, not_and]
    intro hp
    obtain ⟨_, h1, h2⟩ := hSb hp
    intro h3
    exact h3 (div_nonneg (by linarith) hq.le) (by rw [div_le_one hq]; linarith)
  rw [this, measure_empty, mul_zero]

/-- **Domination of the zoomed law.** If `μ ≤ K • ν ⊗ dt` and the retained set
lies over `A`, the zoomed law normalized by `q ν(A)` is dominated by `K` times
the conditioned prior and Lebesgue measure. -/
theorem zoomLaw_le {ν : Measure α} [SFinite ν] {μ : Measure (α × ℝ)} {K : ℝ≥0∞}
    (hμ : μ ≤ K • ν.prod volume) {A : Set α} (hA : MeasurableSet A)
    {S : Set (α × ℝ)} (hS : MeasurableSet S) (hSA : S ⊆ A ×ˢ univ)
    {t₀ q : ℝ} (hq : 0 < q) :
    zoomLaw μ S t₀ q (ENNReal.ofReal q * ν A) ≤ K • (condPrior ν A).prod volume := by
  rw [Measure.le_iff]
  intro E hE
  rw [zoomLaw_apply μ hS t₀ q _ hE, Measure.smul_apply, smul_eq_mul]
  -- the retained part is inside `A × ℝ`
  have h1 : μ (S ∩ zoomTime t₀ q ⁻¹' E) ≤
      K * (ν.prod volume) {p | p.1 ∈ A ∧ (id p.1, (p.2 - t₀) / q) ∈ E} := by
    calc μ (S ∩ zoomTime t₀ q ⁻¹' E)
        ≤ μ {p | p.1 ∈ A ∧ (id p.1, (p.2 - t₀) / q) ∈ E} := by
          apply measure_mono
          intro p ⟨hpS, hpE⟩
          exact ⟨(hSA hpS).1, hpE⟩
      _ ≤ (K • ν.prod volume) {p | p.1 ∈ A ∧ (id p.1, (p.2 - t₀) / q) ∈ E} := hμ _
      _ = K * (ν.prod volume) {p | p.1 ∈ A ∧ (id p.1, (p.2 - t₀) / q) ∈ E} := by
          rw [Measure.smul_apply, smul_eq_mul]
  rw [Submission.Lib.K4ChartLifting.prod_lift_apply ν id measurable_id A hA t₀ q hq E hE,
    Measure.map_id] at h1
  -- the conditioned product
  have h2 : ((condPrior ν A).prod volume) E = (ν A)⁻¹ * ((ν.restrict A).prod volume) E := by
    rw [condPrior, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]
  rw [h2]
  have hq0 : ENNReal.ofReal q ≠ 0 := by simp [hq]
  have hqt : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  calc (ENNReal.ofReal q * ν A)⁻¹ * μ (S ∩ zoomTime t₀ q ⁻¹' E)
      ≤ (ENNReal.ofReal q * ν A)⁻¹ *
          (K * (ENNReal.ofReal q * ((ν.restrict A).prod volume) E)) := by gcongr
    _ = K * ((ν A)⁻¹ * ((ν.restrict A).prod volume) E) := by
        rw [ENNReal.mul_inv (Or.inl hq0) (Or.inl hqt)]
        calc (ENNReal.ofReal q)⁻¹ * (ν A)⁻¹ *
              (K * (ENNReal.ofReal q * ((ν.restrict A).prod volume) E))
            = K * ((ν A)⁻¹ * ((ENNReal.ofReal q)⁻¹ * ENNReal.ofReal q) *
                ((ν.restrict A).prod volume) E) := by ring
          _ = K * ((ν A)⁻¹ * ((ν.restrict A).prod volume) E) := by
              rw [ENNReal.inv_mul_cancel hq0 hqt, mul_one]

/-- Almost-everywhere statements transfer to the zoomed law. -/
theorem ae_zoomLaw (μ₀ : Measure (α × ℝ)) {S : Set (α × ℝ)} (hS : MeasurableSet S)
    (t₀ q : ℝ) (W : ℝ≥0∞) {P : α × ℝ → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ z ∂μ₀, z ∈ S → P (zoomTime t₀ q z)) :
    ∀ᵐ z ∂zoomLaw μ₀ S t₀ q W, P z := by
  unfold zoomLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_zoomTime t₀ q).aemeasurable hP, ae_restrict_iff' hS]
  exact h

end

end Submission.Lib.K4ContactTransfer
