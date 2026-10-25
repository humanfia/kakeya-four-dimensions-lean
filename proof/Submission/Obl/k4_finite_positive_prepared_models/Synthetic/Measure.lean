import Mathlib

/-!
# The probability space of the synthetic model

The synthetic stage model draws a hidden index `i` uniformly from `{0, …, M-1}`, a fine hidden
part `u₂`, a position `b₀`, a slope seed `u₃` and a transverse position `b₁`, all uniform on
`[0,1]` and independent. `Ω = (ℕ × ℝ) × ((ℝ × ℝ) × ℝ)` groups the coupled coordinates
`(i, u₂)` and `(b₀, u₃)`, so that every event used later is a product of sections. Written by
x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

/-- The uniform probability on `[0,1]`. -/
abbrev U : Measure ℝ := volume.restrict (Icc 0 1)

scoped instance : IsProbabilityMeasure U := ⟨by simp [U]⟩

theorem U_le_volume (s : Set ℝ) : U s ≤ volume s := Measure.restrict_apply_le _ _

/-- The uniform probability on `{0, …, M-1}`. -/
def idx (M : ℕ) : Measure ℕ := ((M : ENNReal)⁻¹) • Measure.count.restrict (Iio M)

theorem idx_apply (M : ℕ) (A : Set ℕ) :
    idx M A = (M : ENNReal)⁻¹ * ((A ∩ Iio M).encard : ENNReal) := by
  rw [idx, Measure.smul_apply, Measure.restrict_apply (MeasurableSet.of_discrete),
    Measure.count_apply (MeasurableSet.of_discrete), smul_eq_mul]

theorem idx_isProb (M : ℕ) (hM : 0 < M) : IsProbabilityMeasure (idx M) := by
  constructor
  rw [idx_apply, univ_inter]
  have : (Iio M).encard = M := by
    rw [Set.encard_eq_coe_toFinset_card]
    simp
  rw [this]
  push_cast
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hM.ne') (by simp)

/-- An index set of at most `c` elements below `M` has mass at most `c / M`. -/
theorem idx_le_of_card (M : ℕ) (A : Set ℕ) (c : ℕ) (hA : (A ∩ Iio M).encard ≤ c) :
    idx M A ≤ (M : ENNReal)⁻¹ * c := by
  rw [idx_apply]
  gcongr
  exact_mod_cast hA

/-- The sample space. -/
abbrev Ω := (ℕ × ℝ) × ((ℝ × ℝ) × ℝ)

/-- The law of a sample. -/
def P (M : ℕ) : Measure Ω := ((idx M).prod U).prod ((U.prod U).prod U)

theorem P_isProb (M : ℕ) (hM : 0 < M) : IsProbabilityMeasure (P M) := by
  have := idx_isProb M hM
  unfold P
  infer_instance

theorem P_prod_prod (M : ℕ) (A₁ : Set (ℕ × ℝ)) (A₂ : Set (ℝ × ℝ)) (A₃ : Set ℝ) :
    P M (A₁ ×ˢ (A₂ ×ˢ A₃)) = ((idx M).prod U) A₁ * ((U.prod U) A₂ * U A₃) := by
  rw [P, Measure.prod_prod, Measure.prod_prod]

theorem P_mono_prod (M : ℕ) {S : Set Ω} {A₁ : Set (ℕ × ℝ)} {A₂ : Set (ℝ × ℝ)} {A₃ : Set ℝ}
    (h : S ⊆ A₁ ×ˢ (A₂ ×ˢ A₃)) :
    P M S ≤ ((idx M).prod U) A₁ * ((U.prod U) A₂ * U A₃) :=
  (measure_mono h).trans_eq (P_prod_prod M A₁ A₂ A₃)

/-- The embedding of samples as lines: `(i, (b₀, b₁, u₂, u₃, 0, 0))`. -/
def emb (ω : Ω) : ℕ × (Fin 6 → ℝ) :=
  (ω.1.1, ![ω.2.1.1, ω.2.2, ω.1.2, ω.2.1.2, 0, 0])

theorem measurable_emb : Measurable emb := by
  unfold emb
  refine Measurable.prodMk (measurable_fst.comp measurable_fst) ?_
  refine measurable_pi_iff.mpr fun j => ?_
  fin_cases j <;> simp <;> fun_prop

@[simp] theorem emb_fst (ω : Ω) : (emb ω).1 = ω.1.1 := rfl
@[simp] theorem emb_snd0 (ω : Ω) : (emb ω).2 0 = ω.2.1.1 := rfl
@[simp] theorem emb_snd1 (ω : Ω) : (emb ω).2 1 = ω.2.2 := rfl
@[simp] theorem emb_snd2 (ω : Ω) : (emb ω).2 2 = ω.1.2 := rfl
@[simp] theorem emb_snd3 (ω : Ω) : (emb ω).2 3 = ω.2.1.2 := rfl

/-- The section of a two-dimensional event at a fixed slope seed, in the position variable. -/
theorem UU_apply_le (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) (c : ENNReal)
    (W : Set ℝ) (hsec : ∀ u ∈ W, U {b | (b, u) ∈ A} ≤ c)
    (hout : ∀ u, u ∉ W → {b | (b, u) ∈ A} = ∅) (hW : MeasurableSet W) :
    (U.prod U) A ≤ c * U W := by
  rw [Measure.prod_apply_symm hA]
  calc ∫⁻ u, U ((fun b => (b, u)) ⁻¹' A) ∂U
      ≤ ∫⁻ u, W.indicator (fun _ => c) u ∂U := by
        refine lintegral_mono fun u => ?_
        by_cases hu : u ∈ W
        · rw [indicator_of_mem hu]; exact hsec u hu
        · rw [indicator_of_notMem hu]
          have : (fun b => (b, u)) ⁻¹' A = ∅ := hout u hu
          rw [this, measure_empty]
    _ = c * U W := lintegral_indicator_const hW c

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
