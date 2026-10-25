import Mathlib

set_option linter.unusedVariables false

/-!
# An affine velocity graph from a small triple moment

At a fine physical state of Section 6 (paper `a05:velocity-graph`), the lifted directions
`(1, V, X')` of the incidences either span three dimensions with positive probability (then the
state is "bad" and multilinear Kakeya bounds the bad mass, see `IncidenceKakeya.lean`) or their
triple determinant moment is small. In the second case, with breadth of `V`, this file extracts an
affine graph `X' = G₀ + G₁ V` with small `L¹` residual, for an arbitrary finite law `P` of
`(V, X')` (not only a finite family): `exists_line_of_triple_moment`. The determinant of the rows
`(1, a), (1, b), (1, c)` is `triArea a b c`, and the graph is the line through two separated
points `a, b` of any full-measure set (so bounds on the support bound the graph's coefficients).
-/

namespace Submission.Lib.K4ContinuousKakeya

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Twice the signed area of the triangle `a b c` in the plane; equals the determinant of the
rows `(1, a), (1, b), (1, c)`. -/
def triArea (a b c : ℝ × ℝ) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

lemma continuous_triArea : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) =>
    triArea x.1 x.2.1 x.2.2 := by
  unfold triArea; fun_prop

/-- The line through `a` and `b`, as a function of the first coordinate. -/
def lineThrough (a b : ℝ × ℝ) (v : ℝ) : ℝ := a.2 + (b.2 - a.2) / (b.1 - a.1) * (v - a.1)

lemma triArea_eq (a b c : ℝ × ℝ) (h : b.1 ≠ a.1) :
    triArea a b c = (b.1 - a.1) * (c.2 - lineThrough a b c.1) := by
  unfold triArea lineThrough
  have h' : b.1 - a.1 ≠ 0 := sub_ne_zero.mpr h
  field_simp
  ring

/-- **Affine velocity graph from a small triple moment.** If a finite measure on pairs `(V, W)`
puts at most half of its mass in every `δ`-window of `V`, then some pair of points `a, b` of any
full-measure set `Q`, with `|b.1 - a.1| ≥ δ`, spans a line `W = lineThrough a b V` whose `L¹`
residual is at most `2 M₃ / (δ P(univ)^2)`, where `M₃` is the triple moment of the triangle
area. -/
theorem exists_line_of_triple_moment (P : Measure (ℝ × ℝ)) [IsFiniteMeasure P] {δ : ℝ}
    (hδ : 0 < δ) (hP : P univ ≠ 0) (hspread : ∀ v : ℝ, P {q | |q.1 - v| < δ} ≤ P univ / 2)
    (Q : Set (ℝ × ℝ)) (hQ : P Qᶜ = 0) :
    ∃ a ∈ Q, ∃ b ∈ Q, δ ≤ |b.1 - a.1| ∧
      ENNReal.ofReal δ * ∫⁻ c, ENNReal.ofReal |c.2 - lineThrough a b c.1| ∂P ≤
        2 * (∫⁻ a, ∫⁻ b, ∫⁻ c, ENNReal.ofReal |triArea a b c| ∂P ∂P ∂P) / P univ ^ 2 := by
  classical
  set M : ℝ≥0∞ := P univ with hM
  have hMtop : M ≠ ⊤ := measure_ne_top P univ
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {x | δ ≤ |x.2.1 - x.1.1|} with hS
  have hSm : MeasurableSet S := by
    apply measurableSet_le measurable_const
    exact (measurable_snd.fst.sub measurable_fst.fst).abs
  -- separated pairs carry at least half of the product mass
  have hSmass : M * (M / 2) ≤ (P.prod P) S := by
    rw [Measure.prod_apply hSm]
    calc M * (M / 2) = ∫⁻ _a, M / 2 ∂P := by rw [lintegral_const, mul_comm]
      _ ≤ ∫⁻ a, P (Prod.mk a ⁻¹' S) ∂P := by
        apply lintegral_mono
        intro a
        show M / 2 ≤ P (Prod.mk a ⁻¹' S)
        have hcompl : Prod.mk a ⁻¹' S = {q : ℝ × ℝ | |q.1 - a.1| < δ}ᶜ := by
          ext q
          simp [hS, not_lt, abs_sub_comm]
        rw [hcompl, measure_compl (measurableSet_lt (by fun_prop) measurable_const)
          (measure_ne_top _ _)]
        have h1 := hspread a.1
        have h2 : P {q : ℝ × ℝ | |q.1 - a.1| < δ} ≠ ⊤ := measure_ne_top _ _
        calc M / 2 = M - M / 2 := by rw [ENNReal.sub_half hMtop]
          _ ≤ M - P {q : ℝ × ℝ | |q.1 - a.1| < δ} := tsub_le_tsub_left h1 _
  have hSpos : (P.prod P) S ≠ 0 := by
    intro h0
    rw [h0, nonpos_iff_eq_zero] at hSmass
    rcases mul_eq_zero.mp hSmass with h | h
    · exact hP h
    · exact hP (by simpa [ENNReal.div_eq_zero_iff] using h)
  -- the residual moment function of a pair
  set f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun x => ∫⁻ c, ENNReal.ofReal |triArea x.1 x.2 c| ∂P
    with hf
  have hfm : Measurable f := by
    have h : Measurable fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × (ℝ × ℝ) =>
        ENNReal.ofReal |triArea z.1.1 z.1.2 z.2| := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.abs
      exact continuous_triArea.measurable.comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact h.lintegral_prod_right'
  set M₃ : ℝ≥0∞ := ∫⁻ a, ∫⁻ b, ∫⁻ c, ENNReal.ofReal |triArea a b c| ∂P ∂P ∂P with hM₃
  have hfS : ∫⁻ x in S, f x ∂(P.prod P) ≤ M₃ := by
    calc ∫⁻ x in S, f x ∂(P.prod P) ≤ ∫⁻ x, f x ∂(P.prod P) := setLIntegral_le_lintegral _ _
      _ = M₃ := lintegral_prod _ hfm.aemeasurable
  -- first moment method on the separated pairs, avoiding the null complement of `Q × Q`
  set μ : Measure ((ℝ × ℝ) × (ℝ × ℝ)) := (P.prod P).restrict S with hμ
  have hμ0 : μ ≠ 0 := by
    intro h
    apply hSpos
    have := congrArg (fun m : Measure ((ℝ × ℝ) × (ℝ × ℝ)) => m univ) h
    simpa [hμ, Measure.restrict_apply_univ] using this
  have hN : μ (Q ×ˢ Q)ᶜ = 0 := by
    have h0 : (P.prod P) (Q ×ˢ Q)ᶜ = 0 := by
      rw [Set.compl_prod_eq_union]
      apply measure_union_null
      · rw [Measure.prod_prod, hQ, zero_mul]
      · rw [Measure.prod_prod, hQ, mul_zero]
    exact le_antisymm (((Measure.restrict_le_self (μ := P.prod P) (s := S)) _).trans h0.le)
      zero_le
  have hNS : μ Sᶜ = 0 := by
    rw [hμ, Measure.restrict_apply hSm.compl, Set.compl_inter_self, measure_empty]
  obtain ⟨x, hxN, hxle⟩ := exists_notMem_null_le_laverage hμ0 hfm.aemeasurable
    (measure_union_null hN hNS)
  simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hxN
  obtain ⟨hxQ, hxS⟩ := hxN
  refine ⟨x.1, (Set.mem_prod.mp hxQ).1, x.2, (Set.mem_prod.mp hxQ).2, hxS, ?_⟩
  have hsep : δ ≤ |x.2.1 - x.1.1| := hxS
  have hne : x.2.1 ≠ x.1.1 := by
    intro h; rw [h, sub_self, abs_zero] at hsep; linarith
  calc ENNReal.ofReal δ * ∫⁻ c, ENNReal.ofReal |c.2 - lineThrough x.1 x.2 c.1| ∂P
      = ∫⁻ c, ENNReal.ofReal δ * ENNReal.ofReal |c.2 - lineThrough x.1 x.2 c.1| ∂P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ c, ENNReal.ofReal |triArea x.1 x.2 c| ∂P := by
        apply lintegral_mono
        intro c
        show ENNReal.ofReal δ * ENNReal.ofReal |c.2 - lineThrough x.1 x.2 c.1| ≤
          ENNReal.ofReal |triArea x.1 x.2 c|
        rw [← ENNReal.ofReal_mul hδ.le, triArea_eq _ _ _ hne, abs_mul]
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hsep (abs_nonneg _)
    _ = f x := rfl
    _ ≤ ⨍⁻ y, f y ∂μ := hxle
    _ = (∫⁻ y in S, f y ∂(P.prod P)) / (P.prod P) S := by
        rw [laverage_eq, hμ, Measure.restrict_apply_univ]
    _ ≤ M₃ / (M * (M / 2)) := ENNReal.div_le_div hfS hSmass
    _ = 2 * M₃ / M ^ 2 := by
        have h2 : (M / 2)⁻¹ = M⁻¹ * 2 := by
          rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (Or.inl (by simp)), inv_inv,
            mul_comm]
        rw [show M₃ / (M * (M / 2)) = (M * (M / 2))⁻¹ * M₃ from ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl hP) (Or.inl hMtop), h2,
          show 2 * M₃ / M ^ 2 = (M ^ 2)⁻¹ * (2 * M₃) from ENNReal.div_eq_inv_mul,
          ENNReal.inv_pow]
        ring

end

end Submission.Lib.K4ContinuousKakeya
