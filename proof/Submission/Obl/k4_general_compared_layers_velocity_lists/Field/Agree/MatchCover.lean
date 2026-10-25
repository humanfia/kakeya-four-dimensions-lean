-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.MatchCover; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254, session x0900; the diameter bounds adapt `deriv_sublevel_volume`/`offset_match_diam` of Field/Kernels/MatchingLength.lean (ported from o247/x0870, itself from o218/x0764). -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Kernels.CoefficientAgreement

set_option autoImplicit false

/-!
# Matching sets under interval-capped measures

A measure `μ` restricted to `A` and pushed along `f : Ω → ℝ` may not have a bounded density at
all scales; it is only assumed interval-capped: `μ (A ∩ f ⁻¹' [a, b]) ≤ W (b - a + λ)`.
The matching set of two quadratics with a nonconstant coefficient gap `≥ e` is covered by one
derivative sublevel set of diameter `≤ θ (4L+2)/e` and `2 |O|` monotone pieces of diameter
`≤ 2w/θ` (`deriv_sublevel_volume`, `offset_match_diam`), so its mass is at most
`W (2θ(4L+2)/e + 8 |O| w/θ + (2|O|+1) λ)`: the thickening `λ` is paid once per piece.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels

open MeasureTheory Set
open scoped ENNReal

/-- The matching set is measurable: a closed interval meets finitely many closed sublevel
sets. -/
theorem agree_measurableSet_matchSet (P Q : Fin 3 → ℝ) (O : Finset ℝ) (w L : ℝ) :
    MeasurableSet (matchSet P Q O w L) := by
  have h : matchSet P Q O w L = Icc (-L) L ∩ ⋃ c ∈ O,
      {U : ℝ | |(P 0 + P 1 * U + P 2 * U ^ 2) - (Q 0 + Q 1 * U + Q 2 * U ^ 2) - c| ≤ w} := by
    ext U
    constructor
    · rintro ⟨hU, c, hc, hv⟩
      exact ⟨hU, mem_iUnion₂.mpr ⟨c, hc, hv⟩⟩
    · rintro ⟨hU, h⟩
      obtain ⟨c, hc, hv⟩ := mem_iUnion₂.mp h
      exact ⟨hU, c, hc, hv⟩
  rw [h]
  refine measurableSet_Icc.inter (Finset.measurableSet_biUnion O fun c _ => ?_)
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- A set of reals whose points are pairwise within `D` has interval-capped mass at most
`W (2 D + λ)`: it lies in an interval of length `2 D` around any of its points. -/
theorem agree_measure_inter_preimage_le_of_diam {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Set Ω) (f : Ω → ℝ) (W : ℝ≥0∞) {lam : ℝ}
    (hcap : ∀ a b : ℝ, a ≤ b → μ (A ∩ f ⁻¹' Icc a b) ≤ W * ENNReal.ofReal (b - a + lam))
    {S : Set ℝ} {D : ℝ} (hS : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ D) :
    μ (A ∩ f ⁻¹' S) ≤ W * ENNReal.ofReal (2 * D + lam) := by
  rcases S.eq_empty_or_nonempty with hempty | ⟨x, hx⟩
  · rw [hempty, preimage_empty, inter_empty, measure_empty]
    exact zero_le
  · have hD : 0 ≤ D := by simpa using hS x hx x hx
    have hsub : S ⊆ Icc (x - D) (x + D) := by
      intro y hy
      have h := abs_le.mp (hS x hx y hy)
      constructor <;> linarith [h.1, h.2]
    calc μ (A ∩ f ⁻¹' S) ≤ μ (A ∩ f ⁻¹' Icc (x - D) (x + D)) :=
          measure_mono (inter_subset_inter_right _ (preimage_mono hsub))
      _ ≤ W * ENNReal.ofReal ((x + D) - (x - D) + lam) := hcap _ _ (by linarith)
      _ = W * ENNReal.ofReal (2 * D + lam) := by
          congr 2
          ring

/-- **Derivative sublevel set, diameter form.** If a quadratic has nonconstant gap
`|δ₁| + |δ₂| ≥ e`, any two points of `[-L, L]` where its derivative is below `θ` are within
`θ (4L+2)/e` (the set is even empty when `|δ₂|` is small). -/
theorem agree_sublevel_abs_sub_le {δ₁ δ₂ e θ L : ℝ} (hL : 0 ≤ L) (he : 0 < e)
    (hgap : e ≤ |δ₁| + |δ₂|) (hθ : 0 < θ) (hθe : θ ≤ e / 2) :
    ∀ x ∈ {U ∈ Icc (-L) L | |δ₁ + 2 * δ₂ * U| < θ},
      ∀ y ∈ {U ∈ Icc (-L) L | |δ₁ + 2 * δ₂ * U| < θ}, |x - y| ≤ θ * (4 * L + 2) / e := by
  have hpos : 0 < 4 * L + 2 := by linarith
  intro x hx y hy
  obtain ⟨hxL, hxθ⟩ := hx
  obtain ⟨hyL, hyθ⟩ := hy
  by_cases hbig : e / (4 * L + 2) ≤ |δ₂|
  · -- the derivative moves at rate `2|δ₂|`, so its `θ`-sublevel set is short
    have hδ₂ : 0 < |δ₂| := lt_of_lt_of_le (div_pos he hpos) hbig
    have hxy : |2 * δ₂ * (x - y)| < 2 * θ := by
      have : 2 * δ₂ * (x - y) = (δ₁ + 2 * δ₂ * x) - (δ₁ + 2 * δ₂ * y) := by ring
      rw [this]
      calc |(δ₁ + 2 * δ₂ * x) - (δ₁ + 2 * δ₂ * y)|
          ≤ |δ₁ + 2 * δ₂ * x| + |δ₁ + 2 * δ₂ * y| := abs_sub _ _
        _ < θ + θ := add_lt_add hxθ hyθ
        _ = 2 * θ := by ring
    rw [abs_mul, abs_mul, abs_two] at hxy
    have h3 : |δ₂| * |x - y| < θ := by nlinarith
    have h4 : |x - y| ≤ θ / |δ₂| := by
      rw [le_div_iff₀ hδ₂]; linarith
    calc |x - y| ≤ θ / |δ₂| := h4
      _ ≤ θ / (e / (4 * L + 2)) := div_le_div_of_nonneg_left hθ.le (div_pos he hpos) hbig
      _ = θ * (4 * L + 2) / e := by field_simp
  · -- the linear coefficient dominates on `[-L, L]`, so the sublevel set is empty
    exfalso
    rw [not_le] at hbig
    have hUL : |x| ≤ L := abs_le.mpr ⟨hxL.1, hxL.2⟩
    have hδ₂' : (4 * L + 2) * |δ₂| < e := by
      have := (lt_div_iff₀ hpos).mp hbig
      linarith
    have h1 : |2 * δ₂ * x| ≤ 2 * L * |δ₂| := by
      rw [abs_mul, abs_mul, abs_two]
      nlinarith [abs_nonneg δ₂, abs_nonneg x]
    have h2 : |δ₁| - |2 * δ₂ * x| ≤ |δ₁ + 2 * δ₂ * x| := by
      have := abs_add_le (δ₁ + 2 * δ₂ * x) (-(2 * δ₂ * x))
      rw [abs_neg] at this
      have h' : δ₁ + 2 * δ₂ * x + -(2 * δ₂ * x) = δ₁ := by ring
      rw [h'] at this
      linarith
    have h3 : 0 ≤ |δ₂| := abs_nonneg _
    nlinarith

/-- **Matching sets under interval-capped measures.** If `μ (A ∩ f ⁻¹' [a, b]) ≤ W (b - a + λ)`
for all `a ≤ b`, the incidences of `A` whose coordinate `f` lies in the matching set of two
quadratics with nonconstant gap `≥ e` have mass at most
`W (2θ(4L+2)/e + 8 |O| w/θ + (2|O|+1) λ)`, for every `0 < θ ≤ e/2`. -/
theorem agree_measure_inter_preimage_matchSet_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Set Ω) (f : Ω → ℝ) (W : ℝ≥0∞) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcap : ∀ a b : ℝ, a ≤ b → μ (A ∩ f ⁻¹' Icc a b) ≤ W * ENNReal.ofReal (b - a + lam))
    {P Q : Fin 3 → ℝ} {O : Finset ℝ} {w L e θ : ℝ} (hL : 0 ≤ L) (he : 0 < e)
    (hgap : e ≤ coeffGap P Q) (hθ : 0 < θ) (hθe : θ ≤ e / 2) (hw : 0 ≤ w) :
    μ (A ∩ f ⁻¹' matchSet P Q O w L) ≤
      W * ENNReal.ofReal (2 * θ * (4 * L + 2) / e + 8 * O.card * w / θ +
        (2 * O.card + 1) * lam) := by
  obtain ⟨δ₀, hδ₀⟩ : ∃ x : ℝ, x = P 0 - Q 0 := ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁⟩ : ∃ x : ℝ, x = P 1 - Q 1 := ⟨_, rfl⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ x : ℝ, x = P 2 - Q 2 := ⟨_, rfl⟩
  have hgap' : e ≤ |δ₁| + |δ₂| := by
    rw [hδ₁, hδ₂]
    exact hgap
  let S₀ : Set ℝ := {U ∈ Icc (-L) L | |δ₁ + 2 * δ₂ * U| < θ}
  let Sp : ℝ → Set ℝ := fun c =>
    {U : ℝ | θ ≤ 1 * (δ₁ + 2 * δ₂ * U) ∧ |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}
  let Sm : ℝ → Set ℝ := fun c =>
    {U : ℝ | θ ≤ -1 * (δ₁ + 2 * δ₂ * U) ∧ |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}
  -- the cover of the matching set
  have hcover : ∀ U ∈ matchSet P Q O w L, U ∈ S₀ ∨ ∃ c ∈ O, U ∈ Sp c ∨ U ∈ Sm c := by
    rintro U ⟨hU, c, hc, hv⟩
    have hv' : |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w := by
      have heq : δ₀ + δ₁ * U + δ₂ * U ^ 2 - c =
          (P 0 + P 1 * U + P 2 * U ^ 2) - (Q 0 + Q 1 * U + Q 2 * U ^ 2) - c := by
        rw [hδ₀, hδ₁, hδ₂]
        ring
      rw [heq]
      exact hv
    by_cases hd : |δ₁ + 2 * δ₂ * U| < θ
    · exact Or.inl ⟨hU, hd⟩
    · right
      refine ⟨c, hc, ?_⟩
      rcases le_abs'.mp (not_lt.mp hd) with h | h
      · right
        exact ⟨by linarith, hv'⟩
      · left
        exact ⟨by linarith, hv'⟩
  -- the masses of the pieces
  have h0 : μ (A ∩ f ⁻¹' S₀) ≤ W * ENNReal.ofReal (2 * (θ * (4 * L + 2) / e) + lam) :=
    agree_measure_inter_preimage_le_of_diam μ A f W hcap (agree_sublevel_abs_sub_le hL he hgap' hθ hθe)
  have hp : ∀ c, μ (A ∩ f ⁻¹' Sp c) ≤ W * ENNReal.ofReal (2 * (2 * w / θ) + lam) := by
    intro c
    refine agree_measure_inter_preimage_le_of_diam μ A f W hcap ?_
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
    exact offset_match_diam hθ 1 (Or.inl rfl) hx1 hy1 hx2 hy2
  have hm : ∀ c, μ (A ∩ f ⁻¹' Sm c) ≤ W * ENNReal.ofReal (2 * (2 * w / θ) + lam) := by
    intro c
    refine agree_measure_inter_preimage_le_of_diam μ A f W hcap ?_
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
    exact offset_match_diam hθ (-1) (Or.inr rfl) hx1 hy1 hx2 hy2
  have ha : 0 ≤ 2 * (θ * (4 * L + 2) / e) + lam := by
    have : 0 ≤ θ * (4 * L + 2) / e := div_nonneg (mul_nonneg hθ.le (by linarith)) he.le
    linarith
  have hb : 0 ≤ 2 * (2 * w / θ) + lam := by
    have : 0 ≤ 2 * w / θ := div_nonneg (by linarith) hθ.le
    linarith
  calc μ (A ∩ f ⁻¹' matchSet P Q O w L)
      ≤ μ ((A ∩ f ⁻¹' S₀) ∪ ⋃ c ∈ O, ((A ∩ f ⁻¹' Sp c) ∪ (A ∩ f ⁻¹' Sm c))) := by
        apply measure_mono
        rintro ω ⟨hωA, hωf⟩
        rcases hcover (f ω) hωf with h | ⟨c, hc, h⟩
        · exact Or.inl ⟨hωA, h⟩
        · right
          refine mem_iUnion₂.mpr ⟨c, hc, ?_⟩
          rcases h with h | h
          · exact Or.inl ⟨hωA, h⟩
          · exact Or.inr ⟨hωA, h⟩
    _ ≤ μ (A ∩ f ⁻¹' S₀) + μ (⋃ c ∈ O, ((A ∩ f ⁻¹' Sp c) ∪ (A ∩ f ⁻¹' Sm c))) :=
        measure_union_le _ _
    _ ≤ μ (A ∩ f ⁻¹' S₀) + ∑ c ∈ O, μ ((A ∩ f ⁻¹' Sp c) ∪ (A ∩ f ⁻¹' Sm c)) :=
        add_le_add le_rfl (measure_biUnion_finset_le O _)
    _ ≤ μ (A ∩ f ⁻¹' S₀) + ∑ c ∈ O, (μ (A ∩ f ⁻¹' Sp c) + μ (A ∩ f ⁻¹' Sm c)) :=
        add_le_add le_rfl (Finset.sum_le_sum fun c _ => measure_union_le _ _)
    _ ≤ W * ENNReal.ofReal (2 * (θ * (4 * L + 2) / e) + lam) +
        ∑ c ∈ O, (W * ENNReal.ofReal (2 * (2 * w / θ) + lam) +
          W * ENNReal.ofReal (2 * (2 * w / θ) + lam)) :=
        add_le_add h0 (Finset.sum_le_sum fun c _ => add_le_add (hp c) (hm c))
    _ = W * (ENNReal.ofReal (2 * (θ * (4 * L + 2) / e) + lam) +
        (O.card : ℝ≥0∞) * (ENNReal.ofReal (2 * (2 * w / θ) + lam) +
          ENNReal.ofReal (2 * (2 * w / θ) + lam))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ = W * ENNReal.ofReal (2 * θ * (4 * L + 2) / e + 8 * O.card * w / θ +
        (2 * O.card + 1) * lam) := by
        congr 1
        rw [← ENNReal.ofReal_add hb hb, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add ha (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hb hb))]
        congr 1
        ring

end Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels
