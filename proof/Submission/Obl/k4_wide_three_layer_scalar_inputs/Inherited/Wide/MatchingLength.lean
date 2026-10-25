/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Wide/MatchingLength.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
/- Adapted within this LOT tree (g-oai-074) from o218 `k4_horizontal_endpoint_wide_return`,
session x0764, branch x0764, commit bc59dbcc1b4f69bb8941ad6a108ac9183fa22bd8, file
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/MatchingLength.lean (namespace renamed into o250's). -/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Matching length of quadratics with a nonconstant coefficient gap

The one-variable estimate behind "Coefficient agreement at a fine state" in the proof of the
wide-interval proposition (paper `prop:wide-interval`, tex-07): if two quadratics in the
transverse variable `U` differ by `Δ(U) = δ₀ + δ₁ U + δ₂ U²` with nonconstant gap
`|δ₁| + |δ₂| ≥ e`, then

* the derivative `Δ'` is below `θ` only on a set of length `θ (4L+2)/e` of `[-L, L]`
  (`deriv_sublevel_volume`), and
* away from that set, `Δ` meets each of finitely many offsets to width `w` only on a set of
  length `4w/θ` (`offset_match_volume`),

so `Δ` comes within `w` of one of `m` offsets on a set of length at most
`θ (4L+2)/e + 4 m w/θ` (`quadratic_offset_match_volume`). With `θ = e N^-τ`, `m = K N^{du}` and
`w = K a₁` this is the paper's pair of bounds `K N^-τ` and `K N^{du} a₁ N^τ / e`.

Everything here is rate-free; nothing about the horizontal model is used.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Wide

open MeasureTheory Set

/-- A set of reals of diameter at most `r` has Lebesgue measure at most `r`. -/
theorem volume_le_of_forall_abs_sub_le {s : Set ℝ} {r : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, |x - y| ≤ r) : volume s ≤ ENNReal.ofReal r :=
  (Real.volume_le_diam s).trans (Metric.ediam_le_of_forall_dist_le h)

/-- The difference of a quadratic at two points is the gap times the mean derivative. -/
theorem quadratic_sub_eq (δ₀ δ₁ δ₂ x y : ℝ) :
    (δ₀ + δ₁ * y + δ₂ * y ^ 2) - (δ₀ + δ₁ * x + δ₂ * x ^ 2) =
      (y - x) * (((δ₁ + 2 * δ₂ * x) + (δ₁ + 2 * δ₂ * y)) / 2) := by
  ring

/-- Where the derivative of a quadratic is at least `θ` (with one sign), its values meet a
fixed offset to width `w` only on a set of diameter `2w/θ`. -/
theorem offset_match_diam {δ₀ δ₁ δ₂ θ w c : ℝ} (hθ : 0 < θ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {x y : ℝ} (hx : θ ≤ σ * (δ₁ + 2 * δ₂ * x)) (hy : θ ≤ σ * (δ₁ + 2 * δ₂ * y))
    (hxw : |δ₀ + δ₁ * x + δ₂ * x ^ 2 - c| ≤ w) (hyw : |δ₀ + δ₁ * y + δ₂ * y ^ 2 - c| ≤ w) :
    |x - y| ≤ 2 * w / θ := by
  have hmean : θ ≤ σ * (((δ₁ + 2 * δ₂ * x) + (δ₁ + 2 * δ₂ * y)) / 2) := by linarith
  have hdiff : |(δ₀ + δ₁ * y + δ₂ * y ^ 2) - (δ₀ + δ₁ * x + δ₂ * x ^ 2)| ≤ 2 * w := by
    have := abs_sub_le (δ₀ + δ₁ * y + δ₂ * y ^ 2) c (δ₀ + δ₁ * x + δ₂ * x ^ 2)
    rw [abs_sub_comm c] at this
    linarith
  rw [quadratic_sub_eq] at hdiff
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
  have hm : θ ≤ |((δ₁ + 2 * δ₂ * x) + (δ₁ + 2 * δ₂ * y)) / 2| := by
    calc θ ≤ σ * (((δ₁ + 2 * δ₂ * x) + (δ₁ + 2 * δ₂ * y)) / 2) := hmean
      _ ≤ |σ * (((δ₁ + 2 * δ₂ * x) + (δ₁ + 2 * δ₂ * y)) / 2)| := le_abs_self _
      _ = |((δ₁ + 2 * δ₂ * x) + (δ₁ + 2 * δ₂ * y)) / 2| := by rw [abs_mul, hσabs, one_mul]
  rw [abs_mul] at hdiff
  have hxy : |y - x| * θ ≤ 2 * w :=
    (mul_le_mul_of_nonneg_left hm (abs_nonneg _)).trans hdiff
  rw [abs_sub_comm]
  rw [le_div_iff₀ hθ]
  exact hxy

/-- Below the sublevel threshold, a quadratic with a nonconstant gap has small derivative only
on a short set: `|Δ'| < θ` on a subset of `[-L, L]` of length at most `θ (4L+2)/e`. -/
theorem deriv_sublevel_volume {δ₁ δ₂ e θ L : ℝ} (hL : 0 ≤ L) (he : 0 < e)
    (hgap : e ≤ |δ₁| + |δ₂|) (hθ : 0 < θ) (hθe : θ ≤ e / 2) :
    volume {U ∈ Icc (-L) L | |δ₁ + 2 * δ₂ * U| < θ} ≤
      ENNReal.ofReal (θ * (4 * L + 2) / e) := by
  have hpos : 0 < 4 * L + 2 := by linarith
  by_cases hbig : e / (4 * L + 2) ≤ |δ₂|
  · -- the derivative moves at rate `2|δ₂|`, so its `θ`-sublevel set is short
    have hδ₂ : 0 < |δ₂| := lt_of_lt_of_le (div_pos he hpos) hbig
    refine volume_le_of_forall_abs_sub_le ?_
    intro x hx y hy
    have hxy : |2 * δ₂ * (x - y)| < 2 * θ := by
      have h1 := hx.2
      have h2 := hy.2
      have : 2 * δ₂ * (x - y) = (δ₁ + 2 * δ₂ * x) - (δ₁ + 2 * δ₂ * y) := by ring
      rw [this]
      calc |(δ₁ + 2 * δ₂ * x) - (δ₁ + 2 * δ₂ * y)|
          ≤ |δ₁ + 2 * δ₂ * x| + |δ₁ + 2 * δ₂ * y| := abs_sub _ _
        _ < θ + θ := add_lt_add h1 h2
        _ = 2 * θ := by ring
    rw [abs_mul, abs_mul, abs_two] at hxy
    have h3 : |δ₂| * |x - y| < θ := by nlinarith
    have h4 : |x - y| ≤ θ / |δ₂| := by
      rw [le_div_iff₀ hδ₂]; linarith
    calc |x - y| ≤ θ / |δ₂| := h4
      _ ≤ θ / (e / (4 * L + 2)) := div_le_div_of_nonneg_left hθ.le (div_pos he hpos) hbig
      _ = θ * (4 * L + 2) / e := by field_simp
  · -- the linear coefficient dominates on `[-L, L]`, so the sublevel set is empty
    rw [not_le] at hbig
    have hempty : {U ∈ Icc (-L) L | |δ₁ + 2 * δ₂ * U| < θ} = ∅ := by
      ext U
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hU
      have hUL : |U| ≤ L := abs_le.mpr ⟨hU.1, hU.2⟩
      have hδ₂' : (4 * L + 2) * |δ₂| < e := by
        have := (lt_div_iff₀ hpos).mp hbig
        linarith
      have h1 : |2 * δ₂ * U| ≤ 2 * L * |δ₂| := by
        rw [abs_mul, abs_mul, abs_two]
        nlinarith [abs_nonneg δ₂, abs_nonneg U]
      have h2 : |δ₁| - |2 * δ₂ * U| ≤ |δ₁ + 2 * δ₂ * U| := by
        have := abs_add_le (δ₁ + 2 * δ₂ * U) (-(2 * δ₂ * U))
        rw [abs_neg] at this
        have h' : δ₁ + 2 * δ₂ * U + -(2 * δ₂ * U) = δ₁ := by ring
        rw [h'] at this
        linarith
      have h3 : 0 ≤ |δ₂| := abs_nonneg _
      nlinarith
    rw [hempty, measure_empty]
    exact bot_le

/-- Away from the derivative sublevel set, a quadratic meets one offset to width `w` on a set of
length at most `4w/θ`. -/
theorem offset_match_volume {δ₀ δ₁ δ₂ θ w c L : ℝ} (hθ : 0 < θ) (hw : 0 ≤ w) :
    volume {U ∈ Icc (-L) L | θ ≤ |δ₁ + 2 * δ₂ * U| ∧ |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w} ≤
      ENNReal.ofReal (4 * w / θ) := by
  let Sp := {U : ℝ | θ ≤ 1 * (δ₁ + 2 * δ₂ * U) ∧ |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}
  let Sm := {U : ℝ | θ ≤ -1 * (δ₁ + 2 * δ₂ * U) ∧ |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}
  have hsub : {U ∈ Icc (-L) L | θ ≤ |δ₁ + 2 * δ₂ * U| ∧ |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w} ⊆
      Sp ∪ Sm := by
    intro U hU
    obtain ⟨-, hd, hv⟩ := hU
    rcases le_abs'.mp hd with h | h
    · right; exact ⟨by linarith, hv⟩
    · left; exact ⟨by linarith, hv⟩
  have hp : volume Sp ≤ ENNReal.ofReal (2 * w / θ) :=
    volume_le_of_forall_abs_sub_le fun x hx y hy =>
      offset_match_diam hθ 1 (Or.inl rfl) hx.1 hy.1 hx.2 hy.2
  have hm : volume Sm ≤ ENNReal.ofReal (2 * w / θ) :=
    volume_le_of_forall_abs_sub_le fun x hx y hy =>
      offset_match_diam hθ (-1) (Or.inr rfl) hx.1 hy.1 hx.2 hy.2
  calc volume {U ∈ Icc (-L) L | θ ≤ |δ₁ + 2 * δ₂ * U| ∧ |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}
      ≤ volume (Sp ∪ Sm) := measure_mono hsub
    _ ≤ volume Sp + volume Sm := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * w / θ) + ENNReal.ofReal (2 * w / θ) := add_le_add hp hm
    _ = ENNReal.ofReal (4 * w / θ) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring

/-- **Matching length.** A quadratic `Δ(U) = δ₀ + δ₁ U + δ₂ U²` with nonconstant gap
`|δ₁| + |δ₂| ≥ e` comes within `w` of one of the offsets in `O` only on a subset of `[-L, L]`
of length at most `θ (4L+2)/e + 4 |O| w/θ`, for every `0 < θ ≤ e/2`. -/
theorem quadratic_offset_match_volume {δ₀ δ₁ δ₂ e θ w L : ℝ} (O : Finset ℝ)
    (hL : 0 ≤ L) (he : 0 < e) (hgap : e ≤ |δ₁| + |δ₂|) (hθ : 0 < θ) (hθe : θ ≤ e / 2)
    (hw : 0 ≤ w) :
    volume {U ∈ Icc (-L) L | ∃ c ∈ O, |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w} ≤
      ENNReal.ofReal (θ * (4 * L + 2) / e + 4 * O.card * w / θ) := by
  have hsub : {U ∈ Icc (-L) L | ∃ c ∈ O, |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w} ⊆
      {U ∈ Icc (-L) L | |δ₁ + 2 * δ₂ * U| < θ} ∪
        ⋃ c ∈ O, {U ∈ Icc (-L) L | θ ≤ |δ₁ + 2 * δ₂ * U| ∧
          |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w} := by
    intro U ⟨hU, c, hc, hv⟩
    by_cases hd : |δ₁ + 2 * δ₂ * U| < θ
    · left; exact ⟨hU, hd⟩
    · right
      simp only [mem_iUnion, mem_ofPred_eq]
      exact ⟨c, hc, hU, not_lt.mp hd, hv⟩
  have hsum : ∑ c ∈ O, volume {U ∈ Icc (-L) L | θ ≤ |δ₁ + 2 * δ₂ * U| ∧
        |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w} ≤ ENNReal.ofReal (4 * O.card * w / θ) := by
    calc ∑ c ∈ O, volume {U ∈ Icc (-L) L | θ ≤ |δ₁ + 2 * δ₂ * U| ∧
          |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}
        ≤ ∑ _c ∈ O, ENNReal.ofReal (4 * w / θ) :=
          Finset.sum_le_sum fun c _ => offset_match_volume hθ hw
      _ = ENNReal.ofReal (4 * O.card * w / θ) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  calc volume {U ∈ Icc (-L) L | ∃ c ∈ O, |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}
      ≤ volume ({U ∈ Icc (-L) L | |δ₁ + 2 * δ₂ * U| < θ} ∪
        ⋃ c ∈ O, {U ∈ Icc (-L) L | θ ≤ |δ₁ + 2 * δ₂ * U| ∧
          |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}) := measure_mono hsub
    _ ≤ volume {U ∈ Icc (-L) L | |δ₁ + 2 * δ₂ * U| < θ} +
        volume (⋃ c ∈ O, {U ∈ Icc (-L) L | θ ≤ |δ₁ + 2 * δ₂ * U| ∧
          |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ * (4 * L + 2) / e) + ENNReal.ofReal (4 * O.card * w / θ) :=
        add_le_add (deriv_sublevel_volume hL he hgap hθ hθe)
          ((measure_biUnion_finset_le O _).trans hsum)
    _ = ENNReal.ofReal (θ * (4 * L + 2) / e + 4 * O.card * w / θ) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Wide
