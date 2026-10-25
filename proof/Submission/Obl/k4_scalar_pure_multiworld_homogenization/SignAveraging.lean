import Submission.Obl.k4_native_base_flattening.PolynomialAveraging

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction

/-- The imported averaging estimate also applies to the three-valued signs in
the frozen format. Each sign is specified by the two tests `p ≤ 0` and `-p ≤ 0`. -/
theorem partial_polynomial_sign_averaging {n : ℕ} {ι : Type*} [Fintype ι]
    (B T : ℝ) (D : ℕ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) B)
    (hf : ∀ x, 0 ≤ f.val x) (hs : supportedInCube f.val T)
    (L : List (Fin (n + 1)))
    (p : Fin (n + 1) → (Fin n → ℝ) → ι → Polynomial ℝ)
    (hdepend : ∀ i ∈ L, ∀ y t t',
      (∀ j, SignType.sign ((p i y j).eval t) = SignType.sign ((p i y j).eval t')) →
        f.val (i.insertNth t y) = f.val (i.insertNth t' y))
    (hdegree : ∀ i ∈ L, ∀ y, ∑ j, (p i y j).natDegree ≤ D)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : boundedMeasurableFunctions (Fin (n + 1) → ℝ) B,
      (∀ x, 0 ≤ g.val x) ∧
      (∫⁻ x, ENNReal.ofReal (g.val x)) = (∫⁻ x, ENNReal.ofReal (f.val x)) ∧
      (∀ x y, (∀ i ∉ L, x i = y i) →
        (∀ i ∈ L, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g.val x = g.val y) ∧
      supportedInCube g.val (T + (L.length : ℝ) * ρ) ∧
      densityL1Distance volume g.val f.val ≤
        ENNReal.ofReal ((L.length : ℝ) * (4 * B * (2 * D : ℕ) * ρ) * (2 * T) ^ n) := by
  let q i y : ι ⊕ ι → Polynomial ℝ :=
    Sum.elim (p i y) (fun j => -p i y j)
  apply Submission.Obl.k4_native_base_flattening.partial_polynomial_averaging
    B T (2 * D) hB hT f hf hs L q _ _ hρ
  · intro i hi y t t' h
    apply hdepend i hi y t t'
    intro j
    have hnonpos : (p i y j).eval t ≤ 0 ↔ (p i y j).eval t' ≤ 0 := h (.inl j)
    have hnonneg : 0 ≤ (p i y j).eval t ↔ 0 ≤ (p i y j).eval t' := by
      simpa only [q, Sum.elim_inr, Polynomial.eval_neg, neg_nonpos] using h (.inr j)
    have hpos : 0 < (p i y j).eval t ↔ 0 < (p i y j).eval t' := by
      simpa only [not_le] using not_congr hnonpos
    have hneg : (p i y j).eval t < 0 ↔ (p i y j).eval t' < 0 := by
      simpa only [not_le] using not_congr hnonneg
    change (if 0 < (p i y j).eval t then (1 : SignType) else
      if (p i y j).eval t < 0 then -1 else 0) = _
    simp only [hpos, hneg]
    rfl
  · intro i hi y
    have := hdegree i hi y
    simp only [q, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Polynomial.natDegree_neg]
    omega

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
