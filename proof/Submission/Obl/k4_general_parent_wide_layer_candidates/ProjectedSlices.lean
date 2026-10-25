import Submission.Obl.k4_general_parent_wide_layer_candidates.ProjectedSlicing
import Submission.Obl.k4_general_parent_wide_layer_candidates.DomainCoordinates

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def comparisonCode (k : ℕ) (m h g b : ℝ) (ω : α × ℝ) :
    (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) :=
  (![⌊p.b k ω.1 3 / p.N k ^ (-m)⌋, ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋],
    p.domainCode k h g b ω)

theorem measurable_comparisonCode (hbase : p.Basic) (k : ℕ) (m h g b : ℝ) :
    Measurable (p.comparisonCode k m h g b) := by
  have hb := (hbase k).1
  have hcode := p.measurable_domainCode hbase k h g b
  unfold comparisonCode
  fun_prop

end Parent

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

def slicedEvent (L : ProjectedLayer α) (p : Parent α) (k : ℕ) (h g b : ℝ)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ)) (e : SliceIndex D) : Set (α × ℝ) :=
  sliceEvent D (fun i => L.C i ×ˢ Icc (0 : ℝ) 1) (p.domainCode k h g b) e

def slicedWeight (L : ProjectedLayer α) (p : Parent α) (k : ℕ) (s m h b : ℝ)
    (i : Fin L.count) : ℝ :=
  (ENNReal.ofReal (h * b) * L.unscaledWeight p k s m i).toReal

/-- Actual common-domain source slices, with their original measurable
assignments and the entire real reference budget. -/
theorem exists_disjoint_slices (L : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H) (hH : 1 ≤ H)
    (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 < b) (hbβ : b ≤ L.β) (hβg : L.β ≤ g)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.ρ k) (hcover : L.Covers σ) :
    ∃ D : Fin L.count → Finset (ℤ × ℤ × ℤ),
      (∀ e, MeasurableSet (L.slicedEvent p k h g b D e)) ∧
      Pairwise (fun e f => Disjoint (L.slicedEvent p k h g b D e) (L.slicedEvent p k h g b D f)) ∧
      (∀ᵐ ω ∂σ, ∃ e, ω ∈ L.slicedEvent p k h g b D e) ∧
      (∑ e : SliceIndex D, L.slicedWeight p k s m h b e.1) ≤ 240 * H ^ 3 := by
  classical
  obtain ⟨D, hD, hbudget⟩ := L.domain_menus p hL hH hh hh1 hb hbβ hβg
  let E (i : Fin L.count) : Set (α × ℝ) := L.C i ×ˢ Icc (0 : ℝ) 1
  have hE (i : Fin L.count) : MeasurableSet (E i) :=
    ((hL.2.2.2.1 i).prod measurableSet_Icc)
  have hdisj : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hω hω'
    exact Set.disjoint_left.mp (hL.2.2.2.2.1 i j hij) hω.1 hω'.1
  have hunit : ∀ᵐ ω ∂σ, ω.2 ∈ Icc (0 : ℝ) 1 := by
    have hunitμ : ∀ᵐ ω ∂p.μ k, ω.2 ∈ Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      have heq : {ω : α × ℝ | ω.2 ∉ Icc (0 : ℝ) 1} = (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
        ext ω
        simp
      rw [heq]
      exact (hbase k).2.2.2.2.2.1
    exact hunitμ.filter_mono (ae_mono (hσ.trans (hbase k).2.2.2.2.1))
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · exact measurableSet_sliceEvent D E hE _ (p.measurable_domainCode hbase k h g b)
  · exact sliceEvent_disjoint D E hdisj _
  · apply sliceEvent_cover σ D E (p.domainCode k h g b)
    · filter_upwards [hcover, hunit] with ω hc ht
      obtain ⟨i, hi⟩ := hc
      exact ⟨i, hi, ht⟩
    · intro i ω hω
      exact hD i ω.1 hω.1 ω.2 hω.2
  · letI := (hbase k).2.2.1
    let W (i : Fin L.count) : ℝ≥0∞ :=
      ENNReal.ofReal (h * b) * L.unscaledWeight p k s m i
    have hW (i : Fin L.count) : W i ≠ ⊤ := by
      dsimp [W, unscaledWeight]
      finiteness
    have hsum : ENNReal.ofReal (∑ e : SliceIndex D, (W e.1).toReal) =
        ∑ e : SliceIndex D, W e.1 := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
      apply Finset.sum_congr rfl
      intro e _
      exact ENNReal.ofReal_toReal (hW e.1)
    have he := (slice_reference_sum D W).trans_le hbudget
    rw [← hsum] at he
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 240 * H ^ 3)).mp he

/-- Every sliced source still has its literal original bins and domain. -/
theorem slicedEvent_code (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ)) (e : SliceIndex D)
    {ω : α × ℝ} (hω : ω ∈ L.slicedEvent p k h g b D e) :
    p.comparisonCode k m h g b ω = (L.tag e.1, e.2.val) := by
  have hmem := (hL.2.2.2.2.2.1 e.1).2.2.2.1 ω.1 hω.1.1
  apply Prod.ext
  · ext i
    fin_cases i
    · exact hmem.1
    · exact hmem.2.1
  · exact hω.2

/-- Slicing never weakens the original native predictor fit. -/
theorem slicedEvent_fit (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ)) (e : SliceIndex D)
    {ω : α × ℝ} (hω : ω ∈ L.slicedEvent p k h g b D e) :
    |MvPolynomial.eval (p.x k ω.1 ω.2) (p.P k) -
      MvPolynomial.eval ![ω.2, (p.x k ω.1 ω.2) 2] (L.G e.1)| ≤ H * p.N k ^ (-s) :=
  ((hL.2.2.2.2.2.1 e.1).2.2.2.1 ω.1 hω.1.1).2.2 ω.2 hω.1.2 |>.2

end ProjectedLayer
end
end Submission.Obl.k4_general_parent_wide_layer_candidates
