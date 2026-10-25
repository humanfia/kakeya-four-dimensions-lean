import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedLayers

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- The original short-domain reference budget in the expanded form used
by the final compared table. -/
theorem reference_domain_menus (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (hN : 0 < p.N k)
    (hL : L.Valid p k s m H) (hH : 1 ≤ H)
    (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 < b) (hbβ : b ≤ L.β) (hβg : L.β ≤ g) :
    ∃ D : Fin L.count → Finset (ℤ × ℤ × ℤ),
      (∀ i l, l ∈ L.C i → ∀ t ∈ Icc (0 : ℝ) 1,
        movingDomainCode h g b (p.b k l 1) (p.b k l 4) t ∈ D i) ∧
      (∑ i, ∑ _q ∈ D i,
        ENNReal.ofReal (h * p.N k ^ (-m) * b * (p.N k ^ (-s)) ^ p.d) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = L.tag i 0}) ≤
        ENNReal.ofReal (240 * H ^ 3) := by
  obtain ⟨D, hD, hbudget⟩ := L.domain_menus p hL hH hh hh1 hb hbβ hβg
  refine ⟨D, hD, ?_⟩
  convert hbudget using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, nsmul_eq_mul, ProjectedLayer.unscaledWeight]
  congr 1
  have heq : h * p.N k ^ (-m) * b * (p.N k ^ (-s)) ^ p.d =
      (h * b) * (p.N k ^ (-m) * (p.N k ^ (-s)) ^ p.d) := by ring
  rw [heq, ENNReal.ofReal_mul (mul_nonneg hh.le hb.le), mul_assoc]

end ProjectedLayer
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
