import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_remez

open Set Metric

/-- The last parameter of a bounded ray set stays in the same closed ball. -/
theorem exists_ray_endpoint {n : ℕ}
    (x v : EuclideanSpace ℝ (Fin n)) (S : Set ℝ)
    (hS : S.Nonempty) (hSsub : S ⊆ Icc (0 : ℝ) 1)
    (hpos : ∀ t ∈ S, ‖x + t • v‖ ≤ (1 : ℝ) / 2) :
    ∃ T ∈ Icc (0 : ℝ) 1, S ⊆ Icc (0 : ℝ) T ∧
      ‖x + T • v‖ ≤ (1 : ℝ) / 2 := by
  have hclsub : closure S ⊆ Icc (0 : ℝ) 1 := closure_minimal hSsub isClosed_Icc
  have hcompact : IsCompact (closure S) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hclsub
  obtain ⟨T, hT, hmax⟩ := hcompact.exists_isMaxOn hS.closure continuousOn_id
  refine ⟨T, hclsub hT, ?_, ?_⟩
  · intro t ht
    exact ⟨(hSsub ht).1, hmax (subset_closure ht)⟩
  · have hclosed : IsClosed {t : ℝ | ‖x + t • v‖ ≤ (1 : ℝ) / 2} :=
      isClosed_le (by fun_prop) continuous_const
    exact closure_minimal hpos hclosed hT

end Submission.Obl.k4_algebraic_sheet_remez
