import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepStruct

/-! Coverage is preserved when the native pairs are embedded in compatible frames. -/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepData

open MeasureTheory Set MvPolynomial
open scoped ENNReal BigOperators

variable {D : PrepData} {N : ℝ} {M₀ D₀ : ℕ} {L : ℝ}
    {E : Fin D.W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}

/-- A native pair has a witness entry in its source's common frame. -/
theorem Hyp.native_pair_mem (h : D.Hyp N M₀ D₀ L E)
    {b b' : Fin D.C} {p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)}
    (hcompat : D.src b ∈ D.compat b')
    (hp : (p.1, p.2.1) ∈ D.Sb b)
    (hp' : (p.1, p.2.2) ∈ D.Sb b')
    (hGood : (p.1, p.2.1) ∈ D.Good (D.γ b))
    (hder : D.dfl * D.B (D.γ b) ≤
      |eval (x p.1 p.2.1) (pderiv 3 (D.R b'))|) :
    ∃ s', p ∈ D.H (D.srcEnt b) s' := by
  have hc : D.key (D.srcIdx b) ∈ D.compat b' := by
    rw [D.key_srcIdx]
    exact hcompat
  refine ⟨D.entOf b' (D.srcIdx b) hc, ?_⟩
  have hJ : coarseIdx (D.j b) = coarseIdx (D.j b') :=
    (D.compat_world_block hcompat).2
  have ht : p.2.2 ∈ D.blk (D.fj (D.srcIdx b)) := by
    rw [fj_of_src (D.key_srcIdx b), hJ]
    exact old_sub_blk _ (h.sel b' hp'.1).2.2.1
  change D.key (D.frame (D.srcEnt b)) = D.src (D.chartOf (D.srcEnt b)) ∧ _
  simp only [D.frame_srcEnt, D.chartOf_srcEnt, D.chartOf_entOf, D.frame_entOf]
  exact ⟨D.key_srcIdx b, trivial, hp, ht, hp', hGood, hder⟩

/-- Injective source entries retain the weighted pair coverage under the original laws. -/
theorem native_coverage_le
    (ν : Fin D.W → Measure (ℕ × (Fin 6 → ℝ))) (ω : Fin D.W → ℝ)
    (H₀ : Fin D.C → Fin D.C → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)))
    (hcover : ∀ b p, (∃ b', p ∈ H₀ b b') → ∃ s', p ∈ D.H (D.srcEnt b) s') :
    (∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
      ((ν (D.γ b)).prod (volume.prod volume)) {p | ∃ b', p ∈ H₀ b b'}) ≤
    ∑ s, ENNReal.ofReal (ω (D.fγ (D.frame s)) * (2 : ℝ) ^ D.T) *
      ((ν (D.fγ (D.frame s))).prod (volume.prod volume)) {p | ∃ s', p ∈ D.H s s'} := by
  classical
  apply Finset.sum_le_sum_of_injOn D.srcEnt
    (fun _ _ _ _ heq => D.srcEnt_injective heq) (Finset.subset_univ _)
  · intro b _
    have hw : D.fγ (D.frame (D.srcEnt b)) = D.γ b := by
      rw [D.frame_world, D.chartOf_srcEnt]
    rw [hw]
    exact mul_le_mul' le_rfl (measure_mono (hcover b))
  · intro s _ _
    exact bot_le

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepData
