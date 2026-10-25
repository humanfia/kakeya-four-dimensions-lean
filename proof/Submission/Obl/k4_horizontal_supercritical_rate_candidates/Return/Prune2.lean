import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Prune
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Good

/-!
# Pruning with disjoint entries; label budgets

With pairwise disjoint entries, a kept point's entry survives the pruning whole. Labels of one
family have total weight `Σ q ν(A) ≤ 1`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A heavy, non-null entry survives whole when entries do not overlap. -/
theorem subset_pruned_of_heavy {X ι : Type*} [MeasurableSpace X] {m : Measure X} {G : Set X}
    {E : ι → Set X} {R : ι → ℝ≥0∞} {K₁ : ℝ≥0∞}
    (huniq : ∀ x e e', x ∈ E e → x ∈ E e' → e = e') (hEG : ∀ e, E e ⊆ G) {e : ι}
    (hheavy : R e / K₁ ≤ m (E e)) (hnz : m (E e) ≠ 0) : E e ⊆ pruned m G E R K₁ := by
  intro x hx
  refine ⟨hEG e hx, ?_⟩
  rintro (h | h)
  · obtain ⟨e', he', hxe'⟩ := Set.mem_iUnion₂.mp h
    rw [huniq x e e' hx hxe'] at hheavy
    exact absurd he' (not_lt.mpr hheavy)
  · obtain ⟨e', he', hxe'⟩ := Set.mem_iUnion₂.mp h
    rw [huniq x e e' hx hxe'] at hnz
    exact hnz he'

/-- The entry of a kept point survives whole. -/
theorem entry_subset_pruned {X ι : Type*} [MeasurableSpace X] {m : Measure X} {G : Set X}
    {E : ι → Set X} {R : ι → ℝ≥0∞} {K₁ : ℝ≥0∞}
    (huniq : ∀ x e e', x ∈ E e → x ∈ E e' → e = e') (hEG : ∀ e, E e ⊆ G) {x : X}
    (hx : x ∈ pruned m G E R K₁) {e : ι} (hxe : x ∈ E e) :
    E e ⊆ pruned m G E R K₁ ∧ R e / K₁ ≤ m (E e) := by
  obtain ⟨h1, h2⟩ := heavy_of_mem_pruned hx hxe
  exact ⟨subset_pruned_of_heavy huniq hEG h1 h2, h1⟩

/-- Total weight of the labels of one family. -/
theorem label_weights_le_one {α : Type} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (f : Fam α) (hA : ∀ i, MeasurableSet (f.A i))
    (hdisj : ∀ i i', i ≠ i' → f.j i = f.j i' → Disjoint (f.A i) (f.A i')) :
    ∑ i, ENNReal.ofReal f.q * ν (f.A i) ≤ 1 := by
  classical
  have hblock : ∀ b : Fin (2 ^ f.T),
      ∑ i ∈ Finset.univ.filter (fun i => f.j i = b), ν (f.A i) ≤ 1 := by
    intro b
    rw [← measure_biUnion_finset]
    · exact prob_le_one
    · intro i hi i' hi' hii'
      exact hdisj i i' hii' ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi').2.symm)
    · exact fun i _ => hA i
  have hsum : ∑ i, ν (f.A i) ≤ (2 ^ f.T : ℕ) := by
    rw [← Finset.sum_fiberwise Finset.univ f.j (fun i => ν (f.A i))]
    calc ∑ b : Fin (2 ^ f.T), ∑ i ∈ Finset.univ.filter (fun i => f.j i = b), ν (f.A i)
        ≤ ∑ _b : Fin (2 ^ f.T), (1 : ℝ≥0∞) := Finset.sum_le_sum (fun b _ => hblock b)
      _ = (2 ^ f.T : ℕ) := by simp
  rw [← Finset.mul_sum]
  have hq : ENNReal.ofReal f.q = ((2 ^ f.T : ℕ) : ℝ≥0∞)⁻¹ := by
    unfold Fam.q
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [show ((2 : ℝ) ^ f.T) = ((2 ^ f.T : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  rw [hq]
  calc ((2 ^ f.T : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, ν (f.A i) ≤ ((2 ^ f.T : ℕ) : ℝ≥0∞)⁻¹ * (2 ^ f.T : ℕ) :=
        mul_le_mul_right hsum _
    _ = 1 := ENNReal.inv_mul_cancel (by positivity) (by simp)

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
