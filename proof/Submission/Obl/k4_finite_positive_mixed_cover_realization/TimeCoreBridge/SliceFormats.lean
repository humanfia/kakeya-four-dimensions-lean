-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/SliceFormats.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/SliceFormats.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/SliceFormats.lean.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Tests

/-!
# Boolean formats and measurability through copy-index slices

* `gfmt_lift7`: a format on the six line coordinates is a format on the seven incidence
  coordinates.
* `gfmt_timeIcc`: the time window of a block.
* `measurableSet_of_slices6`, `measurableSet_of_slices7`: sets of lines (of incidences) whose
  slices at every copy index are measurable are measurable.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial MeasureTheory Submission.Lib.K4XInterface

theorem gfmt_lift7 {H : ℝ} {D : ℕ} {S : Set (Fin 6 → ℝ)} (h : gfmt 6 H D S) :
    gfmt 7 H D {x₁ : Fin 7 → ℝ | (fun j₁ : Fin 6 => x₁ j₁.castSucc) ∈ S} := by
  obtain ⟨m₀, hm, p₀, hp, b₀, hb⟩ := h
  refine ⟨m₀, hm, fun i => rename Fin.castSucc (p₀ i), fun i => (totalDegree_rename_le _ _).trans
    (hp i), b₀, fun x₁ => ?_⟩
  simp only [Set.mem_ofPred_eq, eval_rename]
  exact hb _

theorem gfmt_timeIcc (a b : ℝ) :
    gfmt 7 2 1 {x₁ : Fin 7 → ℝ | a ≤ x₁ 6 ∧ x₁ 6 ≤ b} := by
  have h1 := gfmt_nonneg (X 6 - C a : MvPolynomial (Fin 7) ℝ)
  have h2 := gfmt_nonneg (C b - X 6 : MvPolynomial (Fin 7) ℝ)
  have d1 : (X 6 - C a : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (max_le (by simp [totalDegree_X]) (by simp))
  have d2 : (C b - X 6 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (max_le (by simp) (by simp [totalDegree_X]))
  have h := gfmt_inter (gfmt_mono le_rfl d1 h1) (gfmt_mono le_rfl d2 h2)
  have e : {x : Fin 7 → ℝ | 0 ≤ eval x (X 6 - C a)} ∩ {x | 0 ≤ eval x (C b - X 6)} =
      {x₁ : Fin 7 → ℝ | a ≤ x₁ 6 ∧ x₁ 6 ≤ b} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, map_sub, eval_X, eval_C, sub_nonneg]
  rw [e] at h
  exact gfmt_mono (by norm_num) (by simp) h

theorem measurableSet_of_slices6 {S : Set (ℕ × (Fin 6 → ℝ))}
    (h : ∀ i, MeasurableSet {x | (i, x) ∈ S}) : MeasurableSet S := by
  have e : S = ⋃ i : ℕ, ({i} : Set ℕ) ×ˢ {x | (i, x) ∈ S} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro hp; exact ⟨p.1, rfl, hp⟩
    · rintro ⟨i, hi, hp⟩; rw [← hi] at hp; exact hp
  rw [e]
  exact MeasurableSet.iUnion fun i => (measurableSet_singleton i).prod (h i)

theorem snoc7_six (y : Fin 6 → ℝ) (t : ℝ) : (Fin.snoc y t : Fin 7 → ℝ) 6 = t :=
  Fin.snoc_last (α := fun _ => ℝ) (p := y) (x := t)

theorem snoc7_castSucc (y : Fin 6 → ℝ) (t : ℝ) :
    (fun j₁ : Fin 6 => (Fin.snoc y t : Fin 7 → ℝ) j₁.castSucc) = y := by
  funext j₁
  exact Fin.snoc_castSucc (α := fun _ => ℝ) _ _ _

theorem measurableSet_of_slices7 {S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (h : ∀ i, MeasurableSet {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ S}) :
    MeasurableSet S := by
  let φ : (Fin 6 → ℝ) × ℝ → (Fin 7 → ℝ) := fun q => Fin.snoc q.1 q.2
  have hφ : Measurable φ := by
    refine measurable_pi_iff.mpr fun k => ?_
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [φ, Fin.snoc_last]; exact measurable_snd
    · simp only [φ, Fin.snoc_castSucc]; exact (measurable_pi_apply k).comp measurable_fst
  have e : S = ⋃ i : ℕ, {p : (ℕ × (Fin 6 → ℝ)) × ℝ | p.1.1 = i} ∩
      (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => φ (p.1.2, p.2)) ⁻¹'
        {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ S} := by
    ext p
    obtain ⟨⟨i, y⟩, t⟩ := p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, φ,
      snoc7_six, snoc7_castSucc]
    constructor
    · intro hp; exact ⟨i, rfl, hp⟩
    · rintro ⟨i', hi, hp⟩; rw [hi]; exact hp
  rw [e]
  refine MeasurableSet.iUnion fun i => MeasurableSet.inter ?_ ?_
  · exact (measurableSet_singleton i).preimage (measurable_fst.comp measurable_fst)
  · exact (h i).preimage (hφ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
