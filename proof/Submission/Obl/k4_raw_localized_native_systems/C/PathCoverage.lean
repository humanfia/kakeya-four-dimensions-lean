import Submission.Obl.k4_raw_localized_native_systems.C.GoodPathMass

/-
Adapted from this LOT tree, o178, session x0596, `PathCoverage.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The full path carries the whole coverage of the chart system

In each world the full path is the disjoint union of the selected sets of the
world's charts at their own block index; the block right ends are null.  Hence
the weighted full-path mass equals the weighted coverage of the system.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

theorem blockIdx_of_mem_block {T : ℕ} {j : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T))
    (hne : t ≠ ((j : ℝ) + 1) / (2 : ℝ) ^ T) : blockIdx T t = (j : ℤ) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  unfold blockIdx
  rw [Int.floor_eq_iff]
  obtain ⟨h1, h3⟩ := ht
  have h3' : t < ((j : ℝ) + 1) / (2 : ℝ) ^ T := lt_of_le_of_ne h3 hne
  constructor
  · push_cast
    rw [div_le_iff₀ h2] at h1; linarith
  · push_cast
    rw [lt_div_iff₀ h2] at h3'; linarith

/-- The selected set of a chart, at its own block index. -/
def ownBlock (a : Atlas p k) (b : Fin a.C) : Set Point :=
  a.F b ∩ {q | blockIdx a.T q.2 = ((a.j b : ℕ) : ℤ)}

theorem fullPath_eq_iUnion {M D : ℕ} {κ r : ℝ} (a : Atlas p k) (γ : Fin (p.W k))
    {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex) :
    fullPath a γ = ⋃ b ∈ (Finset.univ.filter (fun b => a.γ b = γ)), ownBlock a b := by
  ext q
  simp only [fullPath, ownBlock, TagPred, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_inter_iff, exists_prop]
  constructor
  · rintro ⟨b, ⟨hγ, -, hj⟩, hF⟩
    exact ⟨b, hγ, hF, hj⟩
  · rintro ⟨b, hγ, hF, hj⟩
    exact ⟨b, ⟨hγ, (hc.selected b hF).2.1, hj⟩, hF⟩

theorem ownBlock_measure {M D : ℕ} {κ r : ℝ} (hp : Valid p) (a : Atlas p k)
    {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex) (b : Fin a.C) :
    priorMass p k (a.γ b) (ownBlock a b) = priorMass p k (a.γ b) (a.F b) := by
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  haveI : IsProbabilityMeasure (p.ν k (a.γ b)) := ((hfmt k).2.2.2.1 (a.γ b)).1
  apply le_antisymm (measure_mono Set.inter_subset_left)
  -- the complement inside `F` is the block's right end, a null set
  have hsub : a.F b ⊆ ownBlock a b ∪
      (Set.univ ×ˢ {(((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T}) := by
    intro q hq
    by_cases hne : q.2 = (((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T
    · right; exact ⟨trivial, hne⟩
    · left
      exact ⟨hq, blockIdx_of_mem_block (hc.selected b hq).2.2 hne⟩
  calc priorMass p k (a.γ b) (a.F b)
      ≤ priorMass p k (a.γ b) (ownBlock a b ∪
          (Set.univ ×ˢ {(((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T})) := measure_mono hsub
    _ ≤ priorMass p k (a.γ b) (ownBlock a b) +
          priorMass p k (a.γ b) (Set.univ ×ˢ {(((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T}) :=
        measure_union_le _ _
    _ = priorMass p k (a.γ b) (ownBlock a b) := by
        unfold priorMass
        rw [Measure.prod_prod, Real.volume_singleton, mul_zero, add_zero]

theorem ownBlock_disjoint {M D : ℕ} {κ r : ℝ} (a : Atlas p k)
    {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    {b b' : Fin a.C} (hne : b ≠ b') (hγ : a.γ b = a.γ b') :
    Disjoint (ownBlock a b) (ownBlock a b') := by
  rw [Set.disjoint_left]
  intro q hq hq'
  by_cases hj : a.j b = a.j b'
  · exact Set.disjoint_left.1 (hdisj b b' hne hγ hj) (hc.selected b hq.1).2.1
      (hc.selected b' hq'.1).2.1
  · apply hj
    have h1 := hq.2
    have h2 := hq'.2
    simp only [Set.mem_setOf_eq] at h1 h2
    rw [h1] at h2
    exact Fin.ext (by exact_mod_cast h2)

theorem measurableSet_ownBlock {M D : ℕ} {κ r : ℝ} (a : Atlas p k)
    {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex) (b : Fin a.C) :
    MeasurableSet (ownBlock a b) :=
  (hc.measF b).inter (measurableSet_eq_fun ((measurable_blockIdx a.T).comp measurable_snd)
    measurable_const)

/-- **Weighted full-path mass equals the weighted coverage.** -/
theorem weighted_fullPath_eq {M D : ℕ} {κ r : ℝ} (hp : Valid p) (a : Atlas p k)
    {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b')) :
    ∑ γ, ENNReal.ofReal (p.ω k γ) * ((p.ν k γ).prod volume) (fullPath a γ) =
      ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b) := by
  classical
  have hworld : ∀ γ, ((p.ν k γ).prod volume) (fullPath a γ) =
      ∑ b ∈ Finset.univ.filter (fun b => a.γ b = γ), priorMass p k (a.γ b) (a.F b) := by
    intro γ
    rw [fullPath_eq_iUnion a γ hc, measure_biUnion_finset]
    · apply Finset.sum_congr rfl
      intro b hb
      have hγ : a.γ b = γ := (Finset.mem_filter.1 hb).2
      rw [← ownBlock_measure hp a hc b]
      unfold priorMass
      rw [hγ]
    · intro b hb b' hb' hne
      exact ownBlock_disjoint a hc hdisj hne
        ((Finset.mem_filter.1 hb).2.trans (Finset.mem_filter.1 hb').2.symm)
    · intro b _
      exact measurableSet_ownBlock a hc b
  simp_rw [hworld, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun b => {a.γ b})]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro γ b
    simp [eq_comm]

end

end Submission.Obl.k4_raw_localized_native_systems.C
