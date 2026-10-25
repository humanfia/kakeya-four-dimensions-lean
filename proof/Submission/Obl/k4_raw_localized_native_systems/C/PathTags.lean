import Submission.Obl.k4_raw_localized_native_systems.C.ChartStrips

/-
Adapted from this LOT tree, o178, session x0596, `PathTags.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Tags of a chart system along its path

For a chart family (an o153 `Atlas`) in one world, an incidence is tagged by the
first chart whose assignment contains its line and whose dyadic block index is
the block index of its time.  Disjointness within a world and block makes the
tag the chart of every selected incidence (away from block right ends).
The tag is measurable.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The dyadic block index of a time. -/
def blockIdx (T : ℕ) (t : ℝ) : ℤ := ⌊t * (2 : ℝ) ^ T⌋

theorem measurable_blockIdx (T : ℕ) : Measurable (blockIdx T) := by
  unfold blockIdx
  exact Int.measurable_floor.comp (measurable_id.mul_const _)

theorem blockIdx_mem_block {T : ℕ} {j : ℕ} {t : ℝ}
    (h : blockIdx T t = (j : ℤ)) : t ∈ Set.Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  unfold blockIdx at h
  have h1 := Int.floor_le (t * (2 : ℝ) ^ T)
  have h3 := Int.lt_floor_add_one (t * (2 : ℝ) ^ T)
  rw [h] at h1 h3
  push_cast at h1 h3
  constructor
  · rw [div_le_iff₀ h2]; exact h1
  · rw [le_div_iff₀ h2]; linarith

section Tags

variable {p : Data} {k : ℕ} (a : Atlas p k) (γ : Fin (p.W k))

/-- The tagging predicate. -/
def TagPred (q : Point) (b : Fin a.C) : Prop :=
  a.γ b = γ ∧ q.1 ∈ a.A b ∧ blockIdx a.T q.2 = ((a.j b : ℕ) : ℤ)

open Classical in
/-- The first chart tagging an incidence (a default chart if none). -/
def tagOf (hC : 0 < a.C) (q : Point) : Fin a.C :=
  if h : ∃ b, TagPred a γ q b then Fin.find (TagPred a γ q) h else ⟨0, hC⟩

theorem measurableSet_tagPred (hA : ∀ b, MeasurableSet (a.A b)) (b : Fin a.C) :
    MeasurableSet {q : Point | TagPred a γ q b} := by
  unfold TagPred
  by_cases hγ : a.γ b = γ
  · simp only [hγ, true_and]
    exact ((hA b).preimage measurable_fst).inter
      (measurableSet_eq_fun ((measurable_blockIdx a.T).comp measurable_snd) measurable_const)
  · simp [hγ]

open Classical in
theorem measurable_tagOf (hC : 0 < a.C) (hA : ∀ b, MeasurableSet (a.A b)) :
    Measurable (tagOf a γ hC) := by
  apply measurable_to_countable'
  intro b
  have : tagOf a γ hC ⁻¹' {b} =
      ({q | TagPred a γ q b} ∩ ⋂ b' ∈ (Finset.univ.filter (· < b)), {q | ¬ TagPred a γ q b'}) ∪
      ({q | ∀ b', ¬ TagPred a γ q b'} ∩ {_q | b = ⟨0, hC⟩}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff, tagOf, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · rw [Fin.find_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, fun b' hb' => h2 b' hb'⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
        · exact ⟨h1, fun b' hb' => h2 b' hb'⟩
        · obtain ⟨b'', hb''⟩ := h; exact absurd hb'' (h1 b'')
    · push Not at h
      constructor
      · rintro rfl; exact Or.inr ⟨h, rfl⟩
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd h1 (h b)
        · exact h2.symm
  rw [this]
  refine MeasurableSet.union ?_ ?_
  · refine (measurableSet_tagPred a γ hA b).inter ?_
    refine MeasurableSet.biInter (Set.to_countable _) fun b' _ => ?_
    exact (measurableSet_tagPred a γ hA b').compl
  · refine MeasurableSet.inter ?_ ?_
    · have : {q : Point | ∀ b', ¬ TagPred a γ q b'} = ⋂ b', {q | TagPred a γ q b'}ᶜ := by
        ext q; simp
      rw [this]
      exact MeasurableSet.iInter fun b' => (measurableSet_tagPred a γ hA b').compl
    · by_cases hb : b = ⟨0, hC⟩
      · simp [hb]
      · simp [hb]

/-- If an incidence is tagged by some chart, `tagOf` is a tagging chart. -/
theorem tagPred_tagOf (hC : 0 < a.C) {q : Point} (h : ∃ b, TagPred a γ q b) :
    TagPred a γ q (tagOf a γ hC q) := by
  classical
  unfold tagOf
  rw [dif_pos h]
  exact Fin.find_spec h

/-- With disjoint assignments in each world and block, every tagging chart is `tagOf`. -/
theorem tagOf_eq (hC : 0 < a.C)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    {q : Point} {b : Fin a.C} (hb : TagPred a γ q b) : tagOf a γ hC q = b := by
  have hex : ∃ b, TagPred a γ q b := ⟨b, hb⟩
  have ht := tagPred_tagOf a γ hC hex
  by_contra hne
  have hγ : a.γ (tagOf a γ hC q) = a.γ b := ht.1.trans hb.1.symm
  have hj : a.j (tagOf a γ hC q) = a.j b := by
    have h1 := ht.2.2
    have h2 := hb.2.2
    rw [h1] at h2
    exact Fin.ext (by exact_mod_cast h2)
  exact Set.disjoint_left.1 (hdisj _ _ hne hγ hj) ht.2.1 hb.2.1

end Tags

end

end Submission.Obl.k4_raw_localized_native_systems.C
