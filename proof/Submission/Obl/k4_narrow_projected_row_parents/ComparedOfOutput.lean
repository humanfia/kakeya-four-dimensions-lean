import Submission.Obl.k4_narrow_projected_row_parents.ComparedOfLaw
import Submission.Obl.k4_narrow_projected_row_parents.CompareMap

/-!
# `Compared` from a single-index comparison output

The single-index comparison (o200 `PreparedComparison`) returns a law `law ≤ ζ` of nearly the
mass of `ζ`, measurable true labels (with a native branch) and projected labels of incidences,
partner lists per (true label, common code) of bounded size, and almost everywhere membership.
Its fields are restated here as hypotheses, so this file does not depend on the adaptation of
that record.

`compared_of_output` turns them into `Compared` for the projected assignments: the projected
label of an incidence is read from its line through the disjointness of the assignments, and the
branch of the true label is forgotten. `law_mass_of_budget` gives the mass floor from the
comparison's mass budget.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type} [MeasurableSpace α]

open Classical in
/-- The label of a line in a family of sets: some index whose set contains it, or `i₀`. -/
noncomputable def outputLineLabel {n : ℕ} (C : Fin n → Set α) (i₀ : Fin n) (l : α) : Fin n :=
  if h : ∃ i, l ∈ C i then h.choose else i₀

theorem outputLineLabel_eq {n : ℕ} {C : Fin n → Set α} (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (i₀ : Fin n) {l : α} {i : Fin n} (hl : l ∈ C i) : outputLineLabel C i₀ l = i := by
  classical
  have h : ∃ j, l ∈ C j := ⟨i, hl⟩
  simp only [outputLineLabel, h, dite_true]
  by_contra hne
  exact Set.disjoint_left.mp (hdisj hne) h.choose_spec hl

theorem measurable_outputLineLabel {n : ℕ} {C : Fin n → Set α} (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (i₀ : Fin n) :
    Measurable (outputLineLabel C i₀) := by
  classical
  refine measurable_to_countable' fun i => ?_
  by_cases hi : i = i₀
  · subst hi
    have heq : outputLineLabel C i ⁻¹' {i} = C i ∪ (⋃ j, C j)ᶜ := by
      ext l
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_compl_iff, mem_iUnion,
        not_exists]
      constructor
      · intro hl
        by_cases h : ∃ j, l ∈ C j
        · left
          obtain ⟨j, hj⟩ := h
          have := outputLineLabel_eq hdisj i hj
          rw [this] at hl
          rw [← hl]; exact hj
        · right; push_neg at h; exact h
      · rintro (hl | hl)
        · exact outputLineLabel_eq hdisj i hl
        · have h : ¬ ∃ j, l ∈ C j := fun ⟨j, hj⟩ => hl j hj
          simp only [outputLineLabel, h, dite_false]
    rw [heq]
    exact (hC i).union (MeasurableSet.iUnion hC).compl
  · have heq : outputLineLabel C i₀ ⁻¹' {i} = C i := by
      ext l
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro hl
        by_cases h : ∃ j, l ∈ C j
        · obtain ⟨j, hj⟩ := h
          have := outputLineLabel_eq hdisj i₀ hj
          rw [this] at hl
          rw [← hl]; exact hj
        · have : outputLineLabel C i₀ l = i₀ := by simp only [outputLineLabel, h, dite_false]
          exact absurd (hl.symm.trans this) hi
      · intro hl
        exact outputLineLabel_eq hdisj i₀ hl
    rw [heq]
    exact hC i

/-- The mass floor of the retained law from the comparison's mass budget. -/
theorem law_mass_of_budget {ζ law : Measure (α × ℝ)} {X Y H₀ : ℝ} (hH₀ : 0 < H₀)
    (hζ : ENNReal.ofReal H₀⁻¹ ≤ ζ univ)
    (hbudget : ζ univ ≤ law univ + ENNReal.ofReal X + ENNReal.ofReal Y)
    (hXY : X + Y ≤ (2 * H₀)⁻¹) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ENNReal.ofReal (2 * H₀)⁻¹ ≤ law univ := by
  have hsplit : ENNReal.ofReal H₀⁻¹ = ENNReal.ofReal (2 * H₀)⁻¹ + ENNReal.ofReal (2 * H₀)⁻¹ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hXY' : ENNReal.ofReal X + ENNReal.ofReal Y ≤ ENNReal.ofReal (2 * H₀)⁻¹ := by
    rw [← ENNReal.ofReal_add hX hY]; exact ENNReal.ofReal_le_ofReal hXY
  have h1 : ENNReal.ofReal (2 * H₀)⁻¹ + ENNReal.ofReal (2 * H₀)⁻¹ ≤
      law univ + ENNReal.ofReal (2 * H₀)⁻¹ := by
    rw [← hsplit]
    calc ENNReal.ofReal H₀⁻¹ ≤ ζ univ := hζ
      _ ≤ law univ + ENNReal.ofReal X + ENNReal.ofReal Y := hbudget
      _ = law univ + (ENNReal.ofReal X + ENNReal.ofReal Y) := by rw [add_assoc]
      _ ≤ law univ + ENNReal.ofReal (2 * H₀)⁻¹ := by gcongr
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h1

/-- **`Compared` from a single-index comparison output.** -/
theorem compared_of_output {a : PreparedModel α} {k : ℕ} {s q χ g m M : ℝ} {n : ℕ}
    (C : Fin n → Set α) (hCm : ∀ i, MeasurableSet (C i))
    (hCdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hb : Measurable (a.b k)) (hW : ∀ Q, MeasurableSet (a.B k s Q ×ˢ a.block k s Q))
    (ζ law : Measure (α × ℝ)) (hζρ : ζ ≤ a.rho k) (hlaw : law ≤ ζ)
    (hmass : ENNReal.ofReal M⁻¹ ≤ law univ) (hM : 0 < M)
    (tru : α × ℝ → Fin (a.n k s) × Bool) (htru : Measurable tru)
    (lab : α × ℝ → Fin n)
    (partners : Fin (a.n k s) → (Fin 5 → ℤ) → Finset (Fin n))
    (hcard : ∀ i c, ((partners i c).card : ℝ) ≤ M)
    (hsource : ∀ᵐ z ∂law, z.1 ∈ a.B k s (tru z).1 ∧ z.2 ∈ a.block k s (tru z).1 ∧
      z.1 ∈ C (lab z) ∧ lab z ∈ partners (tru z).1 (ccode q χ g m (a.b k z.1) z.2)) :
    Nonempty (Compared a k s C q χ g m M) := by
  classical
  -- a default projected label
  have hpos : law univ ≠ 0 := by
    intro h0
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hmass
    exact absurd hmass (not_le.mpr (inv_pos.mpr hM))
  obtain ⟨z₀⟩ : Nonempty (α × ℝ) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hpos (by rw [Set.univ_eq_empty_iff.mpr hne, measure_empty])
  set i₀ := lab z₀
  refine ⟨compared_of_ae C hCm law (hlaw.trans hζρ) hmass (outputLineLabel C i₀)
    (measurable_outputLineLabel hCm hCdisj i₀) (fun z => (tru z).1)
    ((measurable_fst).comp htru) hW hb partners hcard ?_⟩
  filter_upwards [hsource] with z hz
  obtain ⟨hB, hblk, hC, hpart⟩ := hz
  have hlab : outputLineLabel C i₀ z.1 = lab z := outputLineLabel_eq hCdisj i₀ hC
  rw [hlab]
  exact ⟨hC, ⟨hB, hblk⟩, hpart⟩

end Submission.Obl.k4_narrow_projected_row_parents
