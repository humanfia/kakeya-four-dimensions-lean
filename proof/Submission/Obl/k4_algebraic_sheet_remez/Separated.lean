import Mathlib
import Submission.Lib.K4PolynomialRemez

namespace Submission.Obl.k4_algebraic_sheet_remez

open Set MeasureTheory

/-- Positive outer length provides any fixed number of quantitatively
separated interpolation nodes. -/
theorem exists_separated_finset (q : ℕ) (S : Set ℝ) {η : ℝ}
    (hη : 0 < η) (hmass : ENNReal.ofReal η ≤ volume S) :
    ∃ F : Finset ℝ, F.card = q ∧ (↑F : Set ℝ) ⊆ S ∧
      ∀ a ∈ F, ∀ b ∈ F, a ≠ b → η / (4 * ((q : ℝ) + 1)) ≤ |a - b| := by
  classical
  let δ := η / (4 * ((q : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 4 * ((q : ℝ) + 1) * δ = η := by dsimp [δ]; field_simp
  have hex (k : ℕ) : k ≤ q →
      ∃ F : Finset ℝ, F.card = k ∧ (↑F : Set ℝ) ⊆ S ∧
        ∀ a ∈ F, ∀ b ∈ F, a ≠ b → δ ≤ |a - b| := by
    induction k with
    | zero =>
      intro _
      exact ⟨∅, rfl, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨F, hFcard, hFS, hFsep⟩ := ih (by omega)
      have hbudget : 2 * (F.card : ℝ) * δ < η := by
        rw [hFcard]
        have hk' : (k : ℝ) ≤ q := by exact_mod_cast (show k ≤ q by omega)
        nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))]
      obtain ⟨t, ht, haway⟩ :=
        Submission.Lib.K4PolynomialRemez.exists_away_from_finset S F hη hδ.le hbudget hmass
      have htF : t ∉ F := by
        intro htF
        have hh := haway t htF
        rw [sub_self, abs_zero] at hh
        linarith
      refine ⟨insert t F, by simp [htF, hFcard], ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact ht
        · exact hFS ha
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | haF
        · rcases Finset.mem_insert.mp hb with rfl | hbF
          · exact (hab rfl).elim
          · exact haway b hbF
        · rcases Finset.mem_insert.mp hb with rfl | hbF
          · simpa only [abs_sub_comm] using haway a haF
          · exact hFsep a haF b hbF hab
  exact hex q le_rfl

/-- Sorted form of the separated interpolation nodes. -/
theorem exists_separated_nodes (q : ℕ) (S : Set ℝ) {η : ℝ}
    (hη : 0 < η) (hmass : ENNReal.ofReal η ≤ volume S) :
    ∃ t : Fin q → ℝ, StrictMono t ∧ (∀ i, t i ∈ S) ∧
      ∀ i j, i ≠ j → η / (4 * ((q : ℝ) + 1)) ≤ |t i - t j| := by
  classical
  obtain ⟨F, hF, hFS, hsep⟩ := exists_separated_finset q S hη hmass
  refine ⟨F.orderEmbOfFin hF, (F.orderEmbOfFin hF).strictMono, ?_, ?_⟩
  · intro i
    exact hFS (F.orderEmbOfFin_mem hF i)
  · intro i j hij
    exact hsep _ (F.orderEmbOfFin_mem hF i) _ (F.orderEmbOfFin_mem hF j)
      (fun h => hij ((F.orderEmbOfFin hF).injective h))

end Submission.Obl.k4_algebraic_sheet_remez
