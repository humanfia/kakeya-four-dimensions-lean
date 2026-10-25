-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Incidences.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Counts

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set

/-- Double counting with a lower row size and a bounded column multiplicity. -/
theorem bounded_incidence_count {n M : ℕ} (R : Fin n → Fin M → Prop)
    (P : Fin n → Prop) (S : Fin M → Prop) {N D : ℝ} (_hD : 0 ≤ D)
    (hlower : ∀ j, S j → N ≤ (Set.ncard {i | R i j} : ℝ))
    (hupper : ∀ i, (Set.ncard {j | R i j} : ℝ) ≤ D)
    (himp : ∀ i j, S j → R i j → P i) :
    (Set.ncard {j | S j} : ℝ) * N ≤ D * (Set.ncard {i | P i} : ℝ) := by
  classical
  have hcard {k : ℕ} (Q : Fin k → Prop) :
      (Set.ncard {i | Q i} : ℝ) = ∑ i, if Q i then (1 : ℝ) else 0 := by
    simp [Set.ncard_eq_toFinset_card', Finset.sum_boole]
  calc
    _ = ∑ j, if S j then N else 0 := by
      rw [hcard, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ ≤ ∑ j, ∑ i, if S j ∧ R i j then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : S j
      · simpa only [hj, true_and, ite_true, ← hcard] using hlower j hj
      · simp [hj]
    _ = ∑ i, ∑ j, if S j ∧ R i j then (1 : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ i, if P i then D else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : P i
      · simp only [hi, ite_true]
        calc
          _ ≤ ∑ j, if R i j then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro j _
            split_ifs <;> simp_all
          _ ≤ D := by rw [← hcard]; exact hupper i
      · have hfalse : ∀ j, ¬(S j ∧ R i j) := fun j h => hi (himp i j h.1 h.2)
        simp [hi, hfalse]
    _ = _ := by
      rw [hcard, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

end WangZahlLot.Obl.wz_nonflat_factored_improvement
