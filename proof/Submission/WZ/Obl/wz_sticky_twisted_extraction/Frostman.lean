-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_sticky_twisted_extraction.Frostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_sticky_twisted_extraction.Definitions

namespace WangZahlLot.Obl.wz_sticky_twisted_extraction

open Set Metric MeasureTheory
open scoped ENNReal

/-- Exact counting for a partition expressed as a unique relation. -/
theorem sum_ncard_unique {n k : ℕ} (R : Fin n → Fin k → Prop)
    (hR : ∀ i, ∃! j, R i j) (P : Fin n → Prop) :
    ∑ j, ncard {i | R i j ∧ P i} = ncard {i | P i} := by
  classical
  let f : Fin n → Fin k := fun i => (hR i).choose
  have hf : ∀ i j, R i j ↔ f i = j := by
    intro i j
    constructor
    · intro h
      exact ((hR i).choose_spec.2 j h).symm
    · intro h
      rw [← h]
      exact (hR i).choose_spec.1
  simp_rw [hf]
  simpa [Set.ncard_eq_toFinset_card', Finset.filter_filter, and_comm] using
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter P) (Finset.univ : Finset (Fin k)) f

/-- Local convex counts sum to a global count at the same coarse radius. -/
theorem global_count_of_partition {n k : ℕ} (T : Fin n → Set Space)
    (R : Fin n → Fin k → Prop) (hR : ∀ i, ∃! j, R i j)
    {m ρ : ℝ} (hm : 0 ≤ m)
    (hcount : ∀ j, ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((ncard {i | R i j ∧ T i ⊆ W} : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (m * (ncard {i | R i j} : ℝ)) * volume W) :
    ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((ncard {i | T i ⊆ W} : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (m * (n : ℝ)) * volume W := by
  intro W hW
  have hsum : (∑ j, (ncard {i | R i j ∧ T i ⊆ W} : ℝ)) =
      (ncard {i | T i ⊆ W} : ℝ) := by
    exact_mod_cast sum_ncard_unique R hR (fun i => T i ⊆ W)
  have htotal : (∑ j, (ncard {i | R i j} : ℝ)) = (n : ℝ) := by
    exact_mod_cast (by simpa using sum_ncard_unique R hR (fun _ => True))
  calc
    ENNReal.ofReal ((ncard {i | T i ⊆ W} : ℝ) * ρ ^ 2) =
        ∑ j, ENNReal.ofReal ((ncard {i | R i j ∧ T i ⊆ W} : ℝ) * ρ ^ 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ← Finset.sum_mul, hsum]
    _ ≤ ∑ j, ENNReal.ofReal (m * (ncard {i | R i j} : ℝ)) * volume W :=
      Finset.sum_le_sum (fun j _ => hcount j W hW)
    _ = ENNReal.ofReal (m * (n : ℝ)) * volume W := by
      rw [← Finset.sum_mul,
        ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ← Finset.mul_sum, htotal]

/-- At the top scale `r = 1`, the original all-scales condition already gives
exactly the output's global Frostman condition. -/
theorem AllScales.globalFrostman {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : AllScales η δ n x v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    GlobalFrostman η δ n x v := by
  obtain ⟨ρ, hρ, hρ1, _, k, _, z, w, _, _, hpart, _, _, hcount⟩ :=
    h 1 hδ1 le_rfl
  have heq : ρ = 1 := le_antisymm hρ1 hρ
  subst ρ
  have hglobal := global_count_of_partition (fun i => Tube δ (x i) (v i))
    (fun i j => Tube δ (x i) (v i) ⊆ Tube 1 (z j) (w j)) hpart
    (Real.rpow_nonneg hδ.le _) hcount
  simpa only [GlobalFrostman, one_pow, mul_one] using hglobal

end WangZahlLot.Obl.wz_sticky_twisted_extraction
