/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/PolynomialBinLists.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit4d8af73c,
Submission/Obl/k4_scalar_mesh_projection/PolynomialBinLists.lean.
Generic prerequisites retain their own accepted-source credits in Pruning.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Finalization.PolynomialBinPower
import Submission.Lib.K4ScalarCoreTools.Finalization.Pruning

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory

/-- All represented normalized-time coefficient bins in a physical fiber.
Different bins may have unrelated original witness rows. -/
def representedPolynomialBins (D : ℕ) (K ε : ℝ) (L : ℝ → Finset ℤ) :
    Set (Fin (D + 1) → ℤ) := {c | ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ (∀ k : Fin (D + 1), ⌊p.coeff k / ε⌋ = c k) ∧
      ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Icc (0 : ℝ) 1 ∧
        ENNReal.ofReal K⁻¹ ≤ volume A ∧ ∀ t ∈ A, ∃ z ∈ L t,
          |p.eval t - ε * (z : ℝ)| ≤ K * ε}

/-- The complete represented family is finite, with a uniform cardinal
bound. Finiteness of the coefficient list is a conclusion here. -/
theorem exists_represented_polynomial_bin_list_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K ε : ℝ), 1 ≤ K → 0 < ε →
      ∀ (L : ℝ → Finset ℤ),
      (∀ t ∈ Icc (0 : ℝ) 1, ((L t).card : ℝ) ≤ K) →
      ∃ F : Finset (Fin (D + 1) → ℤ),
        (↑F : Set (Fin (D + 1) → ℤ)) = representedPolynomialBins D K ε L ∧
        (F.card : ℝ) ≤ C * K^(3 * (D+1) + (D+1)^2 * D) := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_original_polynomial_bin_power_constant D
  refine ⟨C, hC, ?_⟩
  intro K ε hK hε L hL
  let R := representedPolynomialBins D K ε L
  have hfiniteCount (S : Finset (Fin (D + 1) → ℤ)) (hS : (↑S : Set _) ⊆ R) :
      (S.card : ℝ) ≤ C * K^(3 * (D+1) + (D+1)^2 * D) := by
    have hrepr (c : S) : ∃ p : Polynomial ℝ,
        p.natDegree ≤ D ∧ (∀ k : Fin (D + 1), ⌊p.coeff k / ε⌋ = c.val k) ∧
        ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Icc (0 : ℝ) 1 ∧
          ENNReal.ofReal K⁻¹ ≤ volume A ∧ ∀ t ∈ A, ∃ z ∈ L t,
            |p.eval t - ε * (z : ℝ)| ≤ K * ε := hS c.property
    choose p hp hcode A hAm hAunit hAlength hfit using hrepr
    let P : (Fin (D + 1) → ℤ) → Polynomial ℝ :=
      fun c => if hc : c ∈ S then p ⟨c, hc⟩ else 0
    let T : (Fin (D + 1) → ℤ) → Set ℝ :=
      fun c => if hc : c ∈ S then A ⟨c, hc⟩ else ∅
    apply hcount K ε hK hε S P _ _ T _ _ _ L hL _
    · intro c hc
      simpa only [P, dite_eq_left hc] using hp ⟨c, hc⟩
    · intro c hc k
      simpa only [P, dite_eq_left hc] using hcode ⟨c, hc⟩ k
    · intro c hc
      simpa only [T, dite_eq_left hc] using hAm ⟨c, hc⟩
    · intro c hc
      simpa only [T, dite_eq_left hc] using hAunit ⟨c, hc⟩
    · intro c hc
      simpa only [T, dite_eq_left hc] using hAlength ⟨c, hc⟩
    · intro c hc t ht
      have htA : t ∈ A ⟨c, hc⟩ := by simpa only [T, dite_eq_left hc] using ht
      simpa only [P, dite_eq_left hc] using hfit ⟨c, hc⟩ t htA
  have hR : R.Finite :=
    finite_of_uniform_finset_card_bound R
      (C * K^(3 * (D+1) + (D+1)^2 * D)) hfiniteCount
  refine ⟨hR.toFinset, hR.coe_toFinset, ?_⟩
  exact hfiniteCount hR.toFinset (by simp)

end Submission.Lib.K4ScalarCoreTools.Finalization
