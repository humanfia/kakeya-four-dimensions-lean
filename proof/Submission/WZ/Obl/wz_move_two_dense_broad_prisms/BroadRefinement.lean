-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.BroadRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/- Adapted from session x0449 on o152 in this workspace. -/
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs

/-! Broadness after a refinement retaining a controlled pointwise incidence fraction. -/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set LeanEval.Analysis.WangZahlKakeya

/-- If every surviving fibre point keeps at least a `δ^t` fraction of its old
incidences, broadness survives with the corresponding additional error `t`.
Nothing is required at points where the new shading is empty. -/
theorem broad_of_retained_fibre_count {ω ζ δ h t ρ : ℝ} {n N : ℕ}
    {v : Fin n → Space} {S : Finset (Fin n)} {Y Z : Fin n → Set Space}
    {f : Fin n → Fin N} (hδ : 0 < δ) (hZY : ∀ i, Z i ⊆ Y i)
    (hBr : Broad ω ζ δ h ρ n N v S Y f)
    (hretain : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
      (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Y i} : ℝ) ≤
        δ ^ (-t) * (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : ℝ)) :
    Broad ω ζ δ (h + t) ρ n N v S Z f := by
  intro k p u r hu hδr hrρ
  have hr : 0 < r := hδ.trans_le hδr
  have hρ : 0 < ρ := hr.trans_le hrρ
  by_cases hnon : ∃ i ∈ S, f i = k ∧ p ∈ Z i
  · have hcap : (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧
          min ‖v i - u‖ ‖v i + u‖ ≤ r} : ℝ) ≤
        (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Y i ∧
          min ‖v i - u‖ ‖v i + u‖ ≤ r} : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard
        (show {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ⊆
          {i | i ∈ S ∧ f i = k ∧ p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} from
          fun i hi => ⟨hi.1, hi.2.1, hZY i hi.2.2.1, hi.2.2.2⟩)
    have hpow : δ ^ (-h) * δ ^ (-t) = δ ^ (-(h + t)) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    refine (hcap.trans (hBr k p u r hu hδr hrρ)).trans ?_
    calc δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) *
          (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Y i} : ℝ)
        ≤ δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) *
          (δ ^ (-t) * (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : ℝ)) :=
          mul_le_mul_of_nonneg_left (hretain k p hnon) (by positivity)
      _ = δ ^ (-(h + t)) * (r / ρ) ^ (ω * ζ / 100) *
          (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : ℝ) := by
        rw [← hpow]
        ring
  · have hempty : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hnon ⟨i, hi.1, hi.2.1, hi.2.2.1⟩
    change (Set.ncard _ : ℝ) ≤ _
    rw [hempty, Set.ncard_empty, Nat.cast_zero]
    positivity

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
