-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.BroadMerge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs
import Submission.WZ.Obl.wz_tower_depth_step.BalancedCard

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

/-- Summing the same broadness inequality over all coarse fibres removes the
assignment without changing either the scale or the constant. -/
theorem broad_forget_fibres {δ ρ l β : ℝ} {n N : ℕ}
    {v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V} {f : Fin n → Fin N}
    (hbr : ∀ k p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        l * (r / ρ) ^ β * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) :
    ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        l * (r / ρ) ^ β * q n {i | i ∈ S ∧ p ∈ Z i} := by
  classical
  have hs (P : Fin n → Prop) :
      (∑ k : Fin N, q n {i | i ∈ S ∧ f i = k ∧ P i}) = q n {i | i ∈ S ∧ P i} := by
    have he (k : Fin N) : {i | i ∈ S ∧ f i = k ∧ P i} =
        {i | f i = k ∧ (i ∈ S ∧ P i)} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      tauto
    simp_rw [he]
    change (∑ k : Fin N, (Set.ncard {i | f i = k ∧ (i ∈ S ∧ P i)} : ℝ)) =
      (Set.ncard {i | i ∈ S ∧ P i} : ℝ)
    rw [← Nat.cast_sum, WangZahlLot.Obl.wz_tower_depth_step.sum_ncard_fibres]
  intro p u r hu hdr hrρ
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun k (_hk : k ∈ Finset.univ) => hbr k p u r hu hdr hrρ)
  rw [← Finset.mul_sum, hs, hs] at hh
  exact hh

/-- When shadings outside the retained family are empty, forgetting the
cover gives the broadness inequality on the full index type. -/
theorem broad_forget_cover {δ ρ l β : ℝ} {n N : ℕ}
    {v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V} {f : Fin n → Fin N}
    (hzero : ∀ i, i ∉ S → Z i = ∅)
    (hbr : ∀ k p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        l * (r / ρ) ^ β * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) :
    ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        l * (r / ρ) ^ β * q n {i | p ∈ Z i} := by
  have hmem (p : V) (i : Fin n) (hi : p ∈ Z i) : i ∈ S := by
    by_contra hn
    rw [hzero i hn] at hi
    exact hi
  have he (p : V) (P : Fin n → Prop) :
      {i | i ∈ S ∧ p ∈ Z i ∧ P i} = {i | p ∈ Z i ∧ P i} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    exact ⟨And.right, fun hi => ⟨hmem p i hi.1, hi⟩⟩
  have he' (p : V) : {i | i ∈ S ∧ p ∈ Z i} = {i | p ∈ Z i} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    exact ⟨And.right, fun hi => ⟨hmem p i hi, hi⟩⟩
  intro p u r hu hdr hrρ
  simpa only [he, he'] using broad_forget_fibres hbr p u r hu hdr hrρ

end WangZahlLot.Obl.wz_coarse_grains_assembly
