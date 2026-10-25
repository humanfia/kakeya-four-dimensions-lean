-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorGreedy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorMin

/-!
# Step 2 of WZ Proposition 4.6: greedy extraction of maximising hulls

Starting from a family `U₀` whose Katz–Tao constant is robust (every subfamily of at least half
its size keeps a `τ₀` share of `KT U₀`), repeatedly take a hull `W_j` on which the remaining family
attains its Katz–Tao constant and remove the tubes it contains (`R_j`). Until fewer than half of
the tubes remain, each step removes `#R_j ≥ τ₀ KT(U₀) vol(W_j) / ρ²` tubes (WZ (4.11)).
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

variable {N : ℕ} {R ρ : ℝ} {y w : Fin N → Space}

theorem ratio_empty (U : Finset (Fin N)) : ratio ρ y w U ∅ = 0 := by
  simp [ratio, hull]

theorem Fam.greedy (hF : Fam R ρ y w) {U₀ : Finset (Fin N)} (hU₀ : U₀.Nonempty) {τ₀ : ℝ}
    (hrob : ∀ U'' ⊆ U₀, (U₀.card : ℝ) ≤ 2 * U''.card → τ₀ * KT ρ y w U₀ ≤ KT ρ y w U'') :
    ∀ U' ⊆ U₀, ∃ (J : ℕ) (S R : Fin J → Finset (Fin N)),
      (∀ j, (S j).Nonempty ∧ S j ⊆ U₀ ∧ R j ⊆ U' ∧
        (∀ k ∈ R j, tube ρ y w k ⊆ hull ρ y w (S j)) ∧
        τ₀ * KT ρ y w U₀ * (volume (hull ρ y w (S j))).toReal ≤ (R j).card * ρ ^ 2) ∧
      (∀ i j, i ≠ j → Disjoint (R i) (R j)) ∧
      2 * U'.card < U₀.card + 2 * ∑ j, (R j).card := by
  classical
  intro U' hU'
  induction hcard : U'.card using Nat.strong_induction_on generalizing U' with
  | _ n ih =>
  by_cases hstop : 2 * U'.card < U₀.card
  · refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun i => i.elim0, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]
    omega
  replace hstop := not_lt.mp hstop
  have hU'ne : U'.Nonempty := by
    rw [← Finset.card_pos]; have := hU₀.card_pos; omega
  obtain ⟨S, hSU', hS⟩ := exists_ratio_eq_KT (ρ := ρ) (y := y) (w := w) U'
  have hKTpos : 0 < KT ρ y w U' := lt_of_lt_of_le (by norm_num) (hF.KT_lower hU'ne)
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | h
    · rw [ratio_empty] at hS; linarith
    · exact h
  set R := sub ρ y w U' (hull ρ y w S) with hRdef
  have hRU' : R ⊆ U' := sub_subset U' _
  have hSR : S ⊆ R := fun k hk => mem_sub.mpr ⟨hSU' hk, tube_subset_hull hk⟩
  have hRne : R.Nonempty := hSne.mono hSR
  have hvpos := hF.hull_volume_pos hSne
  have hlarge : τ₀ * KT ρ y w U₀ * (volume (hull ρ y w S)).toReal ≤ R.card * ρ ^ 2 := by
    have h1 : R.card * ρ ^ 2 = KT ρ y w U' * (volume (hull ρ y w S)).toReal := by
      rw [← hS]; unfold ratio; rw [← hRdef]; field_simp
    rw [h1]
    gcongr
    exact hrob U' hU' (by exact_mod_cast hstop)
  -- recurse on the remaining tubes
  have hlt : (U' \ R).card < n := by
    rw [← hcard]
    exact Finset.card_lt_card (Finset.sdiff_ssubset hRU' hRne)
  obtain ⟨J, S', R', hprop, hdisj, hsum⟩ := ih _ hlt (U' \ R) (Finset.sdiff_subset.trans hU') rfl
  refine ⟨J + 1, Fin.cons S S', Fin.cons R R', ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]
      exact ⟨hSne, hSU'.trans hU', hRU', fun k hk => (mem_sub.mp hk).2, hlarge⟩
    · simp only [Fin.cons_succ]
      obtain ⟨h1, h2, h3, h4, h5⟩ := hprop i
      exact ⟨h1, h2, h3.trans Finset.sdiff_subset, h4, h5⟩
  · have h0 : ∀ i, Disjoint R (R' i) := fun i =>
      Finset.disjoint_of_subset_right (hprop i).2.2.1 Finset.disjoint_sdiff
    intro i j hij
    induction i using Fin.cases <;> induction j using Fin.cases
    · exact absurd rfl hij
    · simp only [Fin.cons_zero, Fin.cons_succ]; exact h0 _
    · simp only [Fin.cons_zero, Fin.cons_succ]; exact (h0 _).symm
    · simp only [Fin.cons_succ]
      exact hdisj _ _ (fun h => hij (by rw [h]))
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hc : (U' \ R).card + R.card = U'.card := Finset.card_sdiff_add_card_eq_card hRU'
    omega

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
