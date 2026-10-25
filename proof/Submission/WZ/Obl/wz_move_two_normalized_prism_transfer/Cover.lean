-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.Cover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Defs
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.BalancedSlab

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer

open Set MeasureTheory

/-- A balanced retained assignment inherits the coarse Frostman bound from the fine
family. Unique containment supplies the final overlap count in the frozen cover. -/
theorem cover_of_unique_balanced {δ h η l ρ K D : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hS : S.Nonempty) (hK : 0 ≤ K) (hD : 0 ≤ D) (hl : 0 ≤ l)
    (hA : A δ η (δ ^ (-η)) l n x v Y)
    (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅))
    (hmass : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i))
    (hw : ∀ k, ‖w k‖ = 1)
    (hcont : ∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i)))
    (hbal : ∀ k k', q n {i | i ∈ S ∧ f i = k} ≤ K * q n {i | i ∈ S ∧ f i = k'})
    (hcard : (n : ℝ) ≤ D * S.card)
    (hX : X ρ N y w)
    (huniq : ∀ i ∈ S, ∀ k, T δ (x i) (v i) ⊆ T ρ (y k) (w k) → k = f i)
    (hFbudget : K * D * l ≤ δ ^ (-h)) (hKbudget : K ≤ δ ^ (-h))
    (hone : 1 ≤ δ ^ (-h)) :
    C δ h n x v Y S Z ρ N y w f True := by
  classical
  have hcardeq (k : Fin N) : q n {i | i ∈ S ∧ f i = k} =
      ((S.filter (fun i => f i = k)).card : ℝ) := by
    have he : {i | i ∈ S ∧ f i = k} = (S.filter (fun i => f i = k) : Set (Fin n)) := by
      ext i
      simp
    simp only [q, he, Set.ncard_coe_finset]
  have hF := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces.slab_count_of_balanced_cover
    S hS f (fun k => T ρ (y k) (w k)) hK hD hl
    (fun i _ => (hA.2.1 i).2.1) hcont
    (by intro k k'; simpa only [hcardeq] using hbal k k') hcard hA.2.2.2.2.2
  refine ⟨hZ, hmass, hw, hcont, ?_, trivial, ?_, hX, ?_⟩
  · intro u t r hu hr
    have hc : q N {k | T ρ (y k) (w k) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}} ≤
        q N {k | T ρ (y k) (w k) ⊆ {p | |inner ℝ u p - t| ≤ r}} := by
      apply Nat.cast_le.mpr
      exact Set.ncard_le_ncard (fun k hk => hk.trans Set.inter_subset_right) (Set.toFinite _)
    exact (ENNReal.ofReal_le_ofReal hc).trans ((hF u t r hu hr).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hFbudget (Nat.cast_nonneg N))) le_rfl))
  · intro k k'
    exact (hbal k k').trans
      (mul_le_mul_of_nonneg_right hKbudget (Nat.cast_nonneg _))
  · intro i hi
    have he : {k | T δ (x i) (v i) ⊆ T ρ (y k) (w k)} = {f i} := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · exact huniq i hi k
      · intro hk
        simpa only [hk] using hcont i hi
    change q N {k | T δ (x i) (v i) ⊆ T ρ (y k) (w k)} ≤ δ ^ (-h)
    simpa only [q, he, Set.ncard_singleton, Nat.cast_one] using hone

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
