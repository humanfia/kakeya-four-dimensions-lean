-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainSelection.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainWitnesses
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRestriction
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (assignedFiber)
open WangZahlLot.Obl.wz_separated_cover_refinement
  (enumerate enumerate_mem enumerate_injective enumerate_surjective enumerate_sum)

noncomputable section

/-- Retain a collection of whole grain shadings. -/
def selectGrains {L : ℕ} (Q : Finset (Fin L)) (Hg : Fin L → Set V) (j : Fin L) : Set V :=
  if j ∈ Q then Hg j else ∅

theorem mem_selectGrains {L : ℕ} (Q : Finset (Fin L)) (Hg : Fin L → Set V)
    (j : Fin L) (p : V) : p ∈ selectGrains Q Hg j ↔ j ∈ Q ∧ p ∈ Hg j := by
  by_cases hj : j ∈ Q <;> simp [selectGrains, hj]

theorem selectGrains_mass {L : ℕ} (Q : Finset (Fin L)) (Hg : Fin L → Set V) :
    ∑ j, μ (selectGrains Q Hg j) = ∑ j ∈ Q, μ (Hg j) := by
  classical
  simp [selectGrains, apply_ite]

/-- Whole-grain selection preserves all frozen grain geometry and multiplicity.
Only the new aggregate density and local convex-count inequalities have to be
verified for the selected indices. The fine index set and coarse assignment
are kept fixed; the fine shadings are cut by the selected carrier in each fibre. -/
theorem grains_of_selection {δ h h' ρ a c b g g' : ℝ} (hδ : 0 < δ)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (Q : Finset (Fin L))
    (hmass : O (δ ^ h' * Q.card * a * (ρ * c) * c) ≤ ∑ j ∈ Q, μ (Hg j))
    (hcount : ∀ j ∈ Q, ∀ W, Convex ℝ W →
      O (q L {j' | j' ∈ Q ∧
        P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O g' * μ W) :
    H δ h' n x v S (fun i => Z i ∩ assignedFiber γ (selectGrains Q Hg) (f i))
      ρ N y w f a c b g' := by
  classical
  obtain ⟨hda, hab, hbc, hc1, hgeom, hdisj, hunion, _, hmult, hcross, hblen, _⟩ := hG
  have ha : 0 ≤ a := hδ.le.trans hda
  have hrc : 0 ≤ ρ * c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  let pick : Fin Q.card → Fin L := enumerate Q
  have hpick : Function.Injective pick := enumerate_injective Q
  have hpickQ : ∀ j, pick j ∈ Q := enumerate_mem Q
  refine ⟨Q.card, z ∘ pick, e ∘ pick, Hg ∘ pick, γ ∘ pick, m,
    hda, hab, hbc, hc1, ?_, ?_, ?_, ?_, ?_, ?_, hblen, ?_⟩
  · intro j
    exact hgeom (pick j)
  · intro j j' hne hγ
    exact hdisj (pick j) (pick j') (fun heq => hne (hpick heq)) hγ
  · intro k
    ext p
    constructor
    · rintro ⟨j, hjk, hpj⟩
      have hpold : p ∈ {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i} :=
        (hunion k).subset ⟨pick j, hjk, hpj⟩
      obtain ⟨i, hi, hik, hpi⟩ := hpold
      refine ⟨i, hi, hik, hpi, pick j, hjk.trans hik.symm, ?_⟩
      exact (mem_selectGrains Q Hg (pick j) p).mpr ⟨hpickQ j, hpj⟩
    · rintro ⟨i, hi, hik, hpi, j, hjf, hpj⟩
      obtain ⟨hjQ, hpH⟩ := (mem_selectGrains Q Hg j p).mp hpj
      obtain ⟨j', hj'⟩ := enumerate_surjective Q hjQ
      refine ⟨j', ?_, ?_⟩
      · change γ (pick j') = k
        rw [show pick j' = j from hj']
        exact hjf.trans hik
      · change p ∈ Hg (pick j')
        rwa [show pick j' = j from hj']
  · change O (δ ^ h' * Q.card * a * (ρ * c) * c) ≤
      ∑ j : Fin Q.card, μ (Hg (enumerate Q j))
    rw [enumerate_sum Q (fun j => μ (Hg j))]
    exact hmass
  · intro k p hp
    obtain ⟨i, hi, hik, hpi, hpC⟩ := hp
    have hpCk : p ∈ assignedFiber γ (selectGrains Q Hg) k := hik ▸ hpC
    have hset : {i | i ∈ S ∧ f i = k ∧
        p ∈ Z i ∩ assignedFiber γ (selectGrains Q Hg) (f i)} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
      ext i'
      constructor
      · rintro ⟨hi', hi'k, hpZ, _⟩
        exact ⟨hi', hi'k, hpZ⟩
      · rintro ⟨hi', hi'k, hpZ⟩
        exact ⟨hi', hi'k, hpZ, hi'k.symm ▸ hpCk⟩
    rw [hset]
    exact hmult k p ⟨i, hi, hik, hpi⟩
  · intro i hi j hfi hne
    have hne' : (Z i ∩ Hg (pick j)).Nonempty := by
      obtain ⟨p, hpZ, hpH⟩ := hne
      exact ⟨p, hpZ.1, hpH⟩
    obtain ⟨hshade, hfront, hends⟩ := hcross i hi (pick j) hfi hne'
    exact ⟨fun p hp => hshade ⟨hp.1.1, hp.2⟩, hfront, hends⟩
  · intro j W hW
    have hnat :
        {j' : Fin Q.card |
          P (a / ρ) c c (z (pick j')) (e (pick j')) ⊆
            P (2 * a / ρ) (2 * c) (2 * c) (z (pick j)) (e (pick j)) ∧
          P a (ρ * c) c (z (pick j')) (e (pick j')) ⊆ W}.ncard ≤
        {j' : Fin L | j' ∈ Q ∧
          P (a / ρ) c c (z j') (e j') ⊆
            P (2 * a / ρ) (2 * c) (2 * c) (z (pick j)) (e (pick j)) ∧
          P a (ρ * c) c (z j') (e j') ⊆ W}.ncard :=
      Set.ncard_le_ncard_of_injOn pick
        (fun j' hj' => ⟨hpickQ j', hj'⟩) hpick.injOn (Set.toFinite _)
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnat) (by positivity))).trans
      (hcount (pick j) (hpickQ j) W hW)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
