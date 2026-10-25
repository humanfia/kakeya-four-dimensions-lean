-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainRefinement.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.StateSelection

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber assignedFiber_eq_supported fine_level_of_UF)

noncomputable section

/-- Refining the grain shadings and cutting each fine shading by the full
retained carrier preserves the exact crossing clauses. Disjointness inside a
coarse fibre prevents a retained point in one grain from entering another. -/
theorem grainWitnesses_of_refinement {δ h h' ρ a c b g : ℝ}
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg H' : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (hH'm : ∀ j, MeasurableSet (H' j)) (hsub : ∀ j, H' j ⊆ Hg j)
    (hmass : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ j, μ (H' j)) :
    GrainWitnesses δ h' n x v S (fun i => Z i ∩ assignedFiber γ H' (f i))
      ρ N y w f a c b g L z e H' γ m := by
  obtain ⟨hda, hab, hbc, hc1, hgeom, hdisj, hunion, _, hmult, hcross, hblen, hcount⟩ := hG
  refine ⟨hda, hab, hbc, hc1, ?_, ?_, ?_, hmass, ?_, ?_, hblen, hcount⟩
  · intro j
    exact ⟨hH'm j, (hsub j).trans (hgeom j).2.1, (hgeom j).2.2⟩
  · intro j j' hne hγ
    exact (hdisj j j' hne hγ).mono (hsub j) (hsub j')
  · intro k
    ext p
    constructor
    · rintro ⟨j, hjk, hpj⟩
      have hpold : p ∈ {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i} :=
        (hunion k).subset ⟨j, hjk, hsub j hpj⟩
      obtain ⟨i, hi, hik, hpi⟩ := hpold
      exact ⟨i, hi, hik, hpi, j, hjk.trans hik.symm, hpj⟩
    · rintro ⟨i, _, hik, _, j, hjf, hpj⟩
      exact ⟨j, hjf.trans hik, hpj⟩
  · intro k p hp
    obtain ⟨i, hi, hik, hpi, hpC⟩ := hp
    have hpCk : p ∈ assignedFiber γ H' k := hik ▸ hpC
    have hset : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ assignedFiber γ H' (f i)} =
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
    have hne' : (Z i ∩ Hg j).Nonempty := by
      obtain ⟨p, hpZ, hpH⟩ := hne
      exact ⟨p, hpZ.1, hsub j hpH⟩
    obtain ⟨hshade, hfront, hends⟩ := hcross i hi j hfi hne'
    refine ⟨?_, hfront, hends⟩
    rintro p ⟨⟨hpZ, j', hj'f, hpH'⟩, hpU⟩
    have hpH : p ∈ Hg j := hshade ⟨hpZ, hpU⟩
    have heq : j' = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj j' j hne (hj'f.trans hfi)) (hsub j' hpH') hpH
    simpa only [heq] using hpH'

/-- Arbitrary measurable subshadings of the original grains transfer their
retained mass to the exact frozen cover through a full-fibre cut. -/
theorem cover_of_grain_refinement {δ h h' ρ a c b g t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg H' : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (hH'm : ∀ j, MeasurableSet (H' j)) (hsub : ∀ j, H' j ⊆ Hg j)
    (hretain : O t * ∑ j, μ (Hg j) ≤ ∑ j, μ (H' j))
    (hbudget : O (δ ^ h') ≤ O (t / 2) * O (δ ^ h)) :
    C δ h' n x v Y S (fun i => Z i ∩ assignedFiber γ H' (f i)) ρ N y w f True := by
  classical
  obtain ⟨_, _, _, _, hgeom, hdisj, hunion, _, hmult, _⟩ := hG
  have hZsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  have hfib : ∀ k, assignedFiber γ Hg k = assignedFiber f Z k := by
    intro k
    rw [assignedFiber_eq_supported f hZsupport k]
    exact hunion k
  obtain ⟨m', hm', hlevel⟩ := fine_level_of_UF hZsupport ⟨m, hmult⟩
  obtain ⟨hW, hmass, _⟩ := grain_refinement_transfer_full f γ Z Hg H' hm' ht
    (fun i => (hC.1 i).1) (fun j => (hgeom j).1) hH'm hsub hdisj hfib hlevel hretain
  let W := fun i => Z i ∩ assignedFiber γ H' (f i)
  have hWsupport : ∀ i, i ∉ S → W i = ∅ := by
    intro i hi
    simp [W, hZsupport i hi]
  have hZsum : ∑ i ∈ S, μ (Z i) = ∑ i, μ (Z i) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    simp [hZsupport i hi]
  have hWsum : ∑ i ∈ S, μ (W i) = ∑ i, μ (W i) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    simp [hWsupport i hi]
  refine ⟨?_, ?_, (cover_mono hδ hδ1 hh hC).2.2⟩
  · intro i
    exact ⟨(hW i).1, (hW i).2.trans (hC.1 i).2.1, hWsupport i⟩
  · change O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (W i)
    rw [hWsum]
    calc
      _ ≤ (O (t / 2) * O (δ ^ h)) * ∑ i, μ (Y i) := mul_le_mul' hbudget le_rfl
      _ = O (t / 2) * (O (δ ^ h) * ∑ i, μ (Y i)) := mul_assoc _ _ _
      _ ≤ O (t / 2) * ∑ i ∈ S, μ (Z i) := mul_le_mul' le_rfl hC.2.1
      _ = O (t / 2) * ∑ i, μ (Z i) := by rw [hZsum]
      _ ≤ _ := hmass

/-- A mass-retaining refinement of the grain shadings preserves any frozen
stage after accounting for its factor-two transfer loss. -/
theorem state_of_grain_refinement {ω ζ δ h h' ρ a c g t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    {n N L j : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg H' : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hρlow : δ ^ (1 - ω / 100) ≤ ρ) (hg : 0 < g)
    (hB : Broad ω ζ δ h ρ n N v S Z f)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m)
    (hstop : (1 ≤ j → δ ^ ζ * (ρ / δ) * N / n ≤ c) ∧
      (2 ≤ j → ρ ≤ δ ^ (ω / 100)) ∧ (3 ≤ j → g ≤ δ ^ (-ζ)))
    (hH'm : ∀ j, MeasurableSet (H' j)) (hsub : ∀ j, H' j ⊆ Hg j)
    (hretain : O t * ∑ j, μ (Hg j) ≤ ∑ j, μ (H' j))
    (hbudget : O (δ ^ h') ≤ O (t / 2) * O (δ ^ h)) :
    J ω ζ δ h' ρ c n x v Y j := by
  have hbudget' : O (δ ^ h') ≤ O t * O (δ ^ h) :=
    hbudget.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)
  have hmass : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ j, μ (H' j) := by
    calc
      _ = O (δ ^ h') * O (L * a * (ρ * c) * c) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 1
        ring
      _ ≤ (O t * O (δ ^ h)) * O (L * a * (ρ * c) * c) :=
        mul_le_mul' hbudget' le_rfl
      _ = O t * O (δ ^ h * L * a * (ρ * c) * c) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 2
        ring
      _ ≤ O t * ∑ j, μ (Hg j) := mul_le_mul' le_rfl hG.2.2.2.2.2.2.2.1
      _ ≤ _ := hretain
  refine ⟨S, (fun i => Z i ∩ assignedFiber γ H' (f i)), N, y, w, f, a, g,
    cover_of_grain_refinement hδ hδ1 hh ht hC hG hH'm hsub hretain hbudget,
    hρlow, hg, Broad_mono hδ hδ1 hh (broad_restrict_fibres _ hB), ?_, hstop⟩
  exact ⟨L, z, e, H', γ, m, grainWitnesses_of_refinement hG hH'm hsub hmass⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
