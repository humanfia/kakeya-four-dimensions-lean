-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.StateSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/StateSelection.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainSelection
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenBridge

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber assignedFiber_eq_supported fine_level_of_UF)

noncomputable section

/-- The cover survives selection of whole grains. A fraction `t` of the grain
mass retains at least `t / 2` of the fine mass, because the fine multiplicity
lies in one common factor-two interval. -/
theorem cover_of_grain_selection {δ h h' ρ a c b g t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (Q : Finset (Fin L))
    (hretain : O t * ∑ j, μ (Hg j) ≤ ∑ j ∈ Q, μ (Hg j))
    (hbudget : O (δ ^ h') ≤ O (t / 2) * O (δ ^ h)) :
    C δ h' n x v Y S
      (fun i => Z i ∩ assignedFiber γ (selectGrains Q Hg) (f i))
      ρ N y w f True := by
  classical
  obtain ⟨_, _, _, _, hgeom, hdisj, hunion, _, hmult, _, _, _⟩ := hG
  have hZsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  have hselected : ∀ j, MeasurableSet (selectGrains Q Hg j) := by
    intro j
    by_cases hj : j ∈ Q <;> simp [selectGrains, hj, (hgeom j).1]
  have hsubset : ∀ j, selectGrains Q Hg j ⊆ Hg j := by
    intro j p hp
    exact ((mem_selectGrains Q Hg j p).mp hp).2
  have hfib : ∀ k, assignedFiber γ Hg k = assignedFiber f Z k := by
    intro k
    rw [assignedFiber_eq_supported f hZsupport k]
    exact hunion k
  obtain ⟨m', hm', hlevel⟩ := fine_level_of_UF hZsupport ⟨m, hmult⟩
  have hretain' : O t * ∑ j, μ (Hg j) ≤ ∑ j, μ (selectGrains Q Hg j) := by
    rwa [selectGrains_mass]
  obtain ⟨hW, hmass, _⟩ := grain_refinement_transfer_full f γ Z Hg
    (selectGrains Q Hg) hm' ht (fun i => (hC.1 i).1)
    (fun j => (hgeom j).1) hselected hsubset hdisj hfib hlevel hretain'
  let W := fun i => Z i ∩ assignedFiber γ (selectGrains Q Hg) (f i)
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
      _ ≤ (O (t / 2) * O (δ ^ h)) * ∑ i, μ (Y i) :=
        mul_le_mul' hbudget le_rfl
      _ = O (t / 2) * (O (δ ^ h) * ∑ i, μ (Y i)) := mul_assoc _ _ _
      _ ≤ O (t / 2) * ∑ i ∈ S, μ (Z i) := mul_le_mul' le_rfl hC.2.1
      _ = O (t / 2) * ∑ i, μ (Z i) := by rw [hZsum]
      _ ≤ _ := hmass

/-- Retaining a fraction of total grain mass also retains aggregate density:
the number of selected grains never exceeds the original number. -/
theorem grain_selection_density {δ h h' ρ a c b g t : ℝ} (hδ : 0 < δ)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (Q : Finset (Fin L))
    (hretain : O t * ∑ j, μ (Hg j) ≤ ∑ j ∈ Q, μ (Hg j))
    (hbudget : O (δ ^ h') ≤ O t * O (δ ^ h)) :
    O (δ ^ h' * Q.card * a * (ρ * c) * c) ≤ ∑ j ∈ Q, μ (Hg j) := by
  obtain ⟨hda, hab, hbc, _, _, _, _, hmass, _, _, _, _⟩ := hG
  have ha : 0 ≤ a := hδ.le.trans hda
  have hrc : 0 ≤ ρ * c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  have hcard : Q.card ≤ L := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ Q)
  have hnum : O (Q.card * a * (ρ * c) * c) ≤ O (L * a * (ρ * c) * c) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr
  calc
    _ = O (δ ^ h') * O (Q.card * a * (ρ * c) * c) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
      congr 1
      ring
    _ ≤ (O t * O (δ ^ h)) * O (L * a * (ρ * c) * c) :=
      mul_le_mul' hbudget hnum
    _ = O t * O (δ ^ h * L * a * (ρ * c) * c) := by
      rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
      congr 2
      ring
    _ ≤ O t * ∑ j, μ (Hg j) := mul_le_mul' le_rfl hmass
    _ ≤ _ := hretain

/-- A selected subfamily inherits any local convex-count bound of the original
grains. This does not require measurability or disjointness of the containers. -/
theorem grain_selection_count {δ h ρ a c b g : ℝ} (hδ : 0 < δ)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (Q : Finset (Fin L)) :
    ∀ j ∈ Q, ∀ W, Convex ℝ W →
      O (q L {j' | j' ∈ Q ∧
        P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O g * μ W := by
  obtain ⟨hda, hab, hbc, _, _, _, _, _, _, _, _, hcount⟩ := hG
  have ha : 0 ≤ a := hδ.le.trans hda
  have hrc : 0 ≤ ρ * c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  intro j _ W hW
  apply le_trans _ (hcount j W hW)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Nat.cast_le.mpr (Set.ncard_le_ncard (fun _ hp => hp.2))

/-- A whole-grain selection with a small local convex count supplies the
terminal stage on the same fine family and the same scales. -/
theorem stage_three_of_grain_selection {ω ζ δ h h' ρ a c g g' t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hρlow : δ ^ (1 - ω / 100) ≤ ρ)
    (hB : Broad ω ζ δ h ρ n N v S Z f)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m)
    (hlen : δ ^ ζ * (ρ / δ) * N / n ≤ c) (hρup : ρ ≤ δ ^ (ω / 100))
    (Q : Finset (Fin L)) (hg' : 0 < g') (hg'small : g' ≤ δ ^ (-ζ))
    (hretain : O t * ∑ j, μ (Hg j) ≤ ∑ j ∈ Q, μ (Hg j))
    (hbudget : O (δ ^ h') ≤ O (t / 2) * O (δ ^ h))
    (hmass : O (δ ^ h' * Q.card * a * (ρ * c) * c) ≤ ∑ j ∈ Q, μ (Hg j))
    (hcount : ∀ j ∈ Q, ∀ W, Convex ℝ W →
      O (q L {j' | j' ∈ Q ∧
        P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O g' * μ W) :
    J ω ζ δ h' ρ c n x v Y 3 := by
  refine ⟨S, (fun i => Z i ∩ assignedFiber γ (selectGrains Q Hg) (f i)),
    N, y, w, f, a, g',
    cover_of_grain_selection hδ hδ1 hh ht hC hG Q hretain hbudget,
    hρlow, hg', ?_, grains_of_selection hδ hG Q hmass hcount, ?_⟩
  · exact Broad_mono hδ hδ1 hh (broad_restrict_fibres _ hB)
  · exact ⟨fun _ => hlen, fun _ => hρup, fun _ => hg'small⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
