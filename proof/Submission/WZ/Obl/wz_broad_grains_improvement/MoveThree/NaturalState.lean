-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NaturalState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NaturalState.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalPackets
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinement
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainBounds

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (assignedFiber assignedFiber_mono boxAxis)

noncomputable section

/-- Selecting a natural anchor in every packet preserves the full frozen
state, subject only to the displayed inverse-palette power budget. -/
theorem natural_packet_state {ω ζ δ h h' ρ a c g s : ℝ} {A : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (hA : 1 ≤ A)
    (hs : 0 < s) (hsA : s ≤ A * (a / ρ / c))
    {n N L K : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hAdm : WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hB : Broad ω ζ δ h ρ n N v S Z f)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m)
    (q : Fin L → Fin K) (ref : Fin K → Fin L) (href : ∀ k, q (ref k) = k)
    (hgeom : ∀ i j, q i = q j →
      ‖boxAxis (e i) 0 - boxAxis (e j) 0‖ ≤ s / 100 ∧
      ‖z i - z j‖ ≤ c / 100 ∧
      |inner ℝ (boxAxis (e j) 0) (z i - z j)| ≤ s * c / 100)
    (hdisj : ∀ k l, k ≠ l → Disjoint (assignedFiber q Hg k) (assignedFiber q Hg l))
    (hbudget : δ ^ h' ≤
      (((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ))⁻¹ / 2) * δ ^ h) :
    ∃ (H' : Fin L → Set V) (r : Fin K → Fin L),
      (∀ j, MeasurableSet (H' j) ∧ H' j ⊆ Hg j) ∧
      (∀ j, H' j ≠ ∅ → grainNear a ρ c z e (r (q j)) j) ∧
      (∀ k l, k ≠ l → Disjoint (assignedFiber q H' k) (assignedFiber q H' l)) ∧
      C δ h' n x v Y S (fun i => Z i ∩ assignedFiber γ H' (f i)) ρ N y w f True ∧
      Broad ω ζ δ h' ρ n N v S (fun i => Z i ∩ assignedFiber γ H' (f i)) f ∧
      GrainWitnesses δ h' n x v S (fun i => Z i ∩ assignedFiber γ H' (f i))
        ρ N y w f a c 0 g L z e H' γ m := by
  classical
  have ha : 0 < a := hδ.trans_le hG.1
  have hrc : 0 < ρ * c := ha.trans_le hG.2.1
  have hc : 0 < c := hrc.trans_le hG.2.2.1
  have hρ : 0 < ρ := (mul_pos_iff_of_pos_right hc).mp hrc
  let M : ℕ := (128 * A ^ 2 + 1) ^ 6
  have hM : 0 < M := by dsimp [M]; positivity
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨anchor, hanchor, hcover⟩ := confined_packet_anchors
    (grain_card_pos hδ hAdm hC hG) hA ha hρ hc hG.2.1 hs hsA q ref href z e hgeom
  obtain ⟨Q, r, hmass, hnear⟩ := select_natural_packet_color hM q z e Hg anchor hcover
  let H' := selectGrains Q Hg
  have hH' (j : Fin L) : MeasurableSet (H' j) ∧ H' j ⊆ Hg j := by
    by_cases hj : j ∈ Q
    · simpa only [H', selectGrains, if_pos hj] using
        And.intro (hG.2.2.2.2.1 j).1 (Subset.rfl : Hg j ⊆ Hg j)
    · simp [H', selectGrains, hj]
  have hretain : O ((M : ℝ)⁻¹) * ∑ j, μ (Hg j) ≤ ∑ j, μ (H' j) := by
    rw [show (∑ j, μ (H' j)) = ∑ j ∈ Q, μ (Hg j) from selectGrains_mass Q Hg]
    calc
      _ ≤ O ((M : ℝ)⁻¹) * ((M : ENNReal) * ∑ j ∈ Q, μ (Hg j)) :=
        mul_le_mul' le_rfl hmass
      _ = _ := by
        rw [← ENNReal.ofReal_natCast M, ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hMr.le), inv_mul_cancel₀ hMr.ne']
        simp only [ENNReal.ofReal_one, one_mul]
  have hbudgetE : O (δ ^ h') ≤ O ((M : ℝ)⁻¹ / 2) * O (δ ^ h) := by
    exact (ENNReal.ofReal_le_ofReal hbudget).trans_eq (ENNReal.ofReal_mul (by positivity))
  have hbudget' : O (δ ^ h') ≤ O ((M : ℝ)⁻¹) * O (δ ^ h) :=
    hbudgetE.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith [inv_nonneg.mpr hMr.le])) le_rfl)
  have hdensity : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ j, μ (H' j) := by
    calc
      _ = O (δ ^ h') * O (L * a * (ρ * c) * c) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]; congr 1; ring
      _ ≤ (O ((M : ℝ)⁻¹) * O (δ ^ h)) * O (L * a * (ρ * c) * c) :=
        mul_le_mul' hbudget' le_rfl
      _ = O ((M : ℝ)⁻¹) * O (δ ^ h * L * a * (ρ * c) * c) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]; congr 2; ring
      _ ≤ O ((M : ℝ)⁻¹) * ∑ j, μ (Hg j) := mul_le_mul' le_rfl hG.2.2.2.2.2.2.2.1
      _ ≤ _ := hretain
  refine ⟨H', r, hH', ?_, ?_,
    cover_of_grain_refinement hδ hδ1 hh (inv_nonneg.mpr hMr.le) hC hG
      (fun j => (hH' j).1) (fun j => (hH' j).2) hretain hbudgetE,
    Broad_mono hδ hδ1 hh (broad_restrict_fibres _ hB),
    grainWitnesses_of_refinement hG (fun j => (hH' j).1) (fun j => (hH' j).2) hdensity⟩
  · intro j hj
    apply hnear j
    by_contra h
    exact hj (by simp [H', selectGrains, h])
  · intro k l hkl
    exact (hdisj k l hkl).mono (assignedFiber_mono q (fun j => (hH' j).2) k)
      (assignedFiber_mono q (fun j => (hH' j).2) l)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
