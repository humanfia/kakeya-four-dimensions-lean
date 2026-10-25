-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PlanePackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PlanePackets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketDisjoint
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainBounds
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenPackets

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber frozen_narrow_packets geometricPacketOverlap active_packet_count
   coarseLinear dualLinear boxAxis boxAxis_norm)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd)

noncomputable section

/-- The packet geometry needed to place a narrow grain family in flat
containers. The assignment is onto and the refined packet shadings are disjoint. -/
theorem plane_narrow_grain_packets {ω ζ δ h h' ρ a c g s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h')
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ s * c)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hB : Broad ω ζ δ h ρ n N v S Z f)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m)
    (hnarrow : ∀ i j p, p ∈ Hg i → p ∈ Hg j →
      s = 1 ∨ pd (boxAxis (e i) 0) (boxAxis (e j) 0) ≤ s)
    (hbudget : δ ^ h' ≤ ((geometricPacketOverlap : ℝ)⁻¹ / 2) * δ ^ h) :
    ∃ (K : ℕ) (q : Fin L → Fin K) (ref : Fin K → Fin L) (H' : Fin L → Set V),
      (∀ k, q (ref k) = k) ∧
      (∀ i j, q i = q j →
        ‖boxAxis (e i) 0 - boxAxis (e j) 0‖ ≤ s / 100 ∧
        1 / 2 ≤ |inner ℝ (boxAxis (e j) 2) (boxAxis (e i) 2)| ∧
        ‖z i - z j‖ ≤ c / 100 ∧
        |inner ℝ (boxAxis (e j) 0) (z i - z j)| ≤ s * c / 100) ∧
      (∀ j, MeasurableSet (H' j) ∧ H' j ⊆ Hg j) ∧
      O ((geometricPacketOverlap : ℝ)⁻¹) * ∑ j, μ (Hg j) ≤ ∑ j, μ (H' j) ∧
      (∀ k l, k ≠ l → Disjoint (assignedFiber q H' k) (assignedFiber q H' l)) ∧
      C δ h' n x v Y S (fun i => Z i ∩ assignedFiber γ H' (f i)) ρ N y w f True ∧
      Broad ω ζ δ h' ρ n N v S (fun i => Z i ∩ assignedFiber γ H' (f i)) f ∧
      GrainWitnesses δ h' n x v S (fun i => Z i ∩ assignedFiber γ H' (f i))
        ρ N y w f a c 0 g L z e H' γ m := by
  have ha : 0 < a := hδ.trans_le hG.1
  have hrc : 0 < ρ * c := ha.trans_le hG.2.1
  have hc : 0 < c := hrc.trans_le hG.2.2.1
  have hρ : 0 < ρ := (mul_pos_iff_of_pos_right hc).mp hrc
  have hρ1 : ρ ≤ 1 := by nlinarith [hG.2.2.1]
  have hcoarse (p : V) : coarseLinear 1 p = p := by
    ext i
    fin_cases i <;> simp [coarseLinear, WangZahlLot.Obl.wz_flat_factored_improvement.diagonalMap_apply]
  have hdual (p : V) : dualLinear 1 p = p := by
    ext i
    fin_cases i <;> simp [dualLinear, WangZahlLot.Obl.wz_flat_factored_improvement.diagonalMap_apply]
  have hunit (p : V) (hp : ‖p‖ = 1) :
      WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit (dualLinear 1 p) = p := by
    simp only [hdual, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit, hp, inv_one, one_smul]
  obtain ⟨K, q, ref, href, hclose, hactive⟩ := frozen_narrow_packets
    (by norm_num : (0 : ℝ) < 1) le_rfl hρ hρ1 ha hG.2.1 hc hs hs1
    (by simpa only [one_mul] using has) z e Hg
    (by intro j; rw [hcoarse, boxAxis_norm]; norm_num)
    (fun j => (hG.2.2.2.2.1 j).2.1) (by
      intro i j p hi hj
      simpa only [hunit _ (boxAxis_norm _ _)] using hnarrow i j p hi hj)
  have hK : 0 < K := (Nat.zero_le (q ⟨0, grain_card_pos hδ hA hC hG⟩).val).trans_lt
    (q ⟨0, grain_card_pos hδ hA hC hG⟩).isLt
  have hP : (0 : ℝ) < geometricPacketOverlap := by norm_num [geometricPacketOverlap]
  obtain ⟨H', hH', hmass, hpoint, hdisj⟩ := disjoint_packet_refinement hK hP q Hg
    (fun j => (hG.2.2.2.2.1 j).1) (by
      intro p
      simpa only [active_packet_count] using hactive p)
  have hbudget' : δ ^ h' ≤ (geometricPacketOverlap : ℝ)⁻¹ * δ ^ h :=
    hbudget.trans (mul_le_mul_of_nonneg_right
      (by linarith [inv_nonneg.mpr hP.le]) (Real.rpow_nonneg hδ.le _))
  have hdensity : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ j, μ (H' j) := by
    calc
      _ ≤ O (((geometricPacketOverlap : ℝ)⁻¹ * δ ^ h) * L * a * (ρ * c) * c) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr
      _ = O ((geometricPacketOverlap : ℝ)⁻¹) * O (δ ^ h * L * a * (ρ * c) * c) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hP.le)]
        congr 1
        ring
      _ ≤ O ((geometricPacketOverlap : ℝ)⁻¹) * ∑ j, μ (Hg j) :=
        mul_le_mul' le_rfl hG.2.2.2.2.2.2.2.1
      _ ≤ _ := hmass
  refine ⟨K, q, ref, H', href, ?_, hH', hmass, hdisj,
    cover_of_grain_refinement hδ hδ1 hh (inv_nonneg.mpr hP.le)
      hC hG (fun j => (hH' j).1) (fun j => (hH' j).2) hmass
      ((ENNReal.ofReal_le_ofReal hbudget).trans_eq (ENNReal.ofReal_mul (by positivity))),
    Broad_mono hδ hδ1 hh (broad_restrict_fibres _ hB),
    grainWitnesses_of_refinement hG (fun j => (hH' j).1) (fun j => (hH' j).2) hdensity⟩
  intro i j hij
  simpa only [hunit _ (boxAxis_norm _ _), hcoarse] using hclose i j hij

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
