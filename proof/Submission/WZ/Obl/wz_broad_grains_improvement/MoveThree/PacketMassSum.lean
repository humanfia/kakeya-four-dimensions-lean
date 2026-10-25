-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketMassSum.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketMassSum.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismPacketEstimate

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open scoped Classical

noncomputable section

/-- Sum packet estimates with a controlled low-density error. Only the
occupied-body duplication and the packet-union overlap enter the bound. -/
theorem packet_mass_sum {ι : Type*} [Fintype ι] (Y : ι → Set V) (U : Set V)
    {K τ C lam N L : ℝ} (mass count : ι → ℝ)
    (hK : 0 ≤ K) (hτ : 0 ≤ τ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hYm : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ U) (hfin : μ U ≠ ⊤)
    (hpacket : ∀ i, K * mass i ≤ (μ (Y i)).toReal + K * τ * count i)
    (hmass : lam * N ≤ ∑ i, mass i)
    (hcount : ∑ i, count i ≤ C * N) (hbudget : 2 * τ * C ≤ lam)
    (hover : ∀ p ∈ U, ((Finset.univ.filter fun i => p ∈ Y i).card : ℝ) ≤ L) :
    O (K * lam * N / 2) ≤ O L * μ U := by
  have hYfin i : μ (Y i) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono (hsub i))
  have hsum : K * (∑ i, mass i) ≤ (∑ i, μ (Y i)).toReal + K * τ * (∑ i, count i) := by
    rw [ENNReal.toReal_sum (fun i _ => hYfin i), Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => hpacket i)
  have hbefore : K * (lam * N) ≤ (∑ i, μ (Y i)).toReal + K * τ * (C * N) :=
    (mul_le_mul_of_nonneg_left hmass hK).trans
      (hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount (mul_nonneg hK hτ))))
  have herr : K * τ * (C * N) ≤ K * lam * N / 2 := by
    have hh := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hK hN)
    nlinarith only [hh]
  have hlower : K * lam * N / 2 ≤ (∑ i, μ (Y i)).toReal := by
    nlinarith only [hbefore, herr]
  have hupper : (∑ i, μ (Y i)) ≤ O L * μ U := by
    have hh := WangZahlLot.Obl.wz_terminal_grains_restoration.sum_measure_le_of_mult_le
      volume Finset.univ Y (fun i _ => hYm i) L
      (by
        intro p hp
        have hpU : p ∈ U := by
          simpa only [Finset.mem_univ, iUnion_true] using
            (show p ∈ U from (iUnion_subset fun i => iUnion_subset fun _ => hsub i) hp)
        exact hover p hpU)
    have hjoin : (⋃ i ∈ (Finset.univ : Finset ι), Y i) ⊆ U :=
      iUnion_subset fun i => iUnion_subset fun _ => hsub i
    exact hh.trans (mul_le_mul' le_rfl (measure_mono hjoin))
  have hfinite : O L * μ U ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr
  exact hlower.trans (ENNReal.toReal_mono hfinite hupper)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
