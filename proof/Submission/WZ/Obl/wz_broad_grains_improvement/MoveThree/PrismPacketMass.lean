-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PrismPacketMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PrismPacketMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismPacketEstimate
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PackingRestriction
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyDensity
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyEstimate BodyConvexCount BodyPacking)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (body_convex_count_restrict)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_mem enumerate_injective)

noncomputable section

/-- A packet estimate with an explicit error for low-density bodies. The
error is linear in the occupied body count, so bounded duplication controls
its total over all angular labels. -/
theorem sharp_prism_packet_mass {σ ω : ℝ} (hbody : BodyEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (n : ℕ) (U Y : Fin n → Set V) (x : Fin n → V) (a b r w m p : ℝ),
      (n : ℝ) ≤ d ^ (-100 : ℝ) →
      0 < a → a ≤ b → b ≤ 4 → 0 < r → d ≤ r / 4 → 0 < w →
      d ≤ r / (8192 * a) → 1 ≤ m → 1 ≤ p →
      (∀ i, IsCompact (U i)) → (∀ i, Convex ℝ (U i)) →
      (∀ i, ball (x i) r ⊆ U i) →
      (∀ i, ∃ q ∈ U i, ∃ q' ∈ U i, (1 / 4 : ℝ) ≤ dist q q') →
      (∀ i, μ (U i) = O w) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      BodyConvexCount U w m → BodyPacking U w p →
      ∀ z e, (∀ i, U i ⊆ P a b 4 z e) →
      let K := A * d ^ ε * (r / (8192 * a)) ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) *
        (w / (4 * a * b)) ^ (σ / 2)
      K * (∑ i, μ (Y i)).toReal ≤ (μ (⋃ i, Y i)).toReal + K * d ^ η * w * n := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hsmall, H⟩ := sharp_prism_packet_estimate hbody ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hsmall, ?_⟩
  intro d hd hdd n U Y x a b r w m p hnmax ha hab hb hr hdr hw hdB hm hp
    hcompact hconvex hball hlong hvolume hYm hYU hcount hpack z e hbox
  classical
  let K := A * d ^ ε * (r / (8192 * a)) ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) *
    (w / (4 * a * b)) ^ (σ / 2)
  change K * (∑ i, μ (Y i)).toReal ≤ (μ (⋃ i, Y i)).toReal + K * d ^ η * w * n
  have hbpos : 0 < b := ha.trans_le hab
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hppos : 0 < p := zero_lt_one.trans_le hp
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hYbound i : μ (Y i) ≤ O w := by rw [← hvolume i]; exact measure_mono (hYU i)
  have hYfin i : μ (Y i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hYbound i)
  have hfin : μ (⋃ i, Y i) ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i)) (measure_iUnion_fintype_le _ _)
  have hYR i : (μ (Y i)).toReal ≤ w := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hYbound i)
    simpa only [O, ENNReal.toReal_ofReal hw.le] using hh
  let S := Finset.univ.filter fun i => d ^ η * w ≤ (μ (Y i)).toReal
  have hSbound : K * w * (S.card : ℝ) ≤ (μ (⋃ i, Y i)).toReal := by
    by_cases hS : S.Nonempty
    · let f := enumerate S
      have hf : Function.Injective f := enumerate_injective S
      have hfdense i : O (d ^ η) * μ (U (f i)) ≤ μ (Y (f i)) := by
        rw [hvolume, ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le η)]
        apply (ENNReal.ofReal_le_iff_le_toReal (hYfin (f i))).mpr
        exact (Finset.mem_filter.mp (enumerate_mem S i)).2
      have hSn : S.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
      have hkn : (S.card : ℝ) ≤ d ^ (-100 : ℝ) := (Nat.cast_le.mpr hSn).trans hnmax
      have hh := H d hd hdd S.card (U ∘ f) (Y ∘ f) (x ∘ f) a b r w m p
        (Finset.card_pos.mpr hS) hkn ha hab hb hr hdr hw hdB hm hp
        (fun i => hcompact (f i)) (fun i => hconvex (f i)) (fun i => hball (f i))
        (fun i => hlong (f i)) (fun i => hvolume (f i)) (fun i => hYm (f i))
        (fun i => hYU (f i)) hfdense (body_convex_count_restrict hw.le hcount f hf)
        (packing_restrict hw.le hpack f hf) z e (fun i => hbox (f i))
      apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
      exact hh.trans (measure_mono (iUnion_subset fun i => subset_iUnion Y (f i)))
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.cast_zero, mul_zero]
      exact ENNReal.toReal_nonneg
  have hsum : (∑ i, μ (Y i)).toReal ≤ (S.card : ℝ) * w + n * (d ^ η * w) := by
    rw [ENNReal.toReal_sum (fun i _ => hYfin i)]
    calc
      _ ≤ ∑ i, ((if i ∈ S then w else 0) + d ^ η * w) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ S
        · simp only [ite_eq_left hi]
          exact (hYR i).trans (le_add_of_nonneg_right (by positivity))
        · have hh : (μ (Y i)).toReal < d ^ η * w := by
            simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hi
          simpa only [ite_eq_right hi, zero_add] using hh.le
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite_mem]
  calc
    _ ≤ K * ((S.card : ℝ) * w + n * (d ^ η * w)) := mul_le_mul_of_nonneg_left hsum hK
    _ = K * w * S.card + K * d ^ η * w * n := by ring
    _ ≤ _ := add_le_add hSbound le_rfl

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
