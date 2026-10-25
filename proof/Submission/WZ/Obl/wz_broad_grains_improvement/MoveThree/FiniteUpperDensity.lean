-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FiniteUpperDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FiniteUpperDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FiniteBadSets
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ScaleDensityGain
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CommonCutMass

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (shadingMeasure shadingMeasure_apply shadingMeasure_univ ballDensity
    ballDensity_measurable ballDensity_mass)

noncomputable section

/-- A finite family of density bounds can be imposed while losing only a
prescribed fraction of grain mass, unless one radius already gives a gain. -/
theorem grain_finite_density_cut {σ ω δ h ν t loss κ : ℝ}
    (hδ : 0 < δ) (hloss : 0 ≤ loss) {k : ℕ} (hk : 0 < k)
    (r : Fin k → ℝ) (hr : ∀ j, 0 < r j)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {ρ a c b g : ℝ} {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hg : Fin L → Set V} {γ : Fin L → Fin N} {m : ℝ}
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (hbudget : δ ^ ν ≤ loss / (2 * k) * δ ^ (2 * h))
    (hgain : ∀ j (W : Fin n → Set V),
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) →
      O (δ ^ ν * n * δ ^ 2) ≤ ∑ i, μ (W i) →
      (∀ i p, p ∈ W i → O (δ ^ (-t) * (δ / r j) ^ (ω + σ) * (r j) ^ 3) ≤
        μ ((⋃ i, Y i) ∩ ball p (r j))) → Gain σ ω κ (t / 2) δ n Y) :
    Gain σ ω κ (t / 2) δ n Y ∨
      ∃ Γ : Set V, MeasurableSet Γ ∧
        (∑ j, μ (Hg j \ Γ)) ≤ O loss * ∑ j, μ (Hg j) ∧
        ∀ p ∈ Γ, ∀ j, μ ((⋃ i, Y i) ∩ ball p (r j)) ≤
          O (δ ^ (-t) * (δ / r j) ^ (ω + σ) * (r j) ^ 3) := by
  classical
  let U := ⋃ i, Y i
  let B : Fin k → Set V := fun j =>
    {p | δ ^ (-t) * (δ / r j) ^ (ω + σ) < ballDensity U (r j) p}
  have hB j : MeasurableSet (B j) := measurableSet_lt measurable_const
    (ballDensity_measurable (MeasurableSet.iUnion fun i => (hA.2.1 i).2.2.1) (r j))
  rcases finite_bad_set_loss (shadingMeasure Hg) hk B loss with hbad | hsmall
  · obtain ⟨j, hj⟩ := hbad
    rw [shadingMeasure_univ, shadingMeasure_apply Hg (hB j)] at hj
    have hmass := grain_common_cut_fine_mass (div_nonneg hloss (Nat.cast_nonneg k)) hC hG (hB j) hj
    have hZsum : ∑ i ∈ S, μ (Z i) = ∑ i, μ (Z i) := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      simp [(hC.1 i).2.2 hi]
    have hsource : O (δ ^ (2 * h) * n * δ ^ 2) ≤ ∑ i, μ (Z i) := by
      calc
        _ = O (δ ^ h) * O (δ ^ h * n * δ ^ 2) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
          congr 1
          rw [show 2 * h = h + h by ring, Real.rpow_add hδ]
          ring
        _ ≤ O (δ ^ h) * ∑ i, μ (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
        _ ≤ ∑ i ∈ S, μ (Z i) := hC.2.1
        _ = _ := hZsum
    left
    apply hgain j (fun i => Z i ∩ B j)
      (fun i => ⟨(hC.1 i).1.inter (hB j), inter_subset_left.trans (hC.1 i).2.1⟩)
    · apply le_trans _ hmass
      calc
        _ ≤ O ((loss / (2 * k) * δ ^ (2 * h)) * n * δ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr
        _ = O (loss / k / 2) * O (δ ^ (2 * h) * n * δ ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ loss / k / 2)]
          congr 1
          ring
        _ ≤ _ := mul_le_mul' le_rfl hsource
    · intro i p hp
      apply le_trans _ (ballDensity_mass U p (hr j)).le
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (le_of_lt hp.2) (pow_nonneg (hr j).le 3)
  · right
    let Γ := (⋃ j, B j)ᶜ
    have hΓ : MeasurableSet Γ := (MeasurableSet.iUnion hB).compl
    refine ⟨Γ, hΓ, ?_, ?_⟩
    · rw [shadingMeasure_univ, shadingMeasure_apply Hg (MeasurableSet.iUnion hB)] at hsmall
      convert hsmall using 1
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ext p
      simp [Γ]
    · intro p hp j
      have hh : ballDensity U (r j) p ≤ δ ^ (-t) * (δ / r j) ^ (ω + σ) := by
        apply le_of_not_gt
        intro hh
        exact hp (mem_iUnion.mpr ⟨j, hh⟩)
      change volume (U ∩ ball p (r j)) ≤ _
      rw [← ballDensity_mass U p (hr j)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hh (pow_nonneg (hr j).le 3))

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
