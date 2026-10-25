-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.LowDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/LowDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Statement
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.ThickGrains
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityCut
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (ballDensity ballDensity_measurable ballDensity_mass half_mass_after_loss neighborhood_power_gain)
open WangZahlLot.Obl.wz_move_three_thick_grains_gain
  (scalar_r6 scalar_r8 scalar_eta scalar_nmax scalar_mass)
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

/-- A positive fraction of the fine mass lies at low ball density, unless
the accepted neighborhood estimate already gives the desired power gain.
The density exponent can be chosen below any prescribed positive bound. -/
theorem gain_or_low_ball_density {σ ω b ν₀ : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hb : 0 < b) (hb1 : b ≤ 1) (hν₀ : 0 < ν₀) :
    ∃ ν κ θ d₀ : ℝ, 0 < ν ∧ ν ≤ ν₀ ∧ 0 < κ ∧ 0 < θ ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) →
      O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i, μ (Z i) →
      Gain σ ω κ (b * ω / 2) δ n Y ∨
      ∃ D : Set V, MeasurableSet D ∧
        (1 / 2 : ℝ≥0∞) * ∑ i, μ (Z i) ≤ ∑ i, μ (Z i ∩ D) ∧
        ∀ p ∈ D, μ ((⋃ i, Y i) ∩ ball p (δ ^ (1 - b) / 2)) ≤
          O (δ ^ (6 * ν) * (δ ^ (1 - b) / 2) ^ 3) := by
  obtain ⟨κ, η, d₁, hκ, hη, hd₁, hd₁small, Hgain⟩ :=
    neighborhood_power_gain hσ hσhalf hω hE (b * ω / 8) (by positivity)
  obtain ⟨C₀, hC₀, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  let ν : ℝ := min ν₀ (min η (b * ω / 56))
  have hν : 0 < ν := lt_min hν₀ (lt_min hη (by positivity))
  have hνη : ν ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hνb : ν ≤ b * ω / 56 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨db, hdb, Hb⟩ := exists_rpow_cutoff hb (by norm_num : (0 : ℝ) < 1 / 6)
  obtain ⟨de, hde, He⟩ := exists_rpow_cutoff hη (by norm_num : (0 : ℝ) < 1 / 128)
  obtain ⟨dn, hdn, Hn⟩ := exists_rpow_cutoff (by norm_num : (0 : ℝ) < 196)
    (by positivity : 0 < 1 / C₀)
  obtain ⟨dm, hdm, Hm⟩ := exists_rpow_cutoff (by positivity : 0 < ν / 2)
    (by norm_num : (0 : ℝ) < 1 / 8)
  let d₀ := min (1 / 100) (min d₁ (min db (min de (min dn dm))))
  refine ⟨ν, κ, ν / 4, d₀, hν, min_le_left _ _, hκ, by positivity,
    by dsimp [d₀]; positivity, min_le_left _ _, ?_⟩
  intro δ h hδ hδd hh hhν n x v Y Z hA hZ hretain
  have hd := hδd
  dsimp only [d₀] at hd
  simp only [le_min_iff] at hd
  obtain ⟨hδsmall, hδd₁, hδb, hδe, hδn, hδm⟩ := hd
  have hδ1 : δ ≤ 1 := by linarith
  let r : ℝ := δ ^ (1 - b) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  let U := ⋃ i, Y i
  let D := {p | ballDensity U r p ≤ δ ^ (6 * ν)}
  have hDm : MeasurableSet D := measurableSet_le
    (ballDensity_measurable (MeasurableSet.iUnion fun i => (hA.2.1 i).2.2.1) r) measurable_const
  let W := fun i => Z i \ D
  have hW : ∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i :=
    fun i => ⟨(hZ i).1.diff hDm, sdiff_subset.trans (hZ i).2⟩
  by_cases hhigh : (1 / 2 : ℝ≥0∞) * ∑ i, μ (Z i) ≤ ∑ i, μ (W i)
  · left
    have hδ2 : δ ^ (2 : ℕ) ≤ δ := pow_le_of_le_one hδ.le hδ1 two_ne_zero
    have hr6 : δ ≤ δ ^ (1 - b) / 6 := scalar_r6 hδ (Hb δ hδ hδb)
    have hnmax : (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) :=
      scalar_nmax hδ hC₀ (Nat.cast_pos.mpr hA.1)
        (hpack δ hδ hδsmall n x v (fun i => (hA.2.1 i).1)
          (fun i => (hA.2.1 i).2.1) hA.2.2.1) (Hn δ hδ hδn)
    have hmass : O (δ ^ ν * n * δ ^ 2) ≤ ∑ i, μ (W i) := by
      have hscalar := scalar_mass hδ hδ1 hhν hh (Hm δ hδ hδm)
      have hnd : 0 ≤ (n : ℝ) * δ ^ 2 := by positivity
      calc
        _ ≤ O ((1 / 4 / 2) * (δ ^ h * (δ ^ h * n * δ ^ 2))) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [mul_le_mul_of_nonneg_right hscalar hnd]
        _ = O (1 / 8 : ℝ) * (O (δ ^ h) * O (δ ^ h * n * δ ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ ≤ (1 / 2 : ℝ≥0∞) * (O (δ ^ h) * ∑ i, μ (Y i)) := by
          apply mul_le_mul'
          · norm_num [O, ENNReal.ofReal_div_of_pos]
          · exact mul_le_mul' le_rfl hA.2.2.2.1
        _ ≤ (1 / 2 : ℝ≥0∞) * ∑ i, μ (Z i) := mul_le_mul' le_rfl hretain
        _ ≤ _ := hhigh
    apply Hgain δ h b ν hδ hδ1 hh hb.le hb1 (hδ2.trans hδd₁) hr6
      (scalar_r8 hδ (by linarith) hr6) (scalar_eta hδ hδ1 hνη (He δ hδ hδe))
      (by linarith) n x v Y W hnmax hA hW hmass
    intro i p hp
    have hpD : δ ^ (6 * ν) ≤ ballDensity U r p := le_of_lt (lt_of_not_ge hp.2)
    calc
      _ ≤ O (ballDensity U r p * r ^ 3) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpD (by positivity))
      _ = _ := ballDensity_mass U p hr
  · right
    have hfin : (∑ i, μ (Z i)) ≠ ⊤ := by
      apply ENNReal.sum_ne_top.mpr
      intro i _
      exact ne_top_of_le_ne_top measure_ball_lt_top.ne
        (measure_mono ((hZ i).2.trans ((hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1)))
    have hsplit : (∑ i, μ (Z i)) ≤ (∑ i, μ (Z i ∩ D)) + ∑ i, μ (W i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      exact le_of_eq (measure_inter_add_sdiff (Z i) hDm).symm
    refine ⟨D, hDm, half_mass_after_loss hfin hsplit (le_of_not_ge hhigh), ?_⟩
    intro p hp
    change volume (U ∩ ball p r) ≤ O (δ ^ (6 * ν) * r ^ 3)
    rw [← ballDensity_mass U p hr]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hp (by positivity))

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
