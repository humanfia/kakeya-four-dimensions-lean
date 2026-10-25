-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainBounds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainBounds.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainWitnesses
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainCardinality
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoverSize

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (sum_mass_le_fiber_bound admissible_count_eight closedBall_volume_upper frozen_prism_volume)

noncomputable section

/-- Positive retained mass supplies an actual shaded point, without any slab
condition on the individual coarse fibres. -/
theorem cover_has_shaded_point {δ η m l h ρ : ℝ} (hδ : 0 < δ)
    {n N : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f True) :
    ∃ i ∈ S, ∃ p, p ∈ Z i := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr hA.1
  have hY : 0 < ∑ i, μ (Y i) :=
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < δ ^ η * n * δ ^ 2)).trans_le
      hA.2.2.2.1
  have hcoef : 0 < O (δ ^ h) := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h)
  have hmul : 0 < O (δ ^ h) * ∑ i, μ (Y i) := by positivity
  have hZ : 0 < ∑ i ∈ S, μ (Z i) := hmul.trans_le hC.2.1
  by_contra hh
  push Not at hh
  have hempty : ∀ i ∈ S, Z i = ∅ :=
    fun i hi => Set.eq_empty_iff_forall_notMem.mpr (hh i hi)
  have hzero : ∑ i ∈ S, μ (Z i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hempty i hi]
    exact measure_empty
  rw [hzero] at hZ
  exact lt_irrefl _ hZ

theorem cover_coarse_count {δ η m l h ρ : ℝ} (hδ : 0 < δ)
    {n N : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f True) :
    N ≤ n := by
  classical
  obtain ⟨i, hi, _, _⟩ := cover_has_shaded_point hδ hA hC
  have hsurj : Function.Surjective f := by
    intro k
    obtain ⟨i', _, hi'⟩ :=
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.balanced_fibers_nonempty
        S ⟨i, hi⟩ f (L := δ ^ (-h)) (by
          intro k k'
          simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset] using
            hC.2.2.2.2.2.2.1 k k') k
    exact ⟨i', hi'⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective f hsurj

theorem grain_card_pos {δ η mA l h ρ a c b g : ℝ} (hδ : 0 < δ)
    {n N L : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hA : A δ η mA l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f True)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m) :
    0 < L := by
  obtain ⟨i, hi, p, hp⟩ := cover_has_shaded_point hδ hA hC
  obtain ⟨_, _, _, _, _, _, hunion, _⟩ := hG
  have hpin' : p ∈ {p | ∃ i' ∈ S, f i' = f i ∧ p ∈ Z i'} := ⟨i, hi, rfl, hp⟩
  obtain ⟨j, _, _⟩ := (hunion (f i)).symm.subset hpin'
  exact j.pos

/-- A polynomial grain-count bound using only the weakened retained cover.
In particular, no relative Frostman slab hypothesis is required. -/
theorem grain_card_bound {δ h ρ a c b g : ℝ} (hδ : 0 < δ)
    {n N L : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m) :
    (L : ℝ) ≤ 64 * δ ^ (-(2 * h + 5)) := by
  obtain ⟨hda, hab, hbc, _, hgeom, hdisj, hunion, hmass, _⟩ := hG
  have hball : ∀ j, Hg j ⊆ ball (0 : V) 1 := by
    intro j p hp
    have hf : p ∈ {p | ∃ j', γ j' = γ j ∧ p ∈ Hg j'} := ⟨j, rfl, hp⟩
    obtain ⟨i, _, _, hpi⟩ := (hunion (γ j)).subset hf
    exact (hA.2.1 i).2.1 ((hA.2.1 i).2.2.2 ((hC.1 i).2.1 hpi))
  have hmassup : (∑ j, μ (Hg j)) ≤ O (8 * n) := by
    apply (sum_mass_le_fiber_bound γ Hg (fun j => (hgeom j).1) hdisj
      (ball (0 : V) 1) hball (by norm_num : (0 : ℝ) ≤ 8)
      ((measure_mono ball_subset_closedBall).trans (by
        simpa using closedBall_volume_upper (0 : V) (by norm_num : (0 : ℝ) ≤ 1)))).trans
    apply ENNReal.ofReal_le_ofReal
    have hN : (N : ℝ) ≤ n := Nat.cast_le.mpr (cover_coarse_count hδ hA hC)
    nlinarith
  have ha : 0 < a := hδ.trans_le hda
  have hrc : 0 < ρ * c := ha.trans_le hab
  have hc : 0 < c := hrc.trans_le hbc
  have hv : δ ^ 3 ≤ a * (ρ * c) * c := by
    calc
      _ = δ * δ * δ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hda (hda.trans hab) hδ.le ha.le)
        (hda.trans (hab.trans hbc)) hδ.le (by positivity)
  have hreal : δ ^ h * L * (a * (ρ * c) * c) ≤ 8 * n := by
    have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ 8 * n)).mp
      (hmass.trans hmassup)
    nlinarith
  have hlow : δ ^ h * L * δ ^ 3 ≤ 8 * n :=
    (mul_le_mul_of_nonneg_left hv (by positivity)).trans hreal
  have hn := admissible_count_eight hδ hA
  have hscale : δ ^ h * L * δ ^ 5 ≤ 64 * δ ^ (-h) := by
    nlinarith [mul_le_mul_of_nonneg_right hlow (sq_nonneg δ)]
  have hpow : δ ^ h * δ ^ 5 = δ ^ (h + 5) := by
    rw [Real.rpow_add hδ, Real.rpow_ofNat]
  have hdiv : (L : ℝ) ≤ (64 * δ ^ (-h)) / δ ^ (h + 5) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr
    nlinarith [hpow]
  convert hdiv using 1
  rw [div_eq_mul_inv, ← Real.rpow_neg hδ.le, mul_assoc, ← Real.rpow_add hδ]
  congr 2
  ring

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
