-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain.SharpMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_fibre_multiplicity_gain.SharpCoarseCount
import Submission.WZ.Obl.wz_move_two_fibre_multiplicity_gain.SlabLower
import Submission.WZ.Obl.wz_tower_depth_step.BalancedCard
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Multiplicity

/-! The low fibre multiplicity case of Move 2, using the quadratic coarse count.

Ported from x0449's `SharpMultiplicity.lean` on o152's branch x0449 (namespace renamed). -/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
  (multiplicity multiplicity_eq_ncard first_alternative_of_refined_multiplicity)

/-- Summing an upper fibre bound over the coarse tubes through a point. -/
lemma cover_multiplicity_upper {δ h ρ M C : ℝ} {n N : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    {S : Finset (Fin n)} {Z : Fin n → Set Space}
    {y w : Fin N → Space} {f : Fin n → Fin N}
    (hM : 0 ≤ M) (hC : Cover δ h n x v Y S Z ρ N y w f)
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hcoarse : ∀ p, (Set.ncard {k | p ∈ Tube ρ (y k) (w k)} : ℝ) ≤ C)
    (hfibre : ∀ k p, (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : ℝ) ≤ M) :
    ∀ p, multiplicity Z p ≤ ENNReal.ofReal (M * C) := by
  intro p
  have hmem (i) (hi : p ∈ Z i) : i ∈ S := by
    by_contra hni
    simpa [(hC.1 i).2.2 hni] using hi
  have hf (k : Fin N) : {i | p ∈ Z i ∧ f i = k} =
      {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
    ext i
    exact ⟨fun hi => ⟨hmem i hi.1, hi.2, hi.1⟩, fun hi => ⟨hi.2.2, hi.2.1⟩⟩
  have hcard := WangZahlLot.Obl.wz_tower_depth_step.card_upper_of_fibres f
    (fun i => p ∈ Z i) (fun k => p ∈ Tube ρ (y k) (w k))
    (fun i hi => hC.2.2.2.1 i (hmem i hi) (hYT i ((hC.1 i).2.1 hi)))
    (fun k _ => by rw [hf k]; exact hfibre k p)
  rw [multiplicity_eq_ncard, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_left (hcoarse p) hM))

/-- The slab condition controls the normalization factor in the volume estimate. -/
lemma slab_power_lower {δ h σ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hA : Admissible δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y) :
    δ ^ h ≤ 8 * ((n : ℝ) * δ) ^ σ := by
  have hslab := one_le_slab_count hδ hA
  have hpow : 0 < δ ^ h := Real.rpow_pos_of_pos hδ h
  have hsmall : δ ^ h ≤ 1 := Real.rpow_le_one hδ.le hδ1 hh
  have hX : δ ^ h / 8 ≤ (n : ℝ) * δ := by
    rw [Real.rpow_neg hδ.le] at hslab
    have h1 : 1 ≤ ((n : ℝ) * δ) * 8 / δ ^ h := by
      calc (1 : ℝ) ≤ (δ ^ h)⁻¹ * n * (8 * δ) := hslab
        _ = ((n : ℝ) * δ) * 8 / δ ^ h := by ring
    rw [le_div_iff₀ hpow] at h1
    linarith
  have hX0 : 0 < δ ^ h / 8 := by positivity
  have h1 : δ ^ h / 8 ≤ ((n : ℝ) * δ) ^ σ := by
    calc δ ^ h / 8 = (δ ^ h / 8) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (δ ^ h / 8) ^ σ :=
        Real.rpow_le_rpow_of_exponent_ge hX0 (by linarith) hσ1
      _ ≤ ((n : ℝ) * δ) ^ σ := Real.rpow_le_rpow hX0.le hX hσ
  linarith

/-- Step 2 of Lemma 8.2, with the `24ω/25` threshold and the `ω/100` gain. -/
theorem quadratic_low_multiplicity_gain {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hω : 0 < ω) :
    ∃ κ h₀ d₀ : ℝ, 0 < κ ∧ 0 < h₀ ∧ 0 < d₀ ∧ ∀ δ h : ℝ,
      0 < δ → δ ≤ d₀ → 0 < h → h ≤ h₀ →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Admissible δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
        ∀ (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
          (y w : Fin N → Space) (f : Fin n → Fin N),
          Cover δ h n x v Y S Z ρ N y w f → δ ^ (ω / 100) ≤ ρ → ρ ≤ 1 →
          (∀ k p, (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : ℝ) ≤
            2 * δ ^ (-(24 * ω / 25))) → Gain σ ω (ω / 100) κ δ n Y := by
  obtain ⟨C, hC, hcoarse⟩ := coarse_point_count_quadratic
  refine ⟨(16 * C)⁻¹, ω / 1000, 1 / 100, by positivity, by positivity, by norm_num, ?_⟩
  intro δ h hδ hδ0 hh hh0 n x v Y hA S Z ρ N y w f hcover hρ hρ1 hcount
  have hδ1 : δ ≤ 1 := hδ0.trans (by norm_num)
  have hρ0 : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans_le hρ
  have htotal := cover_multiplicity_upper (by positivity : 0 ≤ 2 * δ ^ (-(24 * ω / 25)))
    hcover (fun i => (hA.2.1 i).2.2.2)
    (fun p => hcoarse ρ hρ0 hρ1 N y w hcover.2.2.1 hcover.2.2.2.2.2.2.2.1 p) hcount
  have hρpow : δ ^ (ω / 50) ≤ ρ ^ 2 := by
    have he : δ ^ (ω / 50) = (δ ^ (ω / 100)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 1
      ring
    rw [he]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hδ.le _) hρ 2
  have hnorm := slab_power_lower hδ hδ1 hh.le hσ hσ1 hA
  have hid : δ ^ (-(24 * ω / 25)) / δ ^ (ω / 50) =
      δ ^ (-ω + (ω / 50 - h)) * δ ^ h := by
    rw [← Real.rpow_sub hδ, ← Real.rpow_add hδ]
    congr 1
    ring
  have hmult : ∀ p, multiplicity Z p ≤
      ENNReal.ofReal ((16 * C) * δ ^ (-ω + (ω / 50 - h)) * ((n : ℝ) * δ) ^ σ) := by
    intro p
    apply (htotal p).trans
    apply ENNReal.ofReal_le_ofReal
    calc 2 * δ ^ (-(24 * ω / 25)) * (C / ρ ^ 2)
        ≤ 2 * δ ^ (-(24 * ω / 25)) * (C / δ ^ (ω / 50)) := by gcongr
      _ = 2 * C * (δ ^ (-ω + (ω / 50 - h)) * δ ^ h) := by rw [← hid]; ring
      _ ≤ 2 * C * (δ ^ (-ω + (ω / 50 - h)) * (8 * ((n : ℝ) * δ) ^ σ)) := by gcongr
      _ = _ := by ring
  have hmass : ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) :=
    hcover.2.1.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ S))
  exact first_alternative_of_refined_multiplicity hδ hδ1 (by positivity : 0 < 16 * C)
    (by linarith : h + h + ω / 100 ≤ ω / 50 - h) hA.1
    (fun i => (hcover.1 i).1) (fun i => (hcover.1 i).2.1) hA.2.2.2.1 hmass hmult

end WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain
