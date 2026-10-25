-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CoarseSelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CoarseEnlarge

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, CoarseSelect.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O X)
open WangZahlLot.Obl.wz_coarse_grains_assembly
  (rIdx rIdx_mem rIdx_injective rFib rIdx_rFib)

/-- A constant proportion of prism incidence mass lies in coarse tubes
which remain essentially distinct after doubling. Entire prisms survive. -/
theorem select_doubled_coarse {n : ℕ} (D : PrismData n) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hw : ∀ k, ‖D.w k‖ = 1)
    (hX : X ρ D.N D.y D.w)
    (hpos : 0 < ∑ i, ∑ j, volume (D.W i j)) :
    ∃ L N : ℕ, ∃ f : Fin L → Fin D.L, ∃ g : Fin N → Fin D.N,
      ∃ γ : Fin L → Fin N,
        Function.Injective f ∧ Function.Injective g ∧
        (∀ j, g (γ j) = D.γ (f j)) ∧ X (2 * ρ) N (D.y ∘ g) (D.w ∘ g) ∧
        (∑ i, ∑ j, volume (D.W i j)) ≤
          ((10 ^ 40 + 1 : ℕ) : ENNReal) * ∑ i, ∑ j, volume (D.W i (f j)) := by
  classical
  let weight : Fin D.N → ENNReal := fun k =>
    ∑ j ∈ Finset.univ.filter (fun j => D.γ j = k), ∑ i, volume (D.W i j)
  have htotal : ∑ k, weight k = ∑ i, ∑ j, volume (D.W i j) := by
    rw [show (∑ k, weight k) = ∑ j, ∑ i, volume (D.W i j) from
      Finset.sum_fiberwise Finset.univ D.γ (fun j => ∑ i, volume (D.W i j))]
    exact Finset.sum_comm
  obtain ⟨A, _, hA, hmass, hX'⟩ :=
    WangZahlLot.Obl.wz_coarse_grains_assembly.doubled_distinct_selection hρ hρ1 D.y D.w hw hX
      Finset.univ weight (by simpa only [htotal] using hpos)
  let J : Finset (Fin D.L) := Finset.univ.filter (fun j => D.γ j ∈ A)
  let f := rIdx J
  let g := rIdx A
  let γ := fun j : Fin J.card => rFib A hA D.γ (f j)
  have hγ (j : Fin J.card) : g (γ j) = D.γ (f j) :=
    rIdx_rFib A hA D.γ (Finset.mem_filter.mp (rIdx_mem J j)).2
  have hsum : ∑ k ∈ A, weight k = ∑ i, ∑ j, volume (D.W i (f j)) := by
    rw [show (∑ k ∈ A, weight k) = ∑ j ∈ J, ∑ i, volume (D.W i j) from
      Finset.sum_fiberwise_eq_sum_filter Finset.univ A D.γ (fun j => ∑ i, volume (D.W i j))]
    rw [← Finset.sum_coe_sort]
    have he := J.equivFin.symm.sum_comp (fun j : J => ∑ i, volume (D.W i j.val))
    rw [← he]
    exact Finset.sum_comm
  refine ⟨J.card, A.card, f, g, γ, rIdx_injective J, rIdx_injective A, hγ, ?_, ?_⟩
  · intro k k' hne
    exact hX' _ (rIdx_mem A k) _ (rIdx_mem A k') (fun he => hne (rIdx_injective A he))
  · simpa only [htotal, hsum] using hmass

/-- A fixed multiplicative error budget pays for radius doubling, including
whole-fibre separation, density, and the larger broadness interval. -/
theorem double_prism_scale {ω ζ δ h h' ρ c : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h)
    (hβ : 0 ≤ ω * ζ / 100) (hβ1 : ω * ζ / 100 ≤ 1)
    (hρ2 : 2 * ρ ≤ 1) (hc4 : c ≤ 1 / 4)
    (hbudget : ((10 ^ 40 + 1 : ℕ) : ℝ) * δ ^ h' ≤ δ ^ h)
    (hYpos : 0 < ∑ i, volume (Y i))
    (H : D.Valid ω ζ δ h ρ c x v Y 1) :
    ∃ D' : PrismData n, D'.a = D.a ∧ D'.L ≤ D.L ∧
      D'.Valid ω ζ δ h' (2 * ρ) c x v Y 1 := by
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, _, _, hmass, _, _, _, hX, hw, hcover, _⟩
  have hc0 := hδ.trans_le (ha.trans (hab.trans hbc))
  have hρ : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hp : 0 < ∑ i, ∑ j, volume (D.W i j) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h)).ne' hYpos.ne').trans_le hmass
  have hs : D.s = ρ := (hcover (by norm_num)).1
  rw [hs] at hX
  obtain ⟨L, N, f, g, γ, hf, _, hγ, hX', hkeep⟩ :=
    select_doubled_coarse D hρ (by linarith) hw hX hp
  have h2 : 2 * δ ^ h' ≤ δ ^ h := by
    apply le_trans ?_ hbudget
    exact mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hδ.le _)
  have hdensity : (2 : ENNReal) * O (δ ^ h') ≤ O (δ ^ h) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      using ENNReal.ofReal_le_ofReal h2
  have hangular : δ ^ (-h) * (2 : ℝ) ^ (ω * ζ / 100) ≤ δ ^ (-h') := by
    rw [Real.rpow_neg hδ.le, Real.rpow_neg hδ.le]
    have hb := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr (Real.rpow_nonneg hδ.le h))
    rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hδ h).ne'] at hb
    calc
      (δ ^ h)⁻¹ * 2 ^ (ω * ζ / 100) ≤ (δ ^ h)⁻¹ * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
      _ ≤ (δ ^ h')⁻¹ := by
        rw [inv_eq_one_div (δ ^ h')]
        apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ h')).mpr
        nlinarith
  have hmass' : O (δ ^ h') * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (D.W i (f j)) := by
    let C : ENNReal := ((10 ^ 40 + 1 : ℕ) : ENNReal)
    have hC0 : C ≠ 0 := by norm_num [C]
    have hCt : C ≠ ⊤ := by simp [C]
    have hcoeff : C * O (δ ^ h') ≤ O (δ ^ h) := by
      simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        using ENNReal.ofReal_le_ofReal hbudget
    apply (ENNReal.mul_le_mul_iff_left hC0 hCt).mp
    calc
      (O (δ ^ h') * ∑ i, volume (Y i)) * C =
          (C * O (δ ^ h')) * ∑ i, volume (Y i) := by ring
      _ ≤ O (δ ^ h) * ∑ i, volume (Y i) := mul_le_mul' hcoeff le_rfl
      _ ≤ ∑ i, ∑ j, volume (D.W i j) := hmass
      _ ≤ C * ∑ i, ∑ j, volume (D.W i (f j)) := hkeep
      _ = (∑ i, ∑ j, volume (D.W i (f j))) * C := mul_comm _ _
  refine ⟨D.select (2 * ρ) f g γ, rfl, ?_,
    valid_double_selected D hδ hδ1 hh hβ hρ2 hc4 hdensity hangular H f hf g γ hγ hmass' hX'⟩
  simpa only [PrismData.select, Fintype.card_fin] using Fintype.card_le_of_injective f hf

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
