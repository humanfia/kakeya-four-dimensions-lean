-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.Cut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.UniformCut

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, Cut.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O q P bodyCount)

def PrismData.cut {n : ℕ} (D : PrismData n) (C : Fin D.L → Set V) : PrismData n :=
  { D with W := fun i j => D.W i j ∩ C j }

/-- All structural fields survive a common cut in each prism. Only the
two quantitative measure inequalities need to be supplied separately. -/
theorem valid_cut {ω ζ δ h h' ρ c : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h')
    (H : D.Valid ω ζ δ h ρ c x v Y 1)
    (C : Fin D.L → Set V) (hCm : ∀ j, MeasurableSet (C j))
    (hmass : O (δ ^ h') * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (D.W i j ∩ C j))
    (hdense : ∀ j, O (δ ^ h') * volume (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      volume (⋃ i, D.W i j ∩ C j)) :
    (D.cut C).Valid ω ζ δ h' ρ c x v Y 1 := by
  rcases H with ⟨ha, hab, hbc, hc, hW, _, _, hcross, hbroad, hX, hw, hcover, _⟩
  dsimp only [PrismData.cut, PrismData.Valid]
  refine ⟨ha, hab, hbc, hc, ?_, hmass, hdense, ?_, ?_, hX, hw, hcover, by norm_num⟩
  · intro i j
    exact ⟨(hW i j).1.inter (hCm j), inter_subset_left.trans (hW i j).2.1,
      fun j' hne => ((hW i j).2.2 j' hne).mono inter_subset_left inter_subset_left⟩
  · intro i j hnon
    exact hcross i j (hnon.mono inter_subset_left)
  · intro j p u r hu hdr hrρ
    by_cases hp : p ∈ C j
    · have hc0 : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
      have hρ0 : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
        (by intro h; linarith [h.2]) |>.1
      have hn := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh)
      have hb := (hbroad j p u r hu hdr hrρ).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hn
            (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ0.le) _))
          (Nat.cast_nonneg _))
      simpa only [mem_inter_iff, hp, and_true] using hb
    · simp [hp, q]

theorem valid_uniform_cut {ω ζ δ h h' ρ c t : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h') (ht : 0 ≤ t)
    (hbudget : O (δ ^ h') ≤ O (t / 2) * O (δ ^ h))
    (H : D.Valid ω ζ δ h ρ c x v Y 1)
    (C : Fin D.L → Set V) (hCm : ∀ j, MeasurableSet (C j))
    (hCH : ∀ j, C j ⊆ ⋃ i, D.W i j)
    (m : Fin D.L → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hlevel : ∀ j p, p ∈ ⋃ i, D.W i j →
      m j ≤ bodyCount (fun i => D.W i j) p ∧
        bodyCount (fun i => D.W i j) p ≤ 2 * m j)
    (hretain : ∀ j, O t * volume (⋃ i, D.W i j) ≤ volume (C j)) :
    (D.cut C).Valid ω ζ δ h' ρ c x v Y 1 ∧
      ∀ j, (⋃ i, (D.cut C).W i j) = C j := by
  have Hcopy := H
  rcases Hcopy with ⟨_, _, _, _, hW, hmass, hdense, _⟩
  have heq (j : Fin D.L) : (⋃ i, D.W i j ∩ C j) = C j := by
    rw [← iUnion_inter, inter_eq_right.mpr (hCH j)]
  have hret := uniform_prism_cut_retains_mass D.W (fun i j => (hW i j).1)
    C hCm hCH m hm ht hlevel hretain
  refine ⟨valid_cut D hδ hδ1 hhh H C hCm ?_ ?_, heq⟩
  · calc
      _ ≤ (O (t / 2) * O (δ ^ h)) * ∑ i, volume (Y i) := mul_le_mul' hbudget le_rfl
      _ ≤ O (t / 2) * ∑ i, ∑ j, volume (D.W i j) := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl hmass
      _ ≤ _ := hret
  · intro j
    rw [heq j]
    calc
      _ ≤ (O (t / 2) * O (δ ^ h)) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) :=
        mul_le_mul' hbudget le_rfl
      _ ≤ O (t / 2) * volume (⋃ i, D.W i j) := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl (hdense j)
      _ ≤ O t * volume (⋃ i, D.W i j) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
      _ ≤ _ := hretain j

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
