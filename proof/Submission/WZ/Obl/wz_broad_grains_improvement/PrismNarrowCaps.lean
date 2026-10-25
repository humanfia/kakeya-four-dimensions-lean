-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.PrismNarrowCaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.PrismCapsTransport
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedRotate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.KatzSeparation

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap
  (PrismData weighted_fibre_coarse_dichotomy incidence_measure_domination valid_cut)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (bodyCount shadingMeasure shadingMeasure_apply confinementDensity coarseLinear
   dualLinear boxAxis rotatedFrame rotatedFrame_apply rotated_boxAxis frozen_coarse_axis_bounds)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)

/-- Weighted narrowing preserves the column incidence bounds needed by the
later grain transfer. The quarter-retention statement comes from the accepted
weighted fibre dichotomy and is kept here instead of discarded. -/
theorem capped_weighted_fibre_narrow {ω ζ d h h' ρ c s R lam τ : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hhh : h ≤ h')
    (hmassbudget : O (d^h') ≤ (1/4 : ENNReal) * O (d^h))
    (hcapbudget : O (d^h') ≤ O (τ/4)) (hτ : 0 < τ)
    (H : D.Valid ω ζ d h ρ c x v Y 1) (hYI : ∀ i, Y i ⊆ I)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : D.a ≤ s*ρ*c)
    (hR : 0 < R) (hRs : R ≤ (s/2)*ρ*c) (hlam : 0 ≤ lam)
    (m : Fin D.L → ℝ) (hm : ∀ j, 0 < m j)
    (hcount : ∀ j p, bodyCount (fun i => D.W i j) p ≤ m j)
    (haverage : ∀ j, O (τ*m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j)) ≤
      ∑ i, volume (D.W i j))
    (Z : Set V) (hWZ : ∀ i j, D.W i j ⊆ Z) (hZU : Z ⊆ ⋃ i, Y i)
    (hupper : ∀ p ∈ Z, volume ((⋃ i, Y i) ∩ ball p R) ≤ O (lam*R^3)) :
    confinementDensity D.a ρ c τ s ≤ 46080*lam ∨
      ∃ rot : Fin D.N → V ≃ₗᵢ[ℝ] V,
        (∀ k, rot k (D.w k) = EuclideanSpace.single 2 1) ∧
      ∃ C : Fin D.L → Set V, (D.cut C).Valid ω ζ d h' ρ c x v Y 1 ∧
        (D.cut C).HasCaps d h' ρ c ∧
        (∀ j, MeasurableSet (C j) ∧ C j ⊆ ⋃ i, D.W i j ∧
          (⋃ i, (D.cut C).W i j) = C j) ∧
        ∀ j j' p, D.γ j = D.γ j' → p ∈ C j → p ∈ C j' →
          pd (unit (dualLinear ρ (rot (D.γ j) (boxAxis (D.e j) 0))))
            (unit (dualLinear ρ (rot (D.γ j') (boxAxis (D.e j') 0)))) ≤ s := by
  classical
  have hW := H.2.2.2.2.1
  have hc : 0 < c := hd.trans_le (H.1.trans (H.2.1.trans H.2.2.1))
  have hρ : 0 < ρ := (mul_pos_iff.mp (hd.trans_le (H.1.trans H.2.1))).resolve_right
    (by rintro ⟨_, hneg⟩; linarith) |>.1
  have hρ1 : ρ ≤ 1 := by nlinarith [H.2.2.1]
  have hw := H.2.2.2.2.2.2.2.2.2.2.1
  choose rot hrot using fun k =>
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.exists_rotation_last (hw k)
  have haxis (j : Fin D.L) : ‖coarseLinear ρ (rot (D.γ j) (boxAxis (D.e j) 2))‖ ≤ 43 := by
    have hh := frozen_coarse_axis_bounds hρ hρ1 hρ.le le_rfl
      (rotatedFrame (rot (D.γ j)) (D.e j)) (rot (D.γ j) (D.w (D.γ j)))
      (by simpa only [LinearIsometryEquiv.norm_map] using hw (D.γ j))
      (by rw [hrot]; simpa using hρ.le)
      (by rw [hrot]; simpa using hρ.le)
      (by simpa only [rotatedFrame_apply] using
        ((H.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)).2 j).2)
    simpa only [rotated_boxAxis] using hh.2.2
  let ν : Fin D.L → Measure V := fun j => shadingMeasure (fun i => D.W i j)
  have hUm (j : Fin D.L) : MeasurableSet (⋃ i, D.W i j) :=
    MeasurableSet.iUnion fun i => (hW i j).1
  have htotal (j : Fin D.L) : ν j (⋃ i, D.W i j) = ∑ i, volume (D.W i j) := by
    rw [show ν j = shadingMeasure (fun i => D.W i j) from rfl,
      shadingMeasure_apply _ (hUm j)]
    congr 1
    ext i
    rw [inter_eq_left.mpr (subset_iUnion (fun i => D.W i j) i)]
  have hfinite (j : Fin D.L) : ν j (⋃ i, D.W i j) ≠ ⊤ := by
    rw [htotal]
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((hW i j).2.1.trans (inter_subset_left.trans (hYI i))))
  rcases weighted_fibre_coarse_dichotomy hρ hρ1 (hd.trans_le H.1) H.2.1 hc
      hs hs1 has hR hRs hτ hlam rot D.γ D.z D.e (fun j => ⋃ i, D.W i j)
      Z (⋃ i, Y i) ν m hm haxis hUm
      (fun j => iUnion_subset fun i => (hW i j).2.1.trans inter_subset_right)
      (fun j => iUnion_subset fun i => hWZ i j) hZU (iUnion_subset hYI) hfinite
      (fun j B hB => incidence_measure_domination (fun i => D.W i j)
        (fun i => (hW i j).1) (hm j).le (hcount j) B hB)
      (fun j => (htotal j).symm ▸ haverage j) hupper with hden | hcuts
  · exact Or.inl hden
  obtain ⟨C, hC, hnarrow⟩ := hcuts
  have heq (j : Fin D.L) : (⋃ i, D.W i j ∩ C j) = C j := by
    rw [← iUnion_inter, inter_eq_right.mpr (hC j).2.1]
  have hretain (j : Fin D.L) : (1/4 : ENNReal) * ∑ i, volume (D.W i j) ≤
      ∑ i, volume (D.W i j ∩ C j) := by
    have hh := (hC j).2.2.1
    rw [htotal j, show ν j = shadingMeasure (fun i => D.W i j) from rfl,
      shadingMeasure_apply _ (hC j).1] at hh
    exact hh
  have hvalid : (D.cut C).Valid ω ζ d h' ρ c x v Y 1 := by
    apply valid_cut D hd hd1 hhh H C (fun j => (hC j).1)
    · calc
        _ ≤ ((1/4 : ENNReal) * O (d^h)) * ∑ i, volume (Y i) := mul_le_mul' hmassbudget le_rfl
        _ ≤ (1/4 : ENNReal) * ∑ i, ∑ j, volume (D.W i j) := by
          rw [mul_assoc]
          exact mul_le_mul' le_rfl H.2.2.2.2.2.1
        _ = ∑ j, (1/4 : ENNReal) * ∑ i, volume (D.W i j) := by
          rw [Finset.sum_comm, Finset.mul_sum]
        _ ≤ ∑ j, ∑ i, volume (D.W i j ∩ C j) := Finset.sum_le_sum fun j _ => hretain j
        _ = _ := Finset.sum_comm
    · intro j
      rw [heq]
      exact (mul_le_mul' hcapbudget le_rfl).trans (hC j).2.2.2
  have hcaps : (D.cut C).HasCaps d h' ρ c := by
    refine ⟨m, hm, ?_, ?_⟩
    · intro j p
      change Fin D.L at j
      change bodyCount (fun i => D.W i j ∩ C j) p ≤ m j
      rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount_inter]
      split_ifs
      · exact hcount j p
      · exact (hm j).le
    · intro j
      change Fin D.L at j
      change O (d^h'*m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j)) ≤ _
      calc
        _ = O (d^h') * (O (m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j))) := by
          rw [O, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le h'), mul_assoc]
        _ ≤ O (τ/4) * (O (m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j))) :=
          mul_le_mul' hcapbudget le_rfl
        _ = (1/4 : ENNReal) * (O (τ*m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j))) := by
          rw [O, ENNReal.ofReal_mul hτ.le, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
          norm_num [div_eq_mul_inv]
          ring
        _ ≤ (1/4 : ENNReal) * ∑ i, volume (D.W i j) := mul_le_mul' le_rfl (haverage j)
        _ ≤ _ := hretain j
  exact Or.inr ⟨rot, hrot, C, hvalid, hcaps,
    fun j => ⟨(hC j).1, (hC j).2.1, heq j⟩, hnarrow⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
