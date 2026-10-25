-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.WeightedNarrow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedCoarse
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Cut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityCut

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, WeightedNarrow.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V O I P bodyCount shadingMeasure shadingMeasure_apply confinementDensity
   coarseLinear dualLinear boxAxis)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)

theorem incidence_measure_domination {n : ℕ} (W : Fin n → Set V)
    (hW : ∀ i, MeasurableSet (W i)) {m : ℝ} (hm : 0 ≤ m)
    (hcount : ∀ p, bodyCount W p ≤ m) (A : Set V) (hA : MeasurableSet A) :
    shadingMeasure W A ≤ O m * volume A := by
  have hc (p : V) : bodyCount (fun i => W i ∩ A) p ≤
      m * bodyCount (fun _ : Fin 1 => A) p := by
    by_cases hp : p ∈ A
    · simpa [bodyCount, hp] using hcount p
    · simp [bodyCount, hp]
  have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.body_mass_le_mul_of_count
    (fun i => (hW i).inter hA) (fun _ : Fin 1 => hA) hm hc
  simpa only [shadingMeasure_apply W hA, Fin.sum_univ_one] using hh

/-- Narrowing the frozen incidence data requires only an upper multiplicity
bound and sufficient average incidence density relative to that bound. -/
theorem valid_weighted_narrow_refinement {ω ζ δ h h' θ ρ c s R lam τ : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h')
    (hmassbudget : O (δ ^ h') ≤ (1 / 4 : ENNReal) * O (δ ^ h))
    (hdensitybudget : O (δ ^ h') ≤ O (τ / 4)) (hτ : 0 < τ)
    (H : D.Valid ω ζ δ h ρ c x v Y 1)
    (hYI : ∀ i, Y i ⊆ I) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρθ : ρ ≤ θ)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : D.a ≤ s * ρ * c)
    (hR : 0 < R) (hRs : R ≤ (s / 2) * ρ * c) (hlam : 0 ≤ lam)
    (haxis : ∀ j, ‖coarseLinear θ (boxAxis (D.e j) 2)‖ ≤ 43)
    (m : Fin D.L → ℝ) (hm : ∀ j, 0 < m j)
    (hcount : ∀ j p, bodyCount (fun i => D.W i j) p ≤ m j)
    (haverage : ∀ j, O (τ * m j) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      ∑ i, volume (D.W i j))
    (hupper : ∀ p ∈ ⋃ i, Y i, volume ((⋃ i, Y i) ∩ ball p R) ≤ O (lam * R ^ 3)) :
    confinementDensity D.a ρ c τ s ≤ 46080 * lam ∨
      ∃ C : Fin D.L → Set V, (D.cut C).Valid ω ζ δ h' ρ c x v Y 1 ∧
        (∀ j, MeasurableSet (C j) ∧ C j ⊆ ⋃ i, D.W i j ∧
          (⋃ i, (D.cut C).W i j) = C j) ∧
        ∀ j j' p, p ∈ C j → p ∈ C j' →
          pd (unit (dualLinear θ (boxAxis (D.e j) 0)))
            (unit (dualLinear θ (boxAxis (D.e j') 0))) ≤ s := by
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, _, hW, hmass, _, _⟩
  have hc : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
  have hρ : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  let ν (j : Fin D.L) := shadingMeasure (fun i => D.W i j)
  have hHj (j : Fin D.L) : MeasurableSet (⋃ i, D.W i j) :=
    MeasurableSet.iUnion fun i => (hW i j).1
  have htotal (j : Fin D.L) : ν j (⋃ i, D.W i j) = ∑ i, volume (D.W i j) := by
    rw [show ν j = shadingMeasure (fun i => D.W i j) from rfl,
      shadingMeasure_apply _ (hHj j)]
    apply Finset.sum_congr rfl
    intro i _
    rw [inter_eq_left.mpr (subset_iUnion (fun i => D.W i j) i)]
  have hfin (j : Fin D.L) : ν j (⋃ i, D.W i j) ≠ ⊤ := by
    rw [htotal]
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((hW i j).2.1.trans (inter_subset_left.trans (hYI i))))
  rcases weighted_coarse_grains_transverse_or_narrow hθ hθ1 hρ hρθ
      (hδ.trans_le ha) hab hc hs hs1 has hR hRs hτ hlam D.z D.e
      (fun j => ⋃ i, D.W i j) (⋃ i, Y i) (⋃ i, Y i) ν m hm haxis hHj
      (fun j => iUnion_subset fun i => (hW i j).2.1.trans inter_subset_right)
      (fun j => iUnion_mono fun i => (hW i j).2.1.trans inter_subset_left)
      Subset.rfl (iUnion_subset hYI) hfin
      (fun j A hA => incidence_measure_domination (fun i => D.W i j)
        (fun i => (hW i j).1) (hm j).le (hcount j) A hA)
      (fun j => (htotal j).symm ▸ haverage j) hupper with hden | hcuts
  · exact Or.inl hden
  · obtain ⟨C, hC, hnarrow⟩ := hcuts
    have heq (j : Fin D.L) : (⋃ i, D.W i j ∩ C j) = C j := by
      rw [← iUnion_inter, inter_eq_right.mpr (hC j).2.1]
    have hretain : (1 / 4 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) ≤
        ∑ i, ∑ j, volume (D.W i j ∩ C j) := by
      calc
        _ = ∑ j, (1 / 4 : ENNReal) * ∑ i, volume (D.W i j) := by
          rw [Finset.sum_comm, Finset.mul_sum]
        _ ≤ ∑ j, ∑ i, volume (D.W i j ∩ C j) := by
          apply Finset.sum_le_sum
          intro j _
          have hh := (hC j).2.2.1
          rw [htotal j, show ν j = shadingMeasure (fun i => D.W i j) from rfl,
            shadingMeasure_apply _ (hC j).1] at hh
          exact hh
        _ = _ := Finset.sum_comm
    refine Or.inr ⟨C, valid_cut D hδ hδ1 hhh H C (fun j => (hC j).1) ?_ ?_,
      fun j => ⟨(hC j).1, (hC j).2.1, heq j⟩, hnarrow⟩
    · calc
        _ ≤ ((1 / 4 : ENNReal) * O (δ ^ h)) * ∑ i, volume (Y i) :=
          mul_le_mul' hmassbudget le_rfl
        _ ≤ (1 / 4 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) := by
          rw [mul_assoc]
          exact mul_le_mul' le_rfl hmass
        _ ≤ _ := hretain
    · intro j
      rw [heq j]
      exact (mul_le_mul' hdensitybudget le_rfl).trans (hC j).2.2.2

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
