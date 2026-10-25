-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.RegularityFinite.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.TubeRegularity

/-! Simultaneous local regularity of one shading at finitely many radii. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- Regularity at a finite palette costs its cardinality, not repeated
constant-factor losses. The retained shading is its own density reference. -/
theorem regular_tube_shading_at_scales {J : ℕ} (hJ : 0 < J)
    {d : ℝ} (r : Fin J → ℝ) (hr : ∀ j, 0 < r j) (hr1 : ∀ j, r j ≤ 1)
    (hdr : ∀ j, d ≤ r j/8) {x v : V} (hv : ‖v‖ = 1)
    {Y : Set V} (hY : MeasurableSet Y) (hYT : Y ⊆ T d x v) :
    ∃ Z : Set V, MeasurableSet Z ∧ Z ⊆ Y ∧
      (1/2 : ENNReal)*volume Y ≤ volume Z ∧
      ∀ p ∈ Z, ∀ j, O (r j/(32*J))*volume Y ≤ volume (Z ∩ ball p (r j)) := by
  classical
  have hJr : (0:ℝ) < J := Nat.cast_pos.mpr hJ
  choose K hK hcover using fun j =>
    wz_tower_convex_count_composition.tube_ball_cover
      (r := r j/8) (div_pos (hr j) (by norm_num)) (by have hh := hr1 j; linarith) x v hv
  let I := Σ j : Fin J, Fin (K j)
  let C : I → Set V := fun l => ball (x+((l.2:ℝ)*(r l.1/8)) • v) (r l.1/2)
  let cost : I → ℝ := fun l => r l.1/(32*J)
  have hcost (l : I) : 0 ≤ cost l := by dsimp [cost]; exact div_nonneg (hr _).le (by positivity)
  have hsum : (∑ l : I, cost l) ≤ 1/2 := by
    have hpiece (j : Fin J) : (K j:ℝ)*(r j/(32*J)) ≤ 1/(2*J) := by
      apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*J)).mpr
      have he : (K j:ℝ)*(r j/(32*J))*(2*J) = (K j:ℝ)*r j/16 := by field_simp; ring
      rw [he]
      have hh := hK j
      nlinarith
    calc
      _ = ∑ j : Fin J, (K j:ℝ)*(r j/(32*J)) := by
        rw [Fintype.sum_sigma]
        simp [cost, mul_comm]
      _ ≤ ∑ _j : Fin J, 1/(2*(J:ℝ)) := Finset.sum_le_sum fun j _ => hpiece j
      _ = 1/2 := by simp; field_simp
  have hYfin : volume Y ≠ ∞ := measure_ne_top_of_subset hYT
    ((isBounded_closedBall.subset (segment_subset_closedBall_left x (x+v))).thickening.measure_lt_top).ne
  have hbudget : (∑ l : I, O (cost l)*volume Y) ≤ (1/2 : ENNReal)*volume Y := by
    rw [← Finset.sum_mul]
    have he : (∑ l : I, O (cost l)) = O (∑ l : I, cost l) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun l _ => hcost l)).symm
    rw [he]
    have hh : O (∑ l : I, cost l) ≤ (1/2 : ENNReal) := by
      convert ENNReal.ofReal_le_ofReal hsum using 1
      norm_num [ENNReal.ofReal_div_of_pos]
    exact mul_le_mul_left hh _
  obtain ⟨Z, hZm, hZY, hmass, hreg⟩ := wz_clustered_cover_volume_gain.regular_subshading_half
    volume Finset.univ C (fun l => O (cost l)*volume Y)
    (fun _ _ => measurableSet_ball) Y hY hYfin hbudget
  refine ⟨Z, hZm, hZY, hmass, ?_⟩
  intro p hp j
  have hpT : p ∈ T (r j/8) x v := thickening_mono (hdr j) _ (hYT (hZY hp))
  obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp (hcover j hpT)
  let l : I := ⟨j, ⟨k, Finset.mem_range.mp hk⟩⟩
  have hpC : p ∈ C l := by
    simpa only [C, l, show 4*(r j/8) = r j/2 by ring] using hpk
  have hnon : (Z ∩ C l).Nonempty := ⟨p, hp, hpC⟩
  have hlocal := ((hreg l (Finset.mem_univ _)).resolve_left hnon.ne_empty).le
  apply hlocal.trans
  apply measure_mono
  intro q hq
  refine ⟨hq.1, ?_⟩
  have hqc : dist q (x+((k:ℝ)*(r j/8)) • v) < r j/2 := hq.2
  have hpc : dist p (x+((k:ℝ)*(r j/8)) • v) < r j/2 := hpC
  rw [mem_ball]
  calc
    dist q p ≤ dist q (x+((k:ℝ)*(r j/8)) • v)+dist (x+((k:ℝ)*(r j/8)) • v) p := dist_triangle _ _ _
    _ < r j := by rw [dist_comm _ p]; linarith

/-- The simultaneous regularization applies independently to every fine tube. -/
theorem regular_shading_family_finite {n J : ℕ} (hJ : 0 < J) {d t : ℝ}
    (r : Fin J → ℝ) (hr : ∀ j, 0 < r j) (hr1 : ∀ j, r j ≤ 1)
    (hdr : ∀ j, d ≤ r j/8) (ht : 0 ≤ t)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (hmin : ∀ i, (Y i).Nonempty → O t ≤ volume (Y i)) :
    ∃ Z : Fin n → Set V,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1/2 : ENNReal)*(∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
      ∀ i p, p ∈ Z i → ∀ j, O (r j*t/(32*J)) ≤ volume (Z i ∩ ball p (r j)) := by
  classical
  choose Z hZm hZY hmass hreg using fun i =>
    regular_tube_shading_at_scales hJ r hr hr1 hdr (hv i) (hYm i) (hYT i)
  refine ⟨Z, fun i => ⟨hZm i, hZY i⟩, ?_, ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hmass i
  · intro i p hp j
    calc
      O (r j*t/(32*J)) = O (r j/(32*J))*O t := by
        rw [← ENNReal.ofReal_mul (div_nonneg (hr j).le (by positivity))]
        congr 1
        ring
      _ ≤ O (r j/(32*J))*volume (Y i) := mul_le_mul_right (hmin i ⟨p, hZY i hp⟩) _
      _ ≤ _ := hreg i p hp j

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
