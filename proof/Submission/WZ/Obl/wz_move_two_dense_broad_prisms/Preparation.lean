-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.Preparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.EndpointTrim
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.TubeRegularity
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.FibreRetention

/-! Uniform local mass and pointwise fibre retention for residual shadings. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- Delete tubes carrying less than a specified mass; the cost is at most one
threshold per fine tube. -/
theorem prune_small_tubes {n : ℕ} (Y : Fin n → Set V)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYfin : ∀ i, volume (Y i) ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t)
    (hbudget : O ((n : ℝ)*t) ≤ (1/2 : ENNReal) * ∑ i, volume (Y i)) :
    ∃ Z : Fin n → Set V,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ ((Z i).Nonempty → O t ≤ volume (Z i))) ∧
      (1/2 : ENNReal) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) := by
  classical
  let Z : Fin n → Set V := fun i => if O t ≤ volume (Y i) then Y i else ∅
  let B : Fin n → Set V := fun i => if O t ≤ volume (Y i) then ∅ else Y i
  have hbalance : (∑ i, volume (Y i)) = (∑ i, volume (Z i)) + ∑ i, volume (B i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : O t ≤ volume (Y i) <;> simp [Z, B, hi]
  have hbad : (∑ i, volume (B i)) ≤ O ((n : ℝ)*t) := by
    calc
      _ ≤ ∑ _i : Fin n, O t := Finset.sum_le_sum fun i _ => by
        by_cases hi : O t ≤ volume (Y i)
        · simp [B, hi]
        · simpa only [B, if_neg hi] using (lt_of_not_ge hi).le
      _ = _ := by
        change (∑ _i : Fin n, ENNReal.ofReal t) = ENNReal.ofReal ((n : ℝ)*t)
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        simp
  refine ⟨Z, ?_, wz_clustered_cover_volume_gain.half_mass_after_loss
    (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i)) hbalance.le (hbad.trans hbudget)⟩
  intro i
  by_cases hi : O t ≤ volume (Y i)
  · simpa only [Z, if_pos hi] using ⟨hYm i, Subset.rfl, fun _ => hi⟩
  · simp [Z, hi]

/-- Regularize each occupied fine tube at a common radius while retaining half
of the incidence mass. -/
theorem regular_shading_family {n : ℕ} {d r t : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hdr : d ≤ r/8) (ht : 0 ≤ t)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (hmin : ∀ i, (Y i).Nonempty → O t ≤ volume (Y i)) :
    ∃ Z : Fin n → Set V,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1/2 : ENNReal) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
      ∀ i p, p ∈ Z i → O (r*t/32) ≤ volume (Z i ∩ ball p r) := by
  classical
  choose Z hZm hZY hmass hreg using fun i =>
    regular_tube_shading_at_scale hr hr1 hdr (hv i) (hYm i) (hYT i)
  refine ⟨Z, fun i => ⟨hZm i, hZY i⟩, ?_, ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hmass i
  · intro i p hp
    calc
      O (r*t/32) = O (r/32) * O t := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ O (r/32) * volume (Y i) := mul_le_mul_right (hmin i ⟨p, hZY i hp⟩) _
      _ ≤ _ := hreg i p hp

/-- A half-mass residual admits a regular shading and a pointwise substantial
fibre subshading. The regular shading supplies all local tube masses, and the
smaller shading supplies the broad stem and its partners. -/
theorem prepare_residual_shading {n N : ℕ} {d r R q t : ℝ}
    (hd : 0 < d) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : d ≤ r/8)
    (hdR : d ≤ R) (hendpoint : 4608*R ≤ q) (ht : 0 ≤ t)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1) (f : Fin n → Fin N)
    (Z Y : Fin n → Set V) (hZm : ∀ i, MeasurableSet (Z i))
    (hYm : ∀ i, MeasurableSet (Y i)) (hZT : ∀ i, Z i ⊆ T d (x i) (v i))
    (hYZ : ∀ i, Y i ⊆ Z i)
    (hretain : (1/2 : ENNReal) * (∑ i, volume (Z i)) ≤ ∑ i, volume (Y i))
    (hmin : O (4*(n : ℝ)*t) ≤ ∑ i, volume (Y i))
    (hdense : O (q*(n : ℝ)*d^2) ≤ ∑ i, volume (Y i)) :
    ∃ U W : Fin n → Set V,
      (∀ i, MeasurableSet (U i) ∧ U i ⊆ Y i) ∧
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ U i) ∧
      (∀ i p, p ∈ U i → R < dist p (x i) ∧ R < dist p (x i+v i)) ∧
      (∀ i p, p ∈ U i → O (r*t/32) ≤ volume (U i ∩ ball p r)) ∧
      O (1/32) * (∑ i, volume (Z i)) ≤ ∑ i, volume (W i) ∧
      ∀ k p, (∃ i, f i = k ∧ p ∈ W i) →
        wz_clustered_cover_volume_gain.fiberBodyCount f Z k p ≤
          32*wz_clustered_cover_volume_gain.fiberBodyCount f W k p := by
  have hZfin (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset (hZT i)
    ((isBounded_closedBall.subset (segment_subset_closedBall_left (x i) (x i+v i))).thickening.measure_lt_top).ne
  obtain ⟨E, hE, hEend, hEmass⟩ := shading_away_from_endpoints hd hdR hendpoint
    x v Y hv hYm (fun i => (hYZ i).trans (hZT i)) hdense
  have hEfin (i) : volume (E i) ≠ ∞ :=
    measure_ne_top_of_subset ((hE i).2.trans (hYZ i)) (hZfin i)
  have hbudget : O ((n : ℝ)*t) ≤ (1/2 : ENNReal) * ∑ i, volume (E i) := by
    calc
      _ = (1/4 : ENNReal) * O (4*(n : ℝ)*t) := by
        change ENNReal.ofReal ((n : ℝ)*t) = (1/4 : ENNReal) * ENNReal.ofReal (4*(n : ℝ)*t)
        rw [show 4*(n : ℝ)*t = 4*((n : ℝ)*t) by ring,
          ENNReal.ofReal_mul (by norm_num)]
        norm_num [← mul_assoc, ENNReal.inv_mul_cancel]
      _ ≤ (1/4 : ENNReal) * ∑ i, volume (Y i) := mul_le_mul_right hmin _
      _ = (1/2 : ENNReal) * ((1/2 : ENNReal) * ∑ i, volume (Y i)) := by
        norm_num [← mul_assoc, ← ENNReal.mul_inv]
      _ ≤ _ := mul_le_mul_right hEmass _
  obtain ⟨Q, hQ, hQmass⟩ := prune_small_tubes E (fun i => (hE i).1) hEfin ht hbudget
  obtain ⟨U, hU, hUmass, hUreg⟩ := regular_shading_family hr hr1 hdr ht x v hv Q
    (fun i => (hQ i).1) (fun i => (hQ i).2.1.trans ((hE i).2.trans ((hYZ i).trans (hZT i))))
    (fun i => (hQ i).2.2)
  have hUold : O (1/16) * (∑ i, volume (Z i)) ≤ ∑ i, volume (U i) := by
    calc
      _ = (1/2 : ENNReal) * ((1/2 : ENNReal) * ((1/2 : ENNReal) *
          ((1/2 : ENNReal) * ∑ i, volume (Z i)))) := by
        change ENNReal.ofReal (1/16) * _ = _
        norm_num [← mul_assoc, ← ENNReal.mul_inv, ENNReal.ofReal_div_of_pos]
      _ ≤ (1/2 : ENNReal) * ((1/2 : ENNReal) * ((1/2 : ENNReal) * ∑ i, volume (Y i))) := by
        gcongr
      _ ≤ (1/2 : ENNReal) * ((1/2 : ENNReal) * ∑ i, volume (E i)) := by gcongr
      _ ≤ (1/2 : ENNReal) * ∑ i, volume (Q i) := by gcongr
      _ ≤ _ := hUmass
  have hUZ (i) : U i ⊆ Z i :=
    (hU i).2.trans ((hQ i).2.1.trans ((hE i).2.trans (hYZ i)))
  obtain ⟨W, hW, hWmass, hWcount⟩ := retain_fibre_incidence_ratio f hZm
    (fun i => (hU i).1) hZfin hUZ (by norm_num : (0:ℝ) ≤ 1/16) hUold
  refine ⟨U, W, fun i => ⟨(hU i).1, (hU i).2.trans ((hQ i).2.1.trans (hE i).2)⟩,
    hW, ?_, hUreg, ?_, ?_⟩
  · intro i p hp
    exact hEend i p ((hQ i).2.1 ((hU i).2 hp))
  · convert hWmass using 1 <;> norm_num
  · intro k p hp
    have hh := hWcount k p hp
    linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
