-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.KatzSeparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.PrismCarrier

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

noncomputable section

theorem exists_rotation_last {v : Space} (hv : ‖v‖ = 1) :
    ∃ e : Space ≃ₗᵢ[ℝ] Space, e v = EuclideanSpace.single 2 1 := by
  obtain ⟨u, hu, huv⟩ := Factor.exists_orth_unit hv
  obtain ⟨b, -, hb⟩ := Factor.exists_frame hu hv huv
  exact ⟨b.repr, by rw [← hb]; exact b.repr_self 2⟩

theorem cylinder_volume_upper {r A : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (Cylinder r x v) ≤ ENNReal.ofReal (4 * r ^ 2 * (6 + 2 * A)) := by
  obtain ⟨e, hev⟩ := exists_rotation_last hv
  have he : Cylinder r x v = Carrier 6 r (x + (3 : ℝ) • v - (1 / 2 : ℝ) • v) v := by
    unfold Cylinder wz_seed_of_balanced_robust_clusters.Cylinder Carrier Tube
    congr 2 <;> module
  have hsub := carrier_subset_box (by norm_num : (0 : ℝ) ≤ 6) (x + (3 : ℝ) • v) e hev (ρ := r)
  rw [← he] at hsub
  calc
    _ ≤ volume (Factor.box (2 * r) (2 * r) (6 + 2 * r) (x + (3 : ℝ) • v) e) := measure_mono hsub
    _ = ENNReal.ofReal ((2 * r) * (2 * r) * (6 + 2 * r)) :=
      Factor.box_volume (by positivity) (by positivity) (by positivity) _ _
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hrA (by positivity : 0 ≤ 8 * r ^ 2)
      nlinarith

def tubeConflict {n : ℕ} (δ : ℝ) (x v : Fin n → Space) (i j : Fin n) : Prop :=
  (¬ volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) ∨
  (¬ volume (Tube δ (x j) (v j) ∩ Tube δ (x i) (v i)) ≤
    (1 / 2 : ENNReal) * volume (Tube δ (x j) (v j)))

theorem tubeConflict_cylinder {n : ℕ} {δ : ℝ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hv : ∀ i, ‖v i‖ = 1) {i j : Fin n}
    (hij : tubeConflict δ x v i j) :
    Tube δ (x j) (v j) ⊆ Cylinder (100003 * δ) (x i - (2 : ℝ) • v i) (v i) := by
  have hmeet : (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)).Nonempty := by
    rcases hij with h | h
    · exact nonempty_of_measure_ne_zero (fun hz => h (by rw [hz]; exact bot_le))
    · rw [inter_comm]
      exact nonempty_of_measure_ne_zero (fun hz => h (by rw [hz]; exact bot_le))
  have hdir : ‖v j - v i‖ ≤ 100000 * δ ∨ ‖v j + v i‖ ≤ 100000 * δ := by
    by_contra hn
    push Not at hn
    rcases hij with h | h
    · apply h
      apply wz_direction_density_transfer.intersection_le_half hδ (hv i) (hv j)
      · simpa only [norm_sub_rev] using hn.1.le
      · simpa only [add_comm] using hn.2.le
    · exact h (wz_direction_density_transfer.intersection_le_half hδ (hv j) (hv i) hn.1.le hn.2.le)
  simpa only [show 100000 * δ + 3 * δ = 100003 * δ by ring] using
    tube_subset_cylinder_of_direction_close hmeet hdir

def conflictCountConstant : ℝ := 4 * 100003 ^ 2 * (6 + 2 * 100003)

/-- Convex counts bound the degree of the half-overlap conflict relation without an
essential-distinctness hypothesis. -/
theorem conflict_degree_of_katz {n : ℕ} {δ m : ℝ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hv : ∀ i, ‖v i‖ = 1)
    (hK : Katz δ m x v) (i : Fin n) :
    ((Finset.univ.filter fun j => tubeConflict δ x v i j).card : ℝ) ≤ conflictCountConstant * m := by
  classical
  let W := Cylinder (100003 * δ) (x i - (2 : ℝ) • v i) (v i)
  have hW : Convex ℝ W := (convex_segment _ _).thickening _
  have hcnt : (Finset.univ.filter fun j => tubeConflict δ x v i j).card ≤
      {j | Tube δ (x j) (v j) ⊆ W}.ncard := by
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_mono
    intro j hj
    exact tubeConflict_cylinder hδ hv (Finset.mem_filter.mp hj).2
  have hvW : volume W ≤ ENNReal.ofReal (conflictCountConstant * δ ^ 2) := by
    have hh := cylinder_volume_upper (by positivity : 0 ≤ 100003 * δ)
      (by linarith : 100003 * δ ≤ 100003) (x i - (2 : ℝ) • v i) (v i) (hv i)
    convert hh using 1
    congr 1
    unfold conflictCountConstant
    ring
  have hk := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcnt) (sq_nonneg δ))).trans (hK W hW)
  have hh := hk.trans (mul_le_mul_right hvW _)
  rw [← ENNReal.ofReal_mul hm] at hh
  have hr := (ENNReal.ofReal_le_ofReal_iff (by dsimp [conflictCountConstant]; positivity)).mp hh
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp
  nlinarith [hr]

/-- Weighted separation loses at most a linear factor in the convex-count coefficient. -/
theorem weighted_distinct_of_katz {n : ℕ} {δ m : ℝ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hv : ∀ i, ‖v i‖ = 1)
    (hK : Katz δ m x v) (a : Fin n → ENNReal) :
    ∃ S : Finset (Fin n),
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) ∧
      ∑ i, a i ≤ (⌈conflictCountConstant * m⌉₊ : ENNReal) * ∑ i ∈ S, a i := by
  classical
  have hdeg : ∀ i, (Finset.univ.filter (tubeConflict δ x v i)).card ≤ ⌈conflictCountConstant * m⌉₊ := by
    intro i
    exact_mod_cast (conflict_degree_of_katz hδ hδ1 hm hv hK i).trans (Nat.le_ceil _)
  obtain ⟨S, -, hsep, hmass⟩ := weighted_separated_subfamily (tubeConflict δ x v)
    (fun i => Or.inl (tube_self_conflict hδ _ _ (hv i))) (fun h => h.symm)
    ⌈conflictCountConstant * m⌉₊ hdeg a Finset.univ
  refine ⟨S, ?_, hmass⟩
  intro i hi j hj hij
  exact not_not.mp (fun hh => hsep i hi j hj hij (Or.inl hh))

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
