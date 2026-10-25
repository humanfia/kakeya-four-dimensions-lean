-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SeparatedRelativePower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SeparatedDensePower

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open wz_extremal_lipschitz_grains
open scoped Classical

set_option maxHeartbeats 1000000 in
/-- Select separated dense rows while keeping a uniform pointwise fraction
of the original incidence. No angular hypothesis is needed for this selection. -/
theorem separated_dense_relative_input_power {η : ℝ} (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ r L : ℝ,
      0 < δ → δ ≤ 1 → δ ≤ d → δ ≤ r → 0 ≤ L →
      ∀ (n N : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
        (C : Fin N → Set Space) (q : Fin N → Space),
      (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, volume (Y i) ≠ ⊤) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
      (∀ j, MeasurableSet (C j)) → (∀ j, C j ⊆ Metric.ball (q j) r) →
      (Pairwise fun j k => Disjoint (C j) (C k)) →
      (⋃ i, Y i) ⊆ ⋃ j, C j →
      (∀ i, ({j | (Y i ∩ C j).Nonempty}.ncard : ℝ) ≤ L) →
      2 * (δ ^ η * δ ^ 2 * r) * n * L ≤ shadingMass Y →
      ∃ W : Fin n → Set Space,
        (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) ∧
        ENNReal.ofReal (δ ^ (3 * η)) * (∑ i, volume (Y i)) ≤ ∑ i, volume (W i) ∧
        (∀ i j k, j ≠ k → (W i ∩ C j).Nonempty → (W i ∩ C k).Nonempty →
          10 * r < dist (q j) (q k)) ∧
        (∀ i, (⋃ j, W i ∩ C j) = W i) ∧
        (∀ i, ({j | (W i ∩ C j).Nonempty}.ncard : ℝ) ≤ L) ∧
        (∀ j, ENNReal.ofReal (δ ^ (4 * η) *
          ({i | (W i ∩ C j).Nonempty}.ncard : ℝ) * δ ^ 2 * r) ≤ ∑ i, volume (W i ∩ C j)) ∧
        ∀ p ∈ ⋃ i, W i, δ ^ (3 * η) * incidence Y p ≤ incidence W p := by
  obtain ⟨d, hd, hcost⟩ := separation_cost_power hη
  refine ⟨d, hd, ?_⟩
  intro δ r L hδ hδ1 hδd hδr hL n N x v Y C q hv hY hfin hYT hC hball hdisj hcover
    hcross hbudget
  have hr : 0 < r := hδ.trans_le hδr
  let K : ℝ := (⌈422400 / δ ^ (2 * η)⌉₊ : ℝ)
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast (Nat.ceil_pos.mpr (show 0 < 422400 / δ ^ (2 * η) by positivity))
  have hKbound : 8 * K ≤ δ ^ (-3 * η) := hcost δ hδ hδ1 hδd
  have hrow : (δ ^ (2 * η) * δ ^ 2 * r) * n * L ≤ (1 / 2 : ℝ) * shadingMass Y := by
    have hp : δ ^ (2 * η) ≤ δ ^ η :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc
      _ ≤ (δ ^ η * δ ^ 2 * r) * n * L := by gcongr
      _ ≤ _ := by nlinarith [hbudget]
  have hcell : (8 * K) * ((δ ^ (4 * η) * δ ^ 2 * r) * n * L) ≤ shadingMass Y := by
    calc
      _ ≤ δ ^ (-3 * η) * ((δ ^ (4 * η) * δ ^ 2 * r) * n * L) :=
        mul_le_mul_of_nonneg_right hKbound (by positivity)
      _ = (δ ^ η * δ ^ 2 * r) * n * L := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hδ]
        congr 4
        ring
      _ ≤ _ := by nlinarith [hbudget, show 0 ≤ (δ ^ η * δ ^ 2 * r) * n * L by positivity]
  obtain ⟨W, hW, hkeep, hrelative, hsep, hunion, hcrossW, hdense⟩ :=
    separated_dense_local_input hδ hr hδr (Real.rpow_pos_of_pos hδ _) (by positivity)
      x v Y C q hv hY hfin hYT hC hball hdisj hcover hcross hrow hcell
  have hWfin (i : Fin n) : volume (W i) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin i) (measure_mono (hW i).2)
  have hmassY : ENNReal.ofReal (shadingMass Y) = ∑ i, volume (Y i) := by
    rw [shadingMass, ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    simp only [ENNReal.ofReal_toReal (hfin _)]
  have hmassW : ENNReal.ofReal (shadingMass W) = ∑ i, volume (W i) := by
    rw [shadingMass, ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    simp only [ENNReal.ofReal_toReal (hWfin _)]
  have hkeepR : δ ^ (3 * η) * shadingMass Y ≤ shadingMass W := by
    have hmassW0 : 0 ≤ shadingMass W := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    calc
      _ ≤ δ ^ (3 * η) * ((8 * K) * shadingMass W) :=
        mul_le_mul_of_nonneg_left hkeep (Real.rpow_nonneg hδ.le _)
      _ ≤ δ ^ (3 * η) * (δ ^ (-3 * η) * shadingMass W) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKbound hmassW0)
          (Real.rpow_nonneg hδ.le _)
      _ = _ := by rw [← mul_assoc, ← Real.rpow_add hδ]; simp
  refine ⟨W, hW, ?_, hsep, hunion, hcrossW, ?_, ?_⟩
  · rw [← hmassY, ← hmassW, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    exact ENNReal.ofReal_le_ofReal hkeepR
  · intro j
    convert hdense j using 1 <;> congr 1 <;> ring
  · intro p hp
    apply le_trans (mul_le_mul_of_nonneg_right ?_ (incidence_nonneg Y p)) (hrelative p hp)
    apply (le_div_iff₀ (by positivity : 0 < 4 * K)).mpr
    calc
      _ ≤ δ ^ (3 * η) * δ ^ (-3 * η) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
        exact (show 4 * K ≤ 8 * K by linarith).trans hKbound
      _ = 1 := by rw [← Real.rpow_add hδ]; simp

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
