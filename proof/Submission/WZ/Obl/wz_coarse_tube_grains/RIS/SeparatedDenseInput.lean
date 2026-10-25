-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SeparatedDenseInput.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SeparatedRelative

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

set_option maxHeartbeats 800000 in
/-- Separation, relative broadness, and average density can be achieved on
the same fixed local cells. Two explicit budgets account for all pruning. -/
theorem separated_dense_local_input {δ r τ s L : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hδr : δ ≤ r) (hτ : 0 < τ) (hs : 0 ≤ s)
    {n N : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (C : Fin N → Set Space) (q : Fin N → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, volume (Y i) ≠ ⊤) (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hC : ∀ j, MeasurableSet (C j)) (hCball : ∀ j, C j ⊆ Metric.ball (q j) r)
    (hdisj : Pairwise fun j k => Disjoint (C j) (C k))
    (hcover : (⋃ i, Y i) ⊆ ⋃ j, C j)
    (hcross : ∀ i, ({j | (Y i ∩ C j).Nonempty}.ncard : ℝ) ≤ L)
    (hrow : (τ * δ ^ 2 * r) * n * L ≤ (1 / 2 : ℝ) * shadingMass Y)
    (hcell : (8 * (⌈422400 / τ⌉₊ : ℝ)) * (s * n * L) ≤ shadingMass Y) :
    ∃ W : Fin n → Set Space,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) ∧
      shadingMass Y ≤ (8 * (⌈422400 / τ⌉₊ : ℝ)) * shadingMass W ∧
      (∀ p ∈ ⋃ i, W i, (1 / (4 * (⌈422400 / τ⌉₊ : ℝ))) * incidence Y p ≤ incidence W p) ∧
      (∀ i j k, j ≠ k → (W i ∩ C j).Nonempty → (W i ∩ C k).Nonempty →
        10 * r < dist (q j) (q k)) ∧
      (∀ i, (⋃ j, W i ∩ C j) = W i) ∧
      (∀ i, ({j | (W i ∩ C j).Nonempty}.ncard : ℝ) ≤ L) ∧
      (∀ j, ENNReal.ofReal (s * ({i | (W i ∩ C j).Nonempty}.ncard : ℝ)) ≤
        ∑ i, volume (W i ∩ C j)) := by
  obtain ⟨V, hV, hretain, hrelative, hsep, hunion, hcrossV⟩ :=
    separated_relative_shading hδ hr hδr hτ x v Y C q hv hY hfin hYT hC hCball
      hdisj hcover hcross hrow
  have hVfin (i : Fin n) : volume (V i) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin i) (measure_mono (hV i).2)
  have hD : (0 : ℝ) < (⌈422400 / τ⌉₊ : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (show 0 < 422400 / τ by positivity))
  have hbudgetR : s * n * L ≤ (1 / 2 : ℝ) * shadingMass V := by
    have hh := hcell.trans hretain
    have hh' : 2 * (s * n * L) ≤ shadingMass V := by
      apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * (⌈422400 / τ⌉₊ : ℝ))).mp
      nlinarith [hh]
    linarith
  have hmassV : ENNReal.ofReal (shadingMass V) = ∑ i, volume (V i) := by
    rw [shadingMass, ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    simp only [ENNReal.ofReal_toReal (hVfin _)]
  have hbudget : ENNReal.ofReal (s * n * L) ≤ (1 / 2 : ENNReal) * ∑ i, volume (V i) := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * shadingMass V) := ENNReal.ofReal_le_ofReal hbudgetR
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), hmassV]; norm_num [ENNReal.ofReal_div_of_pos]
  obtain ⟨A, hA, hhalf, hdense⟩ := common_cell_density_refinement volume V C
    (fun i => (hV i).1) hC hVfin hs hcrossV hbudget
  let W : Fin n → Set Space := fun i => V i ∩ A
  have hW (i : Fin n) : MeasurableSet (W i) ∧ W i ⊆ Y i :=
    ⟨(hV i).1.inter hA, inter_subset_left.trans (hV i).2⟩
  have hWfin (i : Fin n) : volume (W i) ≠ ⊤ :=
    ne_top_of_le_ne_top (hVfin i) (measure_mono inter_subset_left)
  have hhalfR : (1 / 2 : ℝ) * shadingMass V ≤ shadingMass W := by
    have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hWfin i)) hhalf
    simpa only [W, shadingMass, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_ofNat, ENNReal.toReal_sum (fun i _ => hVfin i),
      ENNReal.toReal_sum (fun i _ => hWfin i)] using hh
  refine ⟨W, hW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hhalfR
      (by positivity : 0 ≤ 8 * (⌈422400 / τ⌉₊ : ℝ))
    nlinarith [hretain]
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    change p ∈ V i ∩ A at hi
    have he : incidence W p = incidence V p := by
      rw [show incidence W p = A.indicator (incidence V) p from incidence_restrict V A p,
        indicator_of_mem hi.2]
    rw [he]
    exact hrelative p (mem_iUnion.mpr ⟨i, hi.1⟩)
  · intro i j k hjk hj hk
    exact hsep i j k hjk (hj.mono (inter_subset_inter_left _ inter_subset_left))
      (hk.mono (inter_subset_inter_left _ inter_subset_left))
  · intro i
    rw [← inter_iUnion]
    exact inter_eq_left.mpr ((hW i).2.trans ((subset_iUnion Y i).trans hcover))
  · intro i
    have hh : ({j | (W i ∩ C j).Nonempty}.ncard : ℝ) ≤ {j | (V i ∩ C j).Nonempty}.ncard := by
      exact_mod_cast ncard_le_ncard (fun j (hj : (W i ∩ C j).Nonempty) =>
        hj.mono (inter_subset_inter_left _ inter_subset_left))
    exact hh.trans (hcrossV i)
  · intro j
    by_cases hne : (⋃ i, W i ∩ C j).Nonempty
    · have hne' : ((⋃ i, V i ∩ A) ∩ C j).Nonempty := by
        simpa only [W, ← iUnion_inter] using hne
      have hcnt : ({i | (W i ∩ C j).Nonempty}.ncard : ℝ) ≤ {i | (V i ∩ C j).Nonempty}.ncard := by
        exact_mod_cast ncard_le_ncard (fun i (hi : (W i ∩ C j).Nonempty) =>
          hi.mono (inter_subset_inter_left _ inter_subset_left))
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcnt hs)).trans (hdense j hne')
    · have he : {i | (W i ∩ C j).Nonempty} = ∅ := by
        ext i
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun hi => hne (hi.mono (subset_iUnion (fun i => W i ∩ C j) i))
      simp only [he, ncard_empty, Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, zero_le]

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
