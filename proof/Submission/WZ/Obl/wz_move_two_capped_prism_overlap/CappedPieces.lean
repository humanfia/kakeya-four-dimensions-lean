-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CappedPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.RelativePieces
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedNarrow
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.PrismSelect
import Submission.WZ.Obl.wz_coarse_grains_assembly.DenseWeights

/- Adapted from this workspace: o197/x0567, d9e04e2b24c3, CappedPieces.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P I bodyCount shadingMeasure shadingMeasure_apply)
open WangZahlLot.Obl.wz_extremal_lipschitz_grains (incidence shadingMass incidence_eq_ncard)
open WangZahlLot.Obl.wz_coarse_grains_assembly (rIdx rIdx_mem rIdx_injective)

private theorem ofReal_sum_shadingMass {n L : ℕ} (W : Fin n → Fin L → Set V)
    (hfin : ∀ i j, volume (W i j) ≠ ⊤) :
    ENNReal.ofReal (∑ j, shadingMass (fun i => W i j)) = ∑ i, ∑ j, volume (W i j) := by
  change ENNReal.ofReal (∑ j, ∑ i, (volume (W i j)).toReal) = _
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg))]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
  simp_rw [ENNReal.ofReal_toReal (hfin _ _)]
  exact Finset.sum_comm

/-- Arbitrary incidence cuts retaining a positive fraction can be pruned to
restore relative point counts and the effective density of retained prisms. -/
theorem select_capped_pieces {ω ζ δ h h₁ h₂ ρ c τ q : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh₁ : h ≤ h₁) (hh₂ : h₁ ≤ h₂)
    (hτ : 0 < τ) (hq : 0 < q)
    (hmassbudget : O (δ ^ h₁) ≤ O (q / 4) * O (δ ^ h))
    (hdensitybudget : O (δ ^ h₂) ≤ O (q * τ / 4))
    (hbroadbudget : δ ^ (-h₁) ≤ (q / 2) * δ ^ (-h₂))
    (H : D.Valid ω ζ δ h ρ c x v Y 1) (hYI : ∀ i, Y i ⊆ I)
    (m : Fin D.L → ℝ) (hm : ∀ j, 0 < m j)
    (hcount : ∀ j p, bodyCount (fun i => D.W i j) p ≤ m j)
    (haverage : ∀ j, O (τ * m j) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      ∑ i, volume (D.W i j))
    (Z : Fin n → Fin D.L → Set V)
    (hZ : ∀ i j, MeasurableSet (Z i j) ∧ Z i j ⊆ D.W i j)
    (hretain : O q * (∑ i, ∑ j, volume (D.W i j)) ≤ ∑ i, ∑ j, volume (Z i j)) :
    ∃ (L : ℕ) (f : Fin L → Fin D.L) (U : Fin n → Fin L → Set V),
      Function.Injective f ∧ (∀ i j, MeasurableSet (U i j) ∧ U i j ⊆ Z i (f j)) ∧
      let D' := (D.select D.s f id (D.γ ∘ f)).refinePieces U
      D'.Valid ω ζ δ h₂ ρ c x v Y 1 ∧
      (∀ j p, bodyCount (fun i => U i j) p ≤ m (f j)) ∧
      (∀ j, O ((q * τ / 4) * m (f j)) * volume (P D'.a (ρ * c) c (D'.z j) (D'.e j)) ≤
        ∑ i, volume (U i j)) := by
  classical
  have hWm := H.2.2.2.2.1
  have hWfin (i : Fin n) (j : Fin D.L) : volume (D.W i j) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((hWm i j).2.1.trans (inter_subset_left.trans (hYI i))))
  have hZfin (i : Fin n) (j : Fin D.L) : volume (Z i j) ≠ ⊤ :=
    ne_top_of_le_ne_top (hWfin i j) (measure_mono (hZ i j).2)
  have hchoose (j : Fin D.L) :=
    WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity.relative_incidence_refinement
      (fun i => (hWm i j).1) (fun i => (hZ i j).1) (fun i => hWfin i j)
      (fun i => (hZ i j).2) (by positivity : 0 ≤ q / 2)
  choose R hR hRmass hRrelative using hchoose
  let M (j : Fin D.L) := ∑ i, volume (D.W i j)
  let W (j : Fin D.L) := ∑ i, volume (R j i)
  have hMfin (j : Fin D.L) : M j ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => hWfin i j)
  have hRsub (i : Fin n) (j : Fin D.L) : R j i ⊆ D.W i j := (hR j i).2.trans (hZ i j).2
  have hRfin (i : Fin n) (j : Fin D.L) : volume (R j i) ≠ ⊤ :=
    ne_top_of_le_ne_top (hWfin i j) (measure_mono (hRsub i j))
  have hretainR : q * (∑ j, shadingMass (fun i => D.W i j)) ≤
      ∑ j, shadingMass (fun i => Z i j) := by
    apply (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)))).mp
    change ENNReal.ofReal (q * (∑ j, shadingMass (fun i => D.W i j))) ≤
      ENNReal.ofReal (∑ j, shadingMass (fun i => Z i j))
    rw [ENNReal.ofReal_mul hq.le, ofReal_sum_shadingMass D.W hWfin,
      ofReal_sum_shadingMass Z hZfin]
    exact hretain
  have hhalfR : (q / 2) * (∑ j, shadingMass (fun i => D.W i j)) ≤
      ∑ j, shadingMass (R j) := by
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hRmass j)
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
    linarith
  have hhalf : O (q / 2) * (∑ j, M j) ≤ ∑ j, W j := by
    have hh := ENNReal.ofReal_le_ofReal hhalfR
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ q / 2),
      ofReal_sum_shadingMass D.W hWfin,
      ofReal_sum_shadingMass (fun i j => R j i) hRfin] at hh
    calc
      _ = O (q / 2) * (∑ i, ∑ j, volume (D.W i j)) :=
        congrArg (fun t : ENNReal => O (q / 2) * t) Finset.sum_comm
      _ ≤ ∑ i, ∑ j, volume (R j i) := hh
      _ = _ := Finset.sum_comm
  have hsum : ENNReal.ofReal (∑ j, (M j).toReal) = ∑ j, M j := by
    change ENNReal.ofReal (∑ j, (M j).toReal) = _
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl (fun j _ => ENNReal.ofReal_toReal (hMfin j))
  have hbudget : O (2 * (q / 4) * ∑ j, (M j).toReal) ≤ ∑ j, W j := by
    rw [show (2 : ℝ) * (q / 4) = q / 2 by ring]
    change ENNReal.ofReal _ ≤ _
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ q / 2), hsum]
    exact hhalf
  obtain ⟨J, _, hkeep, hgood⟩ :=
    WangZahlLot.Obl.wz_coarse_grains_assembly.select_dense_weights
      Finset.univ W (fun j => (M j).toReal) (by positivity : 0 ≤ q / 4)
      (fun j _ => ENNReal.toReal_nonneg)
      (fun j _ => ENNReal.sum_ne_top.mpr (fun i _ => hRfin i j)) hbudget
  let f := rIdx J
  let U := fun i j => R (f j) i
  have hf : Function.Injective f := rIdx_injective J
  have hidx (F : Fin D.L → ENNReal) : ∑ j : Fin J.card, F (f j) = ∑ j ∈ J, F j := by
    calc
      _ = ∑ j : J, F j.val := J.equivFin.symm.sum_comp _
      _ = _ := Finset.sum_coe_sort J F
  have hquarter : O (q / 4) * (∑ j, M j) ≤ ∑ j : Fin J.card, W (f j) := by
    rw [hidx]
    calc
      _ = (1 / 2 : ENNReal) * (O (q / 2) * ∑ j, M j) := by
        change ENNReal.ofReal _ * _ = _
        rw [show q / 4 = (1 / 2 : ℝ) * (q / 2) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num [O, ENNReal.ofReal_div_of_pos, mul_assoc]
      _ ≤ (1 / 2 : ENNReal) * ∑ j, W j := mul_le_mul' le_rfl hhalf
      _ ≤ (1 / 2 : ENNReal) * (2 * ∑ j ∈ J, W j) := mul_le_mul' le_rfl hkeep
      _ = _ := by
        rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hmass₁ : O (δ ^ h₁) * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (U i j) := by
    calc
      _ ≤ (O (q / 4) * O (δ ^ h)) * ∑ i, volume (Y i) := mul_le_mul' hmassbudget le_rfl
      _ ≤ O (q / 4) * (∑ i, ∑ j, volume (D.W i j)) := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl H.2.2.2.2.2.1
      _ = O (q / 4) * ∑ j, M j := congrArg (fun t : ENNReal => O (q / 4) * t) Finset.sum_comm
      _ ≤ ∑ j : Fin J.card, W (f j) := hquarter
      _ = _ := Finset.sum_comm
  have hmass₂ : O (δ ^ h₂) * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (U i j) :=
    (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hh₂)) le_rfl).trans hmass₁
  have hlocal (j : Fin J.card) : O ((q * τ / 4) * m (f j)) *
      volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j))) ≤ W (f j) := by
    calc
      _ = O (q / 4) * (O (τ * m (f j)) *
          volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j)))) := by
        change ENNReal.ofReal _ * _ = _
        rw [show q * τ / 4 * m (f j) = (q / 4) * (τ * m (f j)) by ring,
          ENNReal.ofReal_mul (by positivity : 0 ≤ q / 4), mul_assoc]
      _ ≤ O (q / 4) * M (f j) := mul_le_mul' le_rfl (haverage (f j))
      _ = O ((q / 4) * (M (f j)).toReal) := by
        change _ = ENNReal.ofReal _
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ q / 4), ENNReal.ofReal_toReal (hMfin (f j))]
      _ ≤ _ := (hgood (f j) (rIdx_mem J j)).2
  have hcount' (j : Fin J.card) (p : V) : bodyCount (fun i => U i j) p ≤ m (f j) := by
    apply le_trans _ (hcount (f j) p)
    change ({i | p ∈ U i j}.ncard : ℝ) ≤ ({i | p ∈ D.W i (f j)}.ncard : ℝ)
    exact_mod_cast Set.ncard_mono (show {i | p ∈ U i j} ⊆ {i | p ∈ D.W i (f j)} from
      fun i hi => hRsub i (f j) hi)
  have hdense (j : Fin J.card) : O (q * τ / 4) *
      volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j))) ≤ volume (⋃ i, U i j) := by
    let S := ⋃ i, U i j
    have hSm : MeasurableSet S := MeasurableSet.iUnion fun i => (hR (f j) i).1
    have hdom := incidence_measure_domination (fun i => U i j)
      (fun i => (hR (f j) i).1) (hm (f j)).le (hcount' j) S hSm
    have heq : shadingMeasure (fun i => U i j) S = W (f j) := by
      rw [shadingMeasure_apply _ hSm]
      apply Finset.sum_congr rfl
      intro i _
      rw [inter_eq_left.mpr (subset_iUnion (fun i => U i j) i)]
    rw [heq] at hdom
    have hh := (hlocal j).trans hdom
    change ENNReal.ofReal (q * τ / 4 * m (f j)) * _ ≤ _ at hh
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ q * τ / 4)] at hh
    have he : O (q * τ / 4) * O (m (f j)) *
        volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j))) =
        O (m (f j)) * (O (q * τ / 4) *
          volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j)))) := by ring
    rw [he] at hh
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (hm (f j))).ne'
      ENNReal.ofReal_ne_top).mp hh
  let D₀ := D.select D.s f id (D.γ ∘ f)
  have H₀ : D₀.Valid ω ζ δ h₁ ρ c x v Y 1 := by
    apply valid_select_prisms D hδ hδ1 hh₁ H f hf
    exact hmass₁.trans (Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => measure_mono (hRsub i (f j)))
  refine ⟨J.card, f, U, hf, fun i j => hR (f j) i, ?_, hcount', hlocal⟩
  apply valid_relative_pieces D₀ hδ (by positivity : 0 < q / 2) H₀ U
    (fun i j => ⟨(hR (f j) i).1, hRsub i (f j)⟩) hmass₂
    (fun j => (mul_le_mul' hdensitybudget le_rfl).trans (hdense j))
    (fun j => hRrelative (f j)) hbroadbudget

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
