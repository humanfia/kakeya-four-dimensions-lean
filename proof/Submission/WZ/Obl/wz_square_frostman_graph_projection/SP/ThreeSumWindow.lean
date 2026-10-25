-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ThreeSumWindow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarCollisionCounts

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Reorder a finite three-variable count to expose its last-variable fibers. -/
theorem triple_filter_card_reordered {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (R : I → J → K → Prop) :
    ((Finset.univ.filter (fun p : I × J × K => R p.1 p.2.1 p.2.2)).card : ℝ) =
      ∑ i : I, ∑ k : K, ((Finset.univ.filter (fun j => R i j k)).card : ℝ) := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

/-- Three approximate sums determine an output point and both intermediate
coordinates with bounded multiplicity. -/
theorem three_sum_window_card (V A B : Finset ℝ) (a b : V → ℝ)
    {δ c t z₁ z₂ z₃ : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hct : c ≤ t) (ht1 : t ≤ 1)
    (hVsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → δ ≤ dist x y)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hrep : ∀ v : V, a v + t * b v = (v : ℝ)) :
    c * ((Finset.univ.filter (fun p : V × A × B =>
      dist (a p.1 + t * (p.2.2 : ℝ)) z₁ ≤ δ ∧
      dist ((p.2.1 : ℝ) + t * (p.2.2 : ℝ)) z₂ ≤ δ ∧
      dist ((p.2.1 : ℝ) + t * b p.1) z₃ ≤ δ)).card : ℝ) ≤ 288 := by
  classical
  have ht : 0 < t := hc.trans_le hct
  have hc1 : c ≤ 1 := hct.trans ht1
  let W (v : V) (x : A) (y : B) : Prop :=
    dist (a v + t * (y : ℝ)) z₁ ≤ δ ∧
      dist ((x : ℝ) + t * (y : ℝ)) z₂ ≤ δ ∧ dist ((x : ℝ) + t * b v) z₃ ≤ δ
  have himp (v : V) (x : A) (y : B) (hw : W v x y) : dist (v : ℝ) (z₁ - z₂ + z₃) ≤ 3 * δ := by
    have h₁ := abs_le.mp (show |a v + t * (y : ℝ) - z₁| ≤ δ by simpa only [Real.dist_eq] using hw.1)
    have h₂ := abs_le.mp (show |(x : ℝ) + t * (y : ℝ) - z₂| ≤ δ by simpa only [Real.dist_eq] using hw.2.1)
    have h₃ := abs_le.mp (show |(x : ℝ) + t * b v - z₃| ≤ δ by simpa only [Real.dist_eq] using hw.2.2)
    rw [← hrep v, Real.dist_eq, abs_le]
    constructor <;> nlinarith
  have hAwindow (y : B) :
      ((Finset.univ.filter (fun x : A => dist ((x : ℝ) + t * (y : ℝ)) z₂ ≤ δ)).card : ℝ) ≤ 6 := by
    rw [finset_subtype_filter_card A (fun x : ℝ => dist (x + t * (y : ℝ)) z₂ ≤ δ)]
    apply real_separated_two_radius_card hδ _
      (fun x hx x' hx' hne => hAsep x (Finset.mem_filter.mp hx).1 x' (Finset.mem_filter.mp hx').1 hne)
    intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    have hid : dist x (z₂ - t * (y : ℝ)) = dist (x + t * (y : ℝ)) z₂ := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring
    rw [hid]
    linarith
  have hBwindow (v : V) :
      ((Finset.univ.filter (fun y : B => dist (a v + t * (y : ℝ)) z₁ ≤ δ)).card : ℝ) ≤ 6 / c := by
    rw [finset_subtype_filter_card B (fun y : ℝ => dist (a v + t * y) z₁ ≤ δ)]
    apply (le_div_iff₀ hc).mpr
    have hh := real_separated_affine_window hδ hc hc1
      (a := t) (b := a v - z₁) (by simpa only [abs_of_pos ht] using hct)
      (B.filter (fun y => dist (a v + t * y) z₁ ≤ δ))
      (fun y hy y' hy' hne => hBsep y (Finset.mem_filter.mp hy).1 y' (Finset.mem_filter.mp hy').1 hne)
      (by
        intro y hy
        have hwin := (Finset.mem_filter.mp hy).2
        have hid : |t * y + (a v - z₁)| = dist (a v + t * y) z₁ := by
          rw [Real.dist_eq]
          congr 1
          ring
        rw [hid]
        linarith)
    simpa only [mul_comm] using hh
  have hlocal (v : V) (y : B) : ((Finset.univ.filter (fun x : A => W v x y)).card : ℝ) ≤
      if dist (a v + t * (y : ℝ)) z₁ ≤ δ then 6 else 0 := by
    by_cases hy : dist (a v + t * (y : ℝ)) z₁ ≤ δ
    · rw [if_pos hy]
      have hsub : Finset.univ.filter (fun x : A => W v x y) ⊆
          Finset.univ.filter (fun x : A => dist ((x : ℝ) + t * (y : ℝ)) z₂ ≤ δ) := by
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.2.1⟩
      exact (show ((Finset.univ.filter (fun x : A => W v x y)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : A => dist ((x : ℝ) + t * (y : ℝ)) z₂ ≤ δ)).card : ℝ) by
          exact_mod_cast Finset.card_le_card hsub).trans (hAwindow y)
    · simp only [W, hy, false_and, Finset.filter_false, Finset.card_empty, Nat.cast_zero, ite_false, le_refl]
  have hrow (v : V) : (∑ y : B, ((Finset.univ.filter (fun x : A => W v x y)).card : ℝ)) ≤
      if dist (v : ℝ) (z₁ - z₂ + z₃) ≤ 3 * δ then 36 / c else 0 := by
    by_cases hv : dist (v : ℝ) (z₁ - z₂ + z₃) ≤ 3 * δ
    · rw [if_pos hv]
      calc
        _ ≤ ∑ y : B, if dist (a v + t * (y : ℝ)) z₁ ≤ δ then (6 : ℝ) else 0 :=
          Finset.sum_le_sum (fun y _ => hlocal v y)
        _ = ((Finset.univ.filter (fun y : B => dist (a v + t * (y : ℝ)) z₁ ≤ δ)).card : ℝ) * 6 := by
          rw [← Finset.sum_filter]
          simp
        _ ≤ (6 / c) * 6 := mul_le_mul_of_nonneg_right (hBwindow v) (by norm_num)
        _ = _ := by ring
    · rw [if_neg hv]
      have hempty (y : B) : Finset.univ.filter (fun x : A => W v x y) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        exact hv (himp v x y (Finset.mem_filter.mp hx).2)
      simp only [hempty, Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, le_refl]
  have hVwindow :
      ((Finset.univ.filter (fun v : V => dist (v : ℝ) (z₁ - z₂ + z₃) ≤ 3 * δ)).card : ℝ) ≤ 8 := by
    rw [finset_subtype_filter_card V (fun v : ℝ => dist v (z₁ - z₂ + z₃) ≤ 3 * δ)]
    have hh := real_separated_ball_card hδ (by positivity : 0 ≤ 3 * δ)
      (V.filter (fun v => dist v (z₁ - z₂ + z₃) ≤ 3 * δ))
      (fun x hx y hy hne => hVsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne)
      (fun v hv => (Finset.mem_filter.mp hv).2)
    nlinarith
  have htotal : ((Finset.univ.filter (fun p : V × A × B => W p.1 p.2.1 p.2.2)).card : ℝ) ≤ 288 / c := by
    calc
      _ = ∑ v : V, ∑ y : B, ((Finset.univ.filter (fun x : A => W v x y)).card : ℝ) := by
        simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
          Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using triple_filter_card_reordered W
      _ ≤ ∑ v : V, if dist (v : ℝ) (z₁ - z₂ + z₃) ≤ 3 * δ then (36 / c) else 0 :=
        Finset.sum_le_sum (fun v _ => hrow v)
      _ = ((Finset.univ.filter (fun v : V => dist (v : ℝ) (z₁ - z₂ + z₃) ≤ 3 * δ)).card : ℝ) * (36 / c) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ 8 * (36 / c) := mul_le_mul_of_nonneg_right hVwindow (by positivity)
      _ = _ := by ring
  have hh := (le_div_iff₀ hc).mp htotal
  simpa only [mul_comm, W] using hh

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
