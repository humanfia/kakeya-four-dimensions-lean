-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain.SharpCoarseCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_fibre_multiplicity_gain.CoarseCount

/-!
# The quadratic coarse point count

The direction sphere has two effective coordinates: choose a coordinate with
absolute value at least one half and record its sign. The other two coordinates
then determine the direction with a uniform Lipschitz bound.

Ported from x0449's `SharpCoarseCount.lean` on o152's branch x0449 (namespace renamed).
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

lemma exists_large_coordinate {v : Space} (hv : ‖v‖ = 1) :
    ∃ j : Fin 3, (1 / 2 : ℝ) ≤ |v j| := by
  have hs : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq v
    rw [hv, Fin.sum_univ_three] at h
    norm_num at h
    exact h.symm
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have q0 : v 0 ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (v 0)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 h0
  have q1 : v 1 ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (v 1)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 h1
  have q2 : v 2 ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (v 2)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 h2
  nlinarith

lemma abs_sq_sub_sq_le {a b ε : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : |a - b| ≤ ε) : |a ^ 2 - b ^ 2| ≤ 2 * ε := by
  calc |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by rw [← abs_mul]; congr 1; ring
    _ ≤ ε * (1 + 1) := mul_le_mul hab ((abs_add_le _ _).trans (add_le_add ha hb))
      (abs_nonneg _) ((abs_nonneg _).trans hab)
    _ = _ := by ring

lemma sphere_chart_close {u v : Space} {ε : ℝ} (hε : 0 < ε)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (j : Fin 3)
    (huj : (1 / 2 : ℝ) ≤ |u j|) (hvj : (1 / 2 : ℝ) ≤ |v j|)
    (hsign : (0 ≤ u j ↔ 0 ≤ v j))
    (h1 : |u (j + 1) - v (j + 1)| < ε)
    (h2 : |u (j + 2) - v (j + 2)| < ε) : ‖u - v‖ ≤ 10 * ε := by
  have hsq : u j ^ 2 - v j ^ 2 =
      (v (j + 1) ^ 2 - u (j + 1) ^ 2) + (v (j + 2) ^ 2 - u (j + 2) ^ 2) := by
    have hU := EuclideanSpace.real_norm_sq_eq u
    have hV := EuclideanSpace.real_norm_sq_eq v
    rw [hu, Fin.sum_univ_three] at hU
    rw [hv, Fin.sum_univ_three] at hV
    fin_cases j <;> dsimp at * <;> linarith
  have hbound : ∀ w : Space, ‖w‖ = 1 → ∀ i : Fin 3, |w i| ≤ 1 := by
    intro w hw i
    exact (WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm w i).trans_eq hw
  have hsum : 1 ≤ |u j + v j| := by
    by_cases hp : 0 ≤ u j
    · have hp' := hsign.mp hp
      rw [abs_of_nonneg hp] at huj
      rw [abs_of_nonneg hp'] at hvj
      rw [abs_of_nonneg (add_nonneg hp hp')]
      linarith
    · have hp' : v j < 0 := lt_of_not_ge (fun h => hp (hsign.mpr h))
      have hp0 : u j < 0 := lt_of_not_ge hp
      rw [abs_of_neg hp0] at huj
      rw [abs_of_neg hp'] at hvj
      rw [abs_of_neg (add_neg hp0 hp')]
      linarith
  have hj : |u j - v j| ≤ 4 * ε := by
    calc |u j - v j| ≤ |u j - v j| * |u j + v j| :=
          le_mul_of_one_le_right (abs_nonneg _) hsum
      _ = |u j ^ 2 - v j ^ 2| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |v (j + 1) ^ 2 - u (j + 1) ^ 2| + |v (j + 2) ^ 2 - u (j + 2) ^ 2| :=
          by rw [hsq]; exact abs_add_le _ _
      _ ≤ 2 * ε + 2 * ε := add_le_add
        (abs_sq_sub_sq_le (hbound v hv _) (hbound u hu _) (by simpa [abs_sub_comm] using h1.le))
        (abs_sq_sub_sq_le (hbound v hv _) (hbound u hu _) (by simpa [abs_sub_comm] using h2.le))
      _ = 4 * ε := by ring
  have hcoords : ∀ i : Fin 3, |u i - v i| < 5 * ε := by
    intro i
    fin_cases j <;> fin_cases i <;> dsimp at * <;> linarith
  have h := coarse_norm_sub_le (hcoords 0) (hcoords 1) (hcoords 2)
  linarith


/-- At most `C ρ⁻²` essentially distinct unit `ρ`-tubes contain a given point. -/
theorem coarse_point_count_quadratic : ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ (N : ℕ) (y w : Fin N → Space), (∀ k, ‖w k‖ = 1) → Distinct ρ N y w →
    ∀ p : Space, (Set.ncard {k | p ∈ Tube ρ (y k) (w k)} : ℝ) ≤ C / ρ ^ 2 := by
  classical
  refine ⟨6 * 80 * 1201 ^ 2 * 800 ^ 3, by positivity, ?_⟩
  intro ρ hρ hρ1 N y w hw hD p
  let ε : ℝ := ρ / 400
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hdec : ∀ k, ∃ t : ℝ, ∃ q : Space, p ∈ Tube ρ (y k) (w k) →
      0 ≤ t ∧ t ≤ 1 ∧ ‖q‖ < ρ ∧ p = y k + t • w k + q := by
    intro k
    by_cases hk : p ∈ Tube ρ (y k) (w k)
    · obtain ⟨t, q, h⟩ := coarse_decomp hk
      exact ⟨t, q, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose t q htq using hdec
  have hlarge : ∀ k, ∃ j : Fin 3, (1 / 2 : ℝ) ≤ |w k j| :=
    fun k => exists_large_coordinate (hw k)
  choose J hJ using hlarge
  let label : Fin N → Fin 3 × Bool × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := fun k =>
    (J k, decide (0 ≤ w k (J k)), ⌊t k / (1 / 40)⌋₊,
      ⌊(w k (J k + 1) + 1) / ε⌋₊, ⌊(w k (J k + 2) + 1) / ε⌋₊,
      ⌊(q k 0 + ρ) / ε⌋₊, ⌊(q k 1 + ρ) / ε⌋₊, ⌊(q k 2 + ρ) / ε⌋₊)
  let S : Set (Fin N) := {k | p ∈ Tube ρ (y k) (w k)}
  let B : Finset (Fin 3 × Bool × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
    Finset.univ ×ˢ Finset.univ ×ˢ Finset.range 80 ×ˢ
      Finset.range ⌈3 / ε⌉₊ ×ˢ Finset.range ⌈3 / ε⌉₊ ×ˢ
      Finset.range 800 ×ˢ Finset.range 800 ×ˢ Finset.range 800
  have heq : ⌈2 * ρ / ε⌉₊ = 800 := by
    have he : 2 * ρ / ε = 800 := by dsimp [ε]; field_simp; ring
    rw [he]; norm_num
  have hmaps : ∀ k ∈ S, label k ∈ (B : Set _) := by
    intro k hk
    obtain ⟨ht0, ht1, hq, -⟩ := htq k hk
    have hw1 := abs_le.mp
      ((WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm (w k) (J k + 1)).trans_eq (hw k))
    have hw2 := abs_le.mp
      ((WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm (w k) (J k + 2)).trans_eq (hw k))
    have hq0 := abs_lt.mp
      ((WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm (q k) 0).trans_lt hq)
    have hq1 := abs_lt.mp
      ((WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm (q k) 1).trans_lt hq)
    have hq2 := abs_lt.mp
      ((WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm (q k) 2).trans_lt hq)
    simp only [Finset.mem_coe, B, label, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range]
    rw [← heq]
    refine ⟨?_, WangZahlLot.Obl.wz_tube_packing_bound.floor_lt_ceil hε ?_ ?_,
      WangZahlLot.Obl.wz_tube_packing_bound.floor_lt_ceil hε ?_ ?_,
      WangZahlLot.Obl.wz_tube_packing_bound.floor_lt_ceil hε ?_ ?_,
      WangZahlLot.Obl.wz_tube_packing_bound.floor_lt_ceil hε ?_ ?_,
      WangZahlLot.Obl.wz_tube_packing_bound.floor_lt_ceil hε ?_ ?_⟩
    · have hh := WangZahlLot.Obl.wz_tube_packing_bound.floor_lt_ceil
        (by norm_num : (0 : ℝ) < 1 / 40) ht0 (show t k < 2 by linarith)
      norm_num at hh
      exact hh
    all_goals linarith
  have hinj : Set.InjOn label S := by
    intro k hk k' hk' hkk'
    by_contra hne
    obtain ⟨ht0, ht1, hq, hp⟩ := htq k hk
    obtain ⟨ht0', ht1', hq', hp'⟩ := htq k' hk'
    simp only [label, Prod.mk.injEq] at hkk'
    obtain ⟨eJ, eSign, e0, e1, e2, e3, e4, e5⟩ := hkk'
    rw [← eJ] at eSign e1 e2
    have bw := fun (u : Space) (hu : ‖u‖ = 1) (j : Fin 3) => abs_le.mp
      ((WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm u j).trans_eq hu)
    have bq := fun (u : Space) (hu : ‖u‖ < ρ) (j : Fin 3) => abs_lt.mp
      ((WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm u j).trans_lt hu)
    have a1 := bw (w k) (hw k) (J k + 1)
    have a2 := bw (w k) (hw k) (J k + 2)
    have b1 := bw (w k') (hw k') (J k + 1)
    have b2 := bw (w k') (hw k') (J k + 2)
    have c0 := bq (q k) hq 0
    have c1 := bq (q k) hq 1
    have c2 := bq (q k) hq 2
    have d0 := bq (q k') hq' 0
    have d1 := bq (q k') hq' 1
    have d2 := bq (q k') hq' 2
    have f0 := WangZahlLot.Obl.wz_tube_packing_bound.abs_sub_lt_of_floor_eq
      (by norm_num) ht0 ht0' e0
    have f1 := WangZahlLot.Obl.wz_tube_packing_bound.abs_sub_lt_of_floor_eq hε
      (by linarith) (by linarith) e1
    have f2 := WangZahlLot.Obl.wz_tube_packing_bound.abs_sub_lt_of_floor_eq hε
      (by linarith) (by linarith) e2
    have f3 := WangZahlLot.Obl.wz_tube_packing_bound.abs_sub_lt_of_floor_eq hε
      (by linarith) (by linarith) e3
    have f4 := WangZahlLot.Obl.wz_tube_packing_bound.abs_sub_lt_of_floor_eq hε
      (by linarith) (by linarith) e4
    have f5 := WangZahlLot.Obl.wz_tube_packing_bound.abs_sub_lt_of_floor_eq hε
      (by linarith) (by linarith) e5
    simp only [add_sub_add_right_eq_sub] at f1 f2 f3 f4 f5
    have hsign : 0 ≤ w k (J k) ↔ 0 ≤ w k' (J k) := by
      simpa only [decide_eq_decide] using eSign
    have hwk : ‖w k - w k'‖ ≤ ρ / 40 := by
      have hj' : (1 / 2 : ℝ) ≤ |w k' (J k)| := by rw [eJ]; exact hJ k'
      have h := sphere_chart_close hε (hw k) (hw k') (J k) (hJ k) hj' hsign f1 f2
      dsimp [ε] at h
      linarith
    have hqk : ‖q k - q k'‖ ≤ ρ / 40 := by
      have h := coarse_norm_sub_le f3 f4 f5
      dsimp [ε] at h
      linarith
    have hQ : ‖t k' • (w k - w k') + (q k - q k')‖ ≤ ρ / 20 := by
      calc ‖t k' • (w k - w k') + (q k - q k')‖
          ≤ ‖t k' • (w k - w k')‖ + ‖q k - q k'‖ := norm_add_le _ _
        _ = |t k'| * ‖w k - w k'‖ + ‖q k - q k'‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * (ρ / 40) + ρ / 40 := by
            gcongr
            rw [abs_of_nonneg ht0']; exact ht1'
        _ = ρ / 20 := by ring
    have hy : y k' = y k + (t k - t k') • w k + (t k' • (w k - w k') + (q k - q k')) := by
      have h := hp.symm.trans hp'
      linear_combination (norm := module) -h
    exact coarse_not_close hρ (hD k k' hne)
      (f0.le.trans (by norm_num)) (by linarith) hQ hy
  have hcard := Set.ncard_le_ncard_of_injOn label hmaps hinj
  rw [Set.ncard_coe_finset] at hcard
  simp only [B, Finset.card_product, Finset.card_range, Finset.card_univ,
    Fintype.card_fin, Fintype.card_bool] at hcard
  have hM : (⌈3 / ε⌉₊ : ℝ) ≤ 1201 / ρ := by
    have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 / ε by positivity)
    have h2 : 3 / ε = 1200 / ρ := by dsimp [ε]; ring
    have h3 : 1 ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
    have h4 : 1201 / ρ = 1200 / ρ + 1 / ρ := by ring
    linarith
  have hn : (S.ncard : ℝ) ≤ 6 * 80 * (⌈3 / ε⌉₊ : ℝ) ^ 2 * 800 ^ 3 := by
    have hnNat : S.ncard ≤ 6 * 80 * ⌈3 / ε⌉₊ ^ 2 * 800 ^ 3 := by
      convert hcard using 1 <;> ring
    exact_mod_cast hnNat

  calc (S.ncard : ℝ) ≤ 6 * 80 * (⌈3 / ε⌉₊ : ℝ) ^ 2 * 800 ^ 3 := hn
    _ ≤ 6 * 80 * (1201 / ρ) ^ 2 * 800 ^ 3 := by gcongr
    _ = 6 * 80 * 1201 ^ 2 * 800 ^ 3 / ρ ^ 2 := by rw [div_pow]; ring

end WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain
