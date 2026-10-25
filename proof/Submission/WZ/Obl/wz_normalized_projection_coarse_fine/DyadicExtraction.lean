-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.DyadicExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.LaminarExtraction
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.DyadicCells
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.SeparatedSelection

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Simultaneous integral extraction for all dyadic cells down to a fixed depth. -/
theorem dyadic_weighted_extraction {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (q : α → EuclideanSpace ℝ (Fin d)) (J : ℕ) (w : α → ℝ)
    (hw : ∀ a ∈ U, 0 ≤ w a ∧ w a ≤ 1)
    (hcap : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      (∑ a ∈ U.filter (fun a => dyadicLabel k (q a) = l), w a) ≤ (2 : ℝ) ^ (J - k)) :
    ∃ Q ⊆ U, (∑ a ∈ U, w a) ≤ Q.card ∧
      ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
        (Q.filter (fun a => dyadicLabel k (q a) = l)).card ≤ 2 ^ (J - k) := by
  classical
  let I := Fin (J + 1) × {a // a ∈ U}
  let C (i : I) := U.filter (fun a => dyadicLabel i.1 (q a) = dyadicLabel i.1 (q i.2))
  have hCU (i : I) : C i ⊆ U := Finset.filter_subset _ _
  have hlam (i j : I) : C i ⊆ C j ∨ C j ⊆ C i ∨ Disjoint (C i) (C j) := by
    exact nested_partition_cells_laminar U (fun k a => dyadicLabel k (q a))
      (fun j k hjk a b hab => dyadicLabel_eq_of_finer_eq hjk hab) _ _ _ _
  have hcaps (i : I) : ∑ a ∈ C i, w a ≤ ((2 ^ (J - i.1.val) : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      hcap i.1 (by omega) (dyadicLabel i.1 (q i.2))
  obtain ⟨Q, hQU, hmass, hQcap⟩ := indexed_laminar_weighted_extraction U C
    (fun i => 2 ^ (J - i.1.val)) w hCU hlam hw hcaps
  refine ⟨Q, hQU, hmass, ?_⟩
  intro k hk l
  by_cases he : Q.filter (fun a => dyadicLabel k (q a) = l) = ∅
  · simp [he]
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨haQ, hal⟩ := Finset.mem_filter.mp ha
  let i : I := (⟨k, by omega⟩, ⟨a, hQU haQ⟩)
  have hcell : Q ∩ C i = Q.filter (fun a => dyadicLabel k (q a) = l) := by
    ext b
    simp only [C, i, hal, Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hQU h.1, h.2⟩⟩
  simpa only [hcell] using hQcap i

/-- At the finest scale the extracted points have bounded multiplicity in each metric ball. -/
theorem dyadic_extraction_ball_count {α : Type*} [DecidableEq α] {d J : ℕ}
    (Q : Finset α) (q : α → EuclideanSpace ℝ (Fin d))
    (hcell : ∀ l : Fin d → ℤ,
      (Q.filter (fun a => dyadicLabel J (q a) = l)).card ≤ 1)
    (q₀ : EuclideanSpace ℝ (Fin d)) :
    (Q.filter (fun a => q a ∈ Metric.ball q₀ (((2 : ℝ) ^ J)⁻¹))).card ≤ 3 ^ d := by
  have h := ball_count_le_of_dyadic_cells Q q (M := 1)
    (fun l => by exact_mod_cast hcell l) q₀ le_rfl
  simp only [mul_one] at h
  exact_mod_cast h

lemma exists_dyadic_scale {J : ℕ} {r : ℝ}
    (hδr : ((2 : ℝ) ^ J)⁻¹ ≤ r) (hr1 : r ≤ 1) :
    ∃ k ≤ J, r ≤ ((2 : ℝ) ^ k)⁻¹ ∧ ((2 : ℝ) ^ k)⁻¹ < 2 * r := by
  have hr : 0 < r := (by positivity : 0 < ((2 : ℝ) ^ J)⁻¹).trans_le hδr
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hpow (n : ℕ) : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
    simp [div_pow]
  have hkJ : k ≤ J := by
    by_contra hk
    have hlt : (2 : ℝ) ^ J < 2 ^ k := pow_lt_pow_right₀ (by norm_num) (not_le.mp hk)
    have hi : ((2 : ℝ) ^ k)⁻¹ < ((2 : ℝ) ^ J)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by positivity)).mpr hlt
    rw [hpow] at hk₂
    linarith
  refine ⟨k, hkJ, by rwa [hpow] at hk₂, ?_⟩
  rw [pow_succ, hpow] at hk₁
  linarith

/-- The dyadic linear quotas give a Katz--Tao bound at every intervening radius. -/
theorem dyadic_quotas_ball_count {α : Type*} [DecidableEq α] {d J : ℕ}
    (Q : Finset α) (q : α → EuclideanSpace ℝ (Fin d))
    (hcell : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      (Q.filter (fun a => dyadicLabel k (q a) = l)).card ≤ 2 ^ (J - k))
    (q₀ : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hδr : ((2 : ℝ) ^ J)⁻¹ ≤ r) (hr1 : r ≤ 1) :
    ((Q.filter (fun a => q a ∈ Metric.ball q₀ r)).card : ℝ) ≤
      2 * (3 : ℝ) ^ d * (r / ((2 : ℝ) ^ J)⁻¹) := by
  obtain ⟨k, hkJ, hrk, hkr⟩ := exists_dyadic_scale hδr hr1
  have hb := ball_count_le_of_dyadic_cells Q q (M := (2 : ℝ) ^ (J - k))
    (fun l => by exact_mod_cast hcell k hkJ l) q₀ hrk
  have he : (2 : ℝ) ^ k * 2 ^ (J - k) = 2 ^ J := by
    rw [← pow_add, Nat.add_sub_of_le hkJ]
  calc
    _ ≤ (3 : ℝ) ^ d * 2 ^ (J - k) := hb
    _ = (3 : ℝ) ^ d * (((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ J) := by
      rw [← he, inv_mul_cancel_left₀ (by positivity)]
    _ ≤ (3 : ℝ) ^ d * ((2 * r) * (2 : ℝ) ^ J) := by gcongr
    _ = _ := by rw [div_inv_eq_mul]; ring

/-- Convert a sublinear Frostman distribution into dyadic linear count quotas. -/
theorem dyadic_frostman_quota_extraction {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (q : α → EuclideanSpace ℝ (Fin d)) (J : ℕ)
    {K s : ℝ} (hK : 0 < K) (hs : s ≤ 1)
    (hmin : 1 ≤ K * (((2 : ℝ) ^ J)⁻¹) ^ s * U.card)
    (hcount : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (q a) = l)).card : ℝ) ≤
        K * (((2 : ℝ) ^ k)⁻¹) ^ s * U.card) :
    ∃ Q ⊆ U, 1 / (K * (((2 : ℝ) ^ J)⁻¹) ^ s) ≤ (Q.card : ℝ) ∧
      ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
        (Q.filter (fun a => dyadicLabel k (q a) = l)).card ≤ 2 ^ (J - k) := by
  classical
  let δ := ((2 : ℝ) ^ J)⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hp : 0 < δ ^ s := Real.rpow_pos_of_pos hδ _
  have hU : 0 < (U.card : ℝ) := by
    by_contra h
    have hz : (U.card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [hz, mul_zero] at hmin
    norm_num at hmin
  let D := K * δ ^ s * (U.card : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hw : ∀ a ∈ U, 0 ≤ 1 / D ∧ 1 / D ≤ 1 := by
    intro a ha
    exact ⟨by positivity, (div_le_one hD).mpr hmin⟩
  have hcap : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      (∑ _a ∈ U.filter (fun a => dyadicLabel k (q a) = l), 1 / D) ≤
        (2 : ℝ) ^ (J - k) := by
    intro k hk l
    have he : ((2 : ℝ) ^ k)⁻¹ / δ = (2 : ℝ) ^ (J - k) := by
      dsimp [δ]
      have hpow : (2 : ℝ) ^ J = 2 ^ k * 2 ^ (J - k) := by
        rw [← pow_add, Nat.add_sub_of_le hk]
      rw [div_inv_eq_mul, hpow, inv_mul_cancel_left₀ (by positivity)]
    have hratio : 1 ≤ ((2 : ℝ) ^ k)⁻¹ / δ := by
      rw [he]
      exact one_le_pow₀ (by norm_num)
    calc
      _ = ((U.filter (fun a => dyadicLabel k (q a) = l)).card : ℝ) / D := by
        simp [div_eq_mul_inv]
      _ ≤ (K * (((2 : ℝ) ^ k)⁻¹) ^ s * U.card) / D :=
        div_le_div_of_nonneg_right (hcount k hk l) hD.le
      _ = (((2 : ℝ) ^ k)⁻¹ / δ) ^ s := by
        rw [Real.div_rpow (by positivity) hδ.le]
        dsimp [D]
        field_simp
      _ ≤ ((2 : ℝ) ^ k)⁻¹ / δ := Real.rpow_le_self_of_one_le hratio hs
      _ = _ := he
  obtain ⟨Q, hQU, hmass, hQcap⟩ := dyadic_weighted_extraction U q J (fun _ => 1 / D) hw hcap
  refine ⟨Q, hQU, ?_, hQcap⟩
  calc
    _ = ∑ _a ∈ U, 1 / D := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change 1 / (K * δ ^ s) = (U.card : ℝ) * (1 / (K * δ ^ s * U.card))
      field_simp
    _ ≤ Q.card := hmass

/-- A finite dyadic Frostman family has a separated Katz--Tao subset with an explicit size. -/
theorem dyadic_frostman_separated_extraction {α : Type*} [DecidableEq α] {d : ℕ}
    (U : Finset α) (q : α → EuclideanSpace ℝ (Fin d)) (J : ℕ)
    {K s : ℝ} (hK : 0 < K) (hs : s ≤ 1)
    (hmin : 1 ≤ K * (((2 : ℝ) ^ J)⁻¹) ^ s * U.card)
    (hcount : ∀ k, k ≤ J → ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (q a) = l)).card : ℝ) ≤
        K * (((2 : ℝ) ^ k)⁻¹) ^ s * U.card) :
    ∃ V ⊆ U,
      1 / (K * (((2 : ℝ) ^ J)⁻¹) ^ s) ≤ ((3 : ℝ) ^ d + 1) * V.card ∧
      (∀ a ∈ V, ∀ b ∈ V, a ≠ b → ((2 : ℝ) ^ J)⁻¹ ≤ dist (q a) (q b)) ∧
      ∀ (q₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ), ((2 : ℝ) ^ J)⁻¹ ≤ r → r ≤ 1 →
        ((V.filter (fun a => q a ∈ Metric.ball q₀ r)).card : ℝ) ≤
          2 * (3 : ℝ) ^ d * (r / ((2 : ℝ) ^ J)⁻¹) := by
  classical
  obtain ⟨Q, hQU, hmass, hQcap⟩ := dyadic_frostman_quota_extraction U q J hK hs hmin hcount
  have hlocal (a : α) :
      (Q.filter (fun b => q b ∈ Metric.ball (q a) (((2 : ℝ) ^ J)⁻¹))).card ≤ 3 ^ d := by
    apply dyadic_extraction_ball_count Q q
    intro l
    simpa using hQcap J le_rfl l
  obtain ⟨V, hVQ, hVmass, hVsep⟩ := separated_weighted_subset Q q (fun _ => 1)
    (K := 3 ^ d) (fun a _ => hlocal a)
  have hcard : (Q.card : ℝ) ≤ ((3 : ℝ) ^ d + 1) * V.card := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one] using hVmass
  refine ⟨V, hVQ.trans hQU, hmass.trans hcard, hVsep, ?_⟩
  intro q₀ r hδr hr1
  have hc : (V.filter (fun a => q a ∈ Metric.ball q₀ r)).card ≤
      (Q.filter (fun a => q a ∈ Metric.ball q₀ r)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hVQ)
  exact (show ((V.filter (fun a => q a ∈ Metric.ball q₀ r)).card : ℝ) ≤
      ((Q.filter (fun a => q a ∈ Metric.ball q₀ r)).card : ℝ) by exact_mod_cast hc).trans
    (dyadic_quotas_ball_count Q q hQcap q₀ hδr hr1)

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
