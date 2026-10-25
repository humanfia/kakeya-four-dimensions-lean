-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.RichStrip.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_thin_tubes_bootstrap.StripCount

/-!
# The L² count of rich strips

If every strip of an `r`-separated family `J` contains at least `l * #Y` points
of a `(r, 1, C)`-Frostman set `Y` of norm `≤ 4`, then
`l ^ 2 * #J ≤ 16000 * C * (1 + log (1 / r))`: count pairs of points of `Y` in a
common strip, using the one- and two-point strip counts and dyadic shells.
-/

namespace WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap

open Finset
open scoped Classical

lemma sum_sq_card_filter (Y : Finset E2) (J : Finset (E2 × E2)) (S : E2 × E2 → E2 → Prop)
    [∀ j y, Decidable (S j y)] :
    ∑ j ∈ J, ((Y.filter (S j)).card : ℝ) ^ 2 =
      ∑ y ∈ Y, ∑ y' ∈ Y, ((J.filter (fun j => S j y ∧ S j y')).card : ℝ) := by
  have h1 : ∀ j, ((Y.filter (S j)).card : ℝ) = ∑ y ∈ Y, if S j y then (1 : ℝ) else 0 := by
    intro j; rw [Finset.sum_boole]
  simp_rw [h1, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y' _
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl; intro j _
  by_cases h : S j y <;> by_cases h' : S j y' <;> simp [h, h']

/-- Dyadic shells: `∑ 1 / |y - y'|` over far points is `≤ 2 C K #Y`. -/
lemma shell_sum {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (Y : Finset E2) (y : E2)
    (hY8 : ∀ y' ∈ Y, ‖y - y'‖ ≤ 8)
    (hFr : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((Y.filter (fun z => z ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Y.card)
    (K : ℕ) (hK : 8 < 2 ^ K * (4 * r)) :
    ∑ y' ∈ Y.filter (fun z => 4 * r ≤ ‖y - z‖), 1 / ‖y - y'‖ ≤ 2 * C * K * Y.card := by
  classical
  set f : E2 → ℝ := fun y' => ∑ k ∈ range K,
    if y' ∈ Metric.closedBall y (2 ^ (k + 1) * (4 * r)) then 1 / (2 ^ k * (4 * r)) else 0 with hfdef
  have hf0 : ∀ y', 0 ≤ f y' := by
    intro y'; apply Finset.sum_nonneg; intro k _; split_ifs <;> positivity
  have hpt : ∀ y' ∈ Y.filter (fun z => 4 * r ≤ ‖y - z‖), 1 / ‖y - y'‖ ≤ f y' := by
    intro y' hy'
    obtain ⟨hy'Y, hfar⟩ := Finset.mem_filter.mp hy'
    set d := ‖y - y'‖ with hddef
    have h4r : 0 < 4 * r := by positivity
    have hd0 : 0 < d := lt_of_lt_of_le h4r hfar
    have hx1 : 1 ≤ d / (4 * r) := by rw [le_div_iff₀ h4r]; linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
    rw [le_div_iff₀ h4r] at hn1
    rw [div_lt_iff₀ h4r] at hn2
    have hnK : n < K := by
      have : (2 : ℝ) ^ n < 2 ^ K := by
        have h8 := hY8 y' hy'Y
        have : 2 ^ n * (4 * r) < 2 ^ K * (4 * r) := by linarith
        exact lt_of_mul_lt_mul_right this h4r.le
      exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
    have hmem : y' ∈ Metric.closedBall y (2 ^ (n + 1) * (4 * r)) := by
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]; exact hn2.le
    have hterm : 1 / d ≤ 1 / (2 ^ n * (4 * r)) :=
      one_div_le_one_div_of_le (by positivity) hn1
    calc 1 / d ≤ 1 / (2 ^ n * (4 * r)) := hterm
      _ = (if y' ∈ Metric.closedBall y (2 ^ (n + 1) * (4 * r)) then
            1 / (2 ^ n * (4 * r)) else 0) := by rw [ite_eq_left_iff.mpr (fun h => absurd hmem h)]
      _ ≤ f y' := by
          apply Finset.single_le_sum (f := fun k => if y' ∈ Metric.closedBall y
            (2 ^ (k + 1) * (4 * r)) then 1 / (2 ^ k * (4 * r)) else 0) _ (Finset.mem_range.mpr hnK)
          intro k _; split_ifs <;> positivity
  calc ∑ y' ∈ Y.filter (fun z => 4 * r ≤ ‖y - z‖), 1 / ‖y - y'‖
      ≤ ∑ y' ∈ Y.filter (fun z => 4 * r ≤ ‖y - z‖), f y' := Finset.sum_le_sum hpt
    _ ≤ ∑ y' ∈ Y, f y' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hf0 i)
    _ = ∑ k ∈ range K, ∑ y' ∈ Y, (if y' ∈ Metric.closedBall y (2 ^ (k + 1) * (4 * r)) then
          1 / (2 ^ k * (4 * r)) else 0) := by rw [hfdef]; exact Finset.sum_comm
    _ = ∑ k ∈ range K, (1 / (2 ^ k * (4 * r))) *
          ((Y.filter (fun z => z ∈ Metric.closedBall y (2 ^ (k + 1) * (4 * r)))).card : ℝ) := by
        apply Finset.sum_congr rfl; intro k _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ range K, (1 / (2 ^ k * (4 * r))) * (C * (2 ^ (k + 1) * (4 * r)) * Y.card) := by
        apply Finset.sum_le_sum; intro k _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply hFr
        have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
        nlinarith
    _ = ∑ k ∈ range K, 2 * C * Y.card := by
        apply Finset.sum_congr rfl; intro k _
        field_simp; ring
    _ = 2 * C * K * Y.card := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The number of dyadic shells, in terms of `log (1 / r)`. -/
lemma exists_shell_count {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ K : ℕ, 8 < 2 ^ K * (4 * r) ∧ (K : ℝ) ≤ 2 + 3 / 2 * Real.log (1 / r) := by
  classical
  have hex : ∃ K : ℕ, 8 < 2 ^ K * (4 * r) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (8 / (4 * r)) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by rwa [div_lt_iff₀ (by positivity)] at hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  set K := Nat.find hex with hKdef
  have hK0 : K ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hKdef, h0] at this
    simp at this; linarith
  obtain ⟨m, hm⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  have hmin := Nat.find_min hex (show m < K by omega)
  have hle : (2 : ℝ) ^ m ≤ 2 / r := by
    rw [le_div_iff₀ hr]; replace hmin := not_lt.mp hmin; linarith
  have hlog : (m : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log (1 / r) := by
    have h1 := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at h1
    rw [show (2 : ℝ) / r = 2 * (1 / r) by ring, Real.log_mul (by norm_num) (by positivity)] at h1
    exact h1
  have hl2 := Real.log_two_gt_d9
  have hlr : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have hm' : (m : ℝ) ≤ 1 + 3 / 2 * Real.log (1 / r) := by
    by_contra hcon
    replace hcon := not_le.mp hcon
    have : (1 + 3 / 2 * Real.log (1 / r)) * Real.log 2 < (m : ℝ) * Real.log 2 :=
      mul_lt_mul_of_pos_right hcon (by linarith)
    nlinarith
  rw [hm]; push_cast; linarith

/-- The L² count of rich strips (finset form). -/
theorem rich_strip_count_finset {r C l : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C) (hl : 0 ≤ l)
    (Y : Finset E2) (hYne : Y.Nonempty) (hY4 : ∀ y ∈ Y, ‖y‖ ≤ 4)
    (hFr : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((Y.filter (fun z => z ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Y.card)
    (J : Finset (E2 × E2)) (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    (hrich : ∀ j ∈ J, l * Y.card ≤
      ((Y.filter (fun y => |inner ℝ (y - j.1) j.2| < r)).card : ℝ)) :
    l ^ 2 * J.card ≤ 16000 * C * (1 + Real.log (1 / r)) := by
  obtain ⟨K, hK, hKlog⟩ := exists_shell_count hr hr1
  set S : E2 × E2 → E2 → Prop := fun j y => |inner ℝ (y - j.1) j.2| < r with hSdef
  have hid := sum_sq_card_filter Y J S
  have hlow : (J.card : ℝ) * (l * Y.card) ^ 2 ≤ ∑ j ∈ J, ((Y.filter (S j)).card : ℝ) ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum; intro j hj
    have := hrich j hj
    have h0 : 0 ≤ l * Y.card := by positivity
    exact pow_le_pow_left₀ h0 this 2
  have hY8 : ∀ y ∈ Y, ∀ y' ∈ Y, ‖y - y'‖ ≤ 8 := fun y hy y' hy' =>
    norm_le_eight_of_norm_le_four (hY4 y hy) (hY4 y' hy')
  have hrow : ∀ y ∈ Y, ∑ y' ∈ Y, ((J.filter (fun j => S j y ∧ S j y')).card : ℝ) ≤
      (6336 + 3456 * K) * C * Y.card := by
    intro y hy
    rw [← Finset.sum_filter_add_sum_filter_not Y (fun z => 4 * r ≤ ‖y - z‖)]
    have hnear : ∑ y' ∈ Y.filter (fun z => ¬ 4 * r ≤ ‖y - z‖),
        ((J.filter (fun j => S j y ∧ S j y')).card : ℝ) ≤ 6336 * C * Y.card := by
      have hone := card_strips_through_point hr J hJ hsep (hY4 y hy)
      have h48 : (48 : ℝ) ≤ 48 / r := by rw [le_div_iff₀ hr]; nlinarith
      calc ∑ y' ∈ Y.filter (fun z => ¬ 4 * r ≤ ‖y - z‖),
            ((J.filter (fun j => S j y ∧ S j y')).card : ℝ)
          ≤ ∑ y' ∈ Y.filter (fun z => ¬ 4 * r ≤ ‖y - z‖), (1584 / r) := by
            apply Finset.sum_le_sum; intro y' _
            have hsub : J.filter (fun j => S j y ∧ S j y') ⊆
                J.filter (fun j => |inner ℝ (y - j.1) j.2| < r) :=
              Finset.monotone_filter_right _ (fun j _ h => h.1)
            have h1 := (Nat.cast_le (α := ℝ).mpr (Finset.card_mono hsub)).trans hone
            have : (1536 / r + 48 : ℝ) ≤ 1584 / r := by
              have : (1584 : ℝ) / r = 1536 / r + 48 / r := by ring
              linarith
            linarith
        _ = ((Y.filter (fun z => ¬ 4 * r ≤ ‖y - z‖)).card : ℝ) * (1584 / r) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (C * (4 * r) * Y.card) * (1584 / r) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hsub : Y.filter (fun z => ¬ 4 * r ≤ ‖y - z‖) ⊆
                Y.filter (fun z => z ∈ Metric.closedBall y (4 * r)) := by
              apply Finset.monotone_filter_right; intro z _ hz
              rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
              exact (not_le.mp hz).le
            exact (Nat.cast_le.mpr (Finset.card_mono hsub)).trans (hFr y (4 * r) (by linarith))
        _ = 6336 * C * Y.card := by field_simp; ring
    have hfar : ∑ y' ∈ Y.filter (fun z => 4 * r ≤ ‖y - z‖),
        ((J.filter (fun j => S j y ∧ S j y')).card : ℝ) ≤ 3456 * K * C * Y.card := by
      have hshell := shell_sum hr hC Y y (hY8 y hy) hFr K hK
      calc ∑ y' ∈ Y.filter (fun z => 4 * r ≤ ‖y - z‖),
            ((J.filter (fun j => S j y ∧ S j y')).card : ℝ)
          ≤ ∑ y' ∈ Y.filter (fun z => 4 * r ≤ ‖y - z‖), 1728 * (1 / ‖y - y'‖) := by
            apply Finset.sum_le_sum; intro y' hy'
            obtain ⟨hy'Y, hfar⟩ := Finset.mem_filter.mp hy'
            have htwo := card_strips_through_two_points hr J hJ hsep (hY4 y hy) hfar
            have hd8 := hY8 y hy y' hy'Y
            have hd0 : 0 < ‖y - y'‖ := by linarith
            have h24 : (24 : ℝ) ≤ 192 / ‖y - y'‖ := by rw [le_div_iff₀ hd0]; nlinarith
            calc ((J.filter (fun j => S j y ∧ S j y')).card : ℝ) ≤ 1536 / ‖y - y'‖ + 24 := htwo
              _ ≤ 1536 / ‖y - y'‖ + 192 / ‖y - y'‖ := by linarith
              _ = 1728 * (1 / ‖y - y'‖) := by ring
        _ = 1728 * ∑ y' ∈ Y.filter (fun z => 4 * r ≤ ‖y - z‖), 1 / ‖y - y'‖ := by
            rw [Finset.mul_sum]
        _ ≤ 1728 * (2 * C * K * Y.card) := by
            apply mul_le_mul_of_nonneg_left hshell (by norm_num)
        _ = 3456 * K * C * Y.card := by ring
    linarith
  have htot : ∑ y ∈ Y, ∑ y' ∈ Y, ((J.filter (fun j => S j y ∧ S j y')).card : ℝ) ≤
      Y.card * ((6336 + 3456 * K) * C * Y.card) := by
    calc _ ≤ ∑ y ∈ Y, (6336 + 3456 * K) * C * Y.card := Finset.sum_le_sum hrow
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hYne.card_pos
  have key : (J.card : ℝ) * (l * Y.card) ^ 2 ≤ Y.card * ((6336 + 3456 * K) * C * Y.card) :=
    hlow.trans (hid ▸ htot)
  have key2 : (J.card : ℝ) * l ^ 2 ≤ (6336 + 3456 * K) * C := by
    have h2 : ((J.card : ℝ) * l ^ 2) * (Y.card : ℝ) ^ 2 ≤ ((6336 + 3456 * K) * C) * (Y.card : ℝ) ^ 2 := by
      calc ((J.card : ℝ) * l ^ 2) * (Y.card : ℝ) ^ 2 = (J.card : ℝ) * (l * Y.card) ^ 2 := by ring
        _ ≤ Y.card * ((6336 + 3456 * K) * C * Y.card) := key
        _ = ((6336 + 3456 * K) * C) * (Y.card : ℝ) ^ 2 := by ring
    exact le_of_mul_le_mul_right h2 (by positivity)
  have hlr : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have hK3 : (6336 + 3456 * (K : ℝ)) * C ≤ (6336 + 3456 * (2 + 3 / 2 * Real.log (1 / r))) * C := by
    apply mul_le_mul_of_nonneg_right _ hC; linarith
  calc l ^ 2 * J.card = (J.card : ℝ) * l ^ 2 := by ring
    _ ≤ (6336 + 3456 * K) * C := key2
    _ ≤ (6336 + 3456 * (2 + 3 / 2 * Real.log (1 / r))) * C := hK3
    _ ≤ 16000 * C * (1 + Real.log (1 / r)) := by nlinarith

end WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap
