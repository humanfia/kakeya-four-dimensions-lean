-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.StripSecondMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.RichStrip
import Submission.WZ.Obl.wz_multiscale_finite_tower.Dyadic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open scoped BigOperators
open WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

attribute [local instance] Classical.propDecidable

/-- Dyadic selection on squared integer weights upgrades a weak quadratic
bound to a second moment, with a logarithmic loss. -/
theorem second_moment_of_weak_quadratic {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (w : ι → ℕ) (K : ℕ) (B : ℝ)
    (hw : ∀ i ∈ J, (w i : ℝ) ≤ (2 : ℝ) ^ K)
    (hweak : ∀ a : ℝ, 0 < a → ∀ S : Finset ι, S ⊆ J →
      (∀ i ∈ S, a ≤ w i) → a ^ 2 * S.card ≤ B) :
    ∑ i ∈ J, (w i : ℝ) ^ 2 ≤ 2 * (2 * K + 1) * B := by
  classical
  have hB : 0 ≤ B := by
    simpa using hweak 1 (by norm_num) ∅ (Finset.empty_subset _) (by simp)
  let J' := J.filter fun i => 0 < w i
  have hsum : (∑ i : J', (w i : ℝ) ^ 2) = ∑ i ∈ J, (w i : ℝ) ^ 2 := by
    rw [Finset.sum_coe_sort J' (fun i => (w i : ℝ) ^ 2)]
    dsimp only [J']
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · simp only [Nat.not_lt, Nat.le_zero] at h
      simp [h]
  have hnonneg : 0 ≤ ∑ i ∈ J, (w i : ℝ) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (w i : ℝ)
  by_cases hzero : (∑ i ∈ J, (w i : ℝ) ^ 2) = 0
  · rw [hzero]
    positivity
  have hmass : 0 < ∑ i : J', (w i : ℝ) ^ 2 := by
    rw [hsum]
    exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
  obtain ⟨k, hk, S, hSne, hmassS, hS⟩ :=
    WangZahlLot.Obl.wz_multiscale_finite_tower.dyadic_weights
      (K := 2 * K) (fun i : J' => (w i : ℝ) ^ 2) (a := 1) (by norm_num)
      (fun i => by
        have hi : (1 : ℝ) ≤ w i := by
          exact_mod_cast (Finset.mem_filter.mp i.property).2
        nlinarith)
      (fun i => by
        have hh := pow_le_pow_left₀ (Nat.cast_nonneg (w i))
          (hw i (Finset.mem_filter.mp i.property).1) 2
        simpa only [mul_one, pow_mul, Nat.mul_comm 2 K] using hh) hmass
  let T : Finset ι := S.image Subtype.val
  have hTJ : T ⊆ J := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp j.property).1
  have hcard : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hroot : (Real.sqrt ((2 : ℝ) ^ k)) ^ 2 = (2 : ℝ) ^ k :=
    Real.sq_sqrt (by positivity)
  have hlower : ∀ i ∈ T, Real.sqrt ((2 : ℝ) ^ k) ≤ w i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hh := (hS j hj).1
    have hj0 : (0 : ℝ) ≤ w j := Nat.cast_nonneg _
    nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ k)]
  have hweakT := hweak (Real.sqrt ((2 : ℝ) ^ k))
    (Real.sqrt_pos.mpr (by positivity)) T hTJ hlower
  rw [hroot] at hweakT
  have hupper : (∑ i ∈ S, (w i : ℝ) ^ 2) ≤ 2 * B := by
    calc
      (∑ i ∈ S, (w i : ℝ) ^ 2) ≤ ∑ _i ∈ S, (2 : ℝ) ^ (k + 1) :=
        Finset.sum_le_sum fun i hi => by simpa only [mul_one] using (hS i hi).2.le
      _ = 2 * ((2 : ℝ) ^ k * T.card) := by simp [hcard, pow_succ]; ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hweakT (by norm_num)
  rw [hsum] at hmassS
  have hden : (0 : ℝ) < (2 * K : ℕ) + 1 := by positivity
  have hh := (div_le_iff₀ hden).mp (hmassS.trans hupper)
  push_cast at hh
  nlinarith only [hh]

-- The weak bound below adapts the workspace proof in o157/x0572,
-- Multiscale/ColoredStripIncidence.lean.  The accepted rich-strip theorem
-- itself is imported above.
/-- The number of cells met by separated strips has a controlled second
moment. A bounded coloring accommodates quantized coarse tube parameters. -/
theorem colored_strip_second_moment {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (Y : Finset E2) (hY : Y.Nonempty) (J : Finset ι) (rep : ι → E2 × E2) (col : ι → κ)
    {r C : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hY4 : ∀ y ∈ Y, ‖y‖ ≤ 4)
    (hFr : ∀ x ρ, r ≤ ρ →
      ((Y.filter (fun y => y ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Y.card)
    (hrep : ∀ i ∈ J, ‖(rep i).1‖ ≤ 4 ∧ ‖(rep i).2‖ = 1)
    (hinj : Set.InjOn rep (↑J : Set ι))
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → col i = col j → StripSep r (rep i) (rep j))
    (K : ℕ) (hK : (Y.card : ℝ) ≤ (2 : ℝ) ^ K)
    (w : ι → ℕ)
    (hw : ∀ i ∈ J, w i ≤ (Y.filter (fun y => |inner ℝ (y - (rep i).1) (rep i).2| < r)).card) :
    ∑ i ∈ J, (w i : ℝ) ^ 2 ≤
      32000 * Fintype.card κ * C * (1 + Real.log (1 / r)) * (2 * K + 1) *
        (Y.card : ℝ) ^ 2 := by
  classical
  have hYp : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  let B := 16000 * C * (1 + Real.log (1 / r)) * (Y.card : ℝ) ^ 2
  have hweak : ∀ a : ℝ, 0 < a → ∀ S : Finset ι, S ⊆ J →
      (∀ i ∈ S, a ≤ w i) → a ^ 2 * S.card ≤ (Fintype.card κ : ℝ) * B := by
    intro a ha S hSJ hsize
    let T (k : κ) := S.filter (fun i => col i = k)
    have hTJ (k : κ) : T k ⊆ J := (Finset.filter_subset _ _).trans hSJ
    have hcolor (k : κ) : a ^ 2 * (T k).card ≤ B := by
      have hi : Set.InjOn rep (↑(T k) : Set ι) := hinj.mono (hTJ k)
      have hs : ((T k).image rep : Set (E2 × E2)).Pairwise (StripSep r) := by
        intro x hx y hy hxy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        apply hsep i (hTJ k hi) j (hTJ k hj) (fun he => hxy (congrArg rep he))
        exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
      have hc := rich_strip_count_finset hr hr1 hC (div_nonneg ha.le hYp.le)
        Y hY hY4 hFr ((T k).image rep)
        (by intro x hx; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx; exact hrep i (hTJ k hi))
        hs (by
          intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          have hh : a ≤ ((Y.filter (fun y => |inner ℝ (y - (rep i).1) (rep i).2| < r)).card : ℝ) :=
            (hsize i (Finset.mem_filter.mp hi).1).trans (Nat.cast_le.mpr (hw i (hTJ k hi)))
          simpa only [div_mul_cancel₀ _ hYp.ne'] using hh)
      rw [Finset.card_image_of_injOn hi] at hc
      have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (Y.card : ℝ))
      have heq : (a / (Y.card : ℝ)) ^ 2 * ((T k).card : ℝ) * (Y.card : ℝ) ^ 2 =
          a ^ 2 * (T k).card := by field_simp
      rwa [heq] at hm
    have heq : (∑ k : κ, ((T k).card : ℝ)) = S.card := by
      have hh := Finset.sum_card_fiberwise_eq_card_filter S (Finset.univ : Finset κ) col
      simpa only [T, Finset.mem_univ, Finset.filter_true] using (show
        (∑ k : κ, ((S.filter (fun i => col i = k)).card : ℝ)) =
          ((S.filter (fun i => col i ∈ (Finset.univ : Finset κ))).card : ℝ) by exact_mod_cast hh)
    calc
      a ^ 2 * (S.card : ℝ) = ∑ k : κ, a ^ 2 * (T k).card := by rw [← heq, Finset.mul_sum]
      _ ≤ ∑ _k : κ, B := Finset.sum_le_sum fun k _ => hcolor k
      _ = _ := by simp
  have hmain := second_moment_of_weak_quadratic J w K ((Fintype.card κ : ℝ) * B)
    (fun i hi => (Nat.cast_le.mpr ((hw i hi).trans (Finset.card_filter_le _ _))).trans hK) hweak
  convert hmain using 1 <;> dsimp [B] <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
