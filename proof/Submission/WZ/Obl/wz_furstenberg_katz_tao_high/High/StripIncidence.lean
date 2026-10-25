-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.StripIncidence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/StripIncidence.lean (c61cafd).
-- Adapted from local obligation o157, branch x0675, commit 5a2c82ba2c9f.
-- Source: Multiscale/StripIncidence.lean. Shared half definitions imported from accepted o213.
-- Ported from internal o141/x0563, commit 58c4a1f; namespace renamed.
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.RichStrip
import Submission.WZ.Obl.wz_multiscale_finite_tower.Dyadic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

attribute [local instance] Classical.propDecidable

/-- Dyadic selection converts a weak quadratic bound on rich subfamilies into an
incidence bound. The weights may vanish. -/
theorem weak_quadratic_sum {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (w : ι → ℕ) (K : ℕ) (B : ℝ)
    (hw : ∀ i ∈ J, (w i : ℝ) ≤ (2 : ℝ) ^ K)
    (hweak : ∀ a : ℝ, 0 < a → ∀ S : Finset ι, S ⊆ J →
      (∀ i ∈ S, a ≤ w i) → a ^ 2 * S.card ≤ B) :
    (∑ i ∈ J, (w i : ℝ)) ^ 2 ≤ 4 * B * (K + 1) ^ 2 * J.card := by
  classical
  have hB : 0 ≤ B := by
    simpa using hweak 1 (by norm_num) ∅ (Finset.empty_subset _) (by simp)
  let J' := J.filter fun i => 0 < w i
  have hsum : (∑ i : J', (w i : ℝ)) = ∑ i ∈ J, (w i : ℝ) := by
    rw [Finset.sum_coe_sort J' (fun i => (w i : ℝ))]
    dsimp only [J']
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · simp only [Nat.not_lt, Nat.le_zero] at h
      simp [h]
  have hnonneg : 0 ≤ ∑ i ∈ J, (w i : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  by_cases hzero : (∑ i ∈ J, (w i : ℝ)) = 0
  · rw [hzero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hmass : 0 < ∑ i : J', (w i : ℝ) := by
    rw [hsum]
    exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
  obtain ⟨k, hk, S, hSne, hmassS, hS⟩ :=
    WangZahlLot.Obl.wz_multiscale_finite_tower.dyadic_weights
      (K := K) (fun i : J' => (w i : ℝ)) (a := 1) (by norm_num)
      (fun i => by exact_mod_cast (Finset.mem_filter.mp i.property).2)
      (fun i => by simpa using hw i (Finset.mem_filter.mp i.property).1) hmass
  let T : Finset ι := S.image Subtype.val
  have hTJ : T ⊆ J := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp j.property).1
  have hcard : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hcardJ : (T.card : ℝ) ≤ J.card := Nat.cast_le.mpr (Finset.card_le_card hTJ)
  have hlower : ∀ i ∈ T, (2 : ℝ) ^ k ≤ w i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simpa using (hS j hj).1
  have hupper : (∑ i ∈ S, (w i : ℝ)) ≤ 2 * (2 : ℝ) ^ k * T.card := by
    calc
      (∑ i ∈ S, (w i : ℝ)) ≤ ∑ _i ∈ S, (2 : ℝ) ^ (k + 1) :=
        Finset.sum_le_sum fun i hi => by simpa using (hS i hi).2.le
      _ = 2 * (2 : ℝ) ^ k * T.card := by simp [hcard, pow_succ]; ring
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hmassT : (∑ i ∈ J, (w i : ℝ)) ≤ 2 * (K + 1) * (2 : ℝ) ^ k * T.card := by
    rw [hsum] at hmassS
    have := (div_le_iff₀ hK).mp (hmassS.trans hupper)
    nlinarith
  have hweakT := hweak ((2 : ℝ) ^ k) (by positivity) T hTJ hlower
  have hprod : ((2 : ℝ) ^ k) ^ 2 * (T.card : ℝ) ^ 2 ≤ B * J.card := by
    calc
      ((2 : ℝ) ^ k) ^ 2 * (T.card : ℝ) ^ 2 =
          (((2 : ℝ) ^ k) ^ 2 * T.card) * T.card := by ring
      _ ≤ B * T.card := mul_le_mul_of_nonneg_right hweakT (Nat.cast_nonneg _)
      _ ≤ B * J.card := mul_le_mul_of_nonneg_left hcardJ hB
  calc
    (∑ i ∈ J, (w i : ℝ)) ^ 2 ≤
        (2 * (K + 1) * (2 : ℝ) ^ k * T.card) ^ 2 :=
      pow_le_pow_left₀ hnonneg hmassT 2
    _ = 4 * (K + 1) ^ 2 * (((2 : ℝ) ^ k) ^ 2 * (T.card : ℝ) ^ 2) := by ring
    _ ≤ 4 * (K + 1) ^ 2 * (B * J.card) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 4 * B * (K + 1) ^ 2 * J.card := by ring

/-- The coarse-scale quadratic incidence bound uses only point nonconcentration
and separation of the strip labels. -/
theorem strip_incidence_bound {r C m : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C) (hm : 0 ≤ m) (Y : Finset E2) (hYne : Y.Nonempty)
    (hY4 : ∀ y ∈ Y, ‖y‖ ≤ 4)
    (hFr : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((Y.filter (fun z => z ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Y.card)
    (J : Finset (E2 × E2)) (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    (K : ℕ) (hK : (Y.card : ℝ) ≤ (2 : ℝ) ^ K)
    (hinc : m * Y.card ≤ ∑ j ∈ J,
      ((Y.filter (fun y => |inner ℝ (y - j.1) j.2| < r)).card : ℝ)) :
    m ^ 2 ≤ 64000 * C * (1 + Real.log (1 / r)) * (K + 1) ^ 2 * J.card := by
  classical
  have hY : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hYne.card_pos
  let w : E2 × E2 → ℕ := fun j =>
    (Y.filter (fun y => |inner ℝ (y - j.1) j.2| < r)).card
  have hbound := weak_quadratic_sum J w K
    (16000 * C * (1 + Real.log (1 / r)) * (Y.card : ℝ) ^ 2)
    (fun j hj => (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hK)
    (by
      intro a ha S hSJ hrich
      have hcount := rich_strip_count_finset hr hr1 hC (div_nonneg ha.le hY.le)
        Y hYne hY4 hFr S (fun j hj => hJ j (hSJ hj))
        (hsep.mono hSJ)
        (fun j hj => by simpa [div_mul_cancel₀ _ hY.ne', w] using hrich j hj)
      have hmul := mul_le_mul_of_nonneg_right hcount (sq_nonneg (Y.card : ℝ))
      have hid : (a / (Y.card : ℝ)) ^ 2 * (S.card : ℝ) * (Y.card : ℝ) ^ 2 =
          a ^ 2 * S.card := by field_simp
      rwa [hid] at hmul)
  have hsq := (pow_le_pow_left₀ (mul_nonneg hm hY.le) hinc 2).trans hbound
  have hfinal : m ^ 2 * (Y.card : ℝ) ^ 2 ≤
      (64000 * C * (1 + Real.log (1 / r)) * (K + 1) ^ 2 * J.card) *
        (Y.card : ℝ) ^ 2 := by
    convert hsq using 1 <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hY)).mp hfinal

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
