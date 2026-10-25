/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/ScalarSupport.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit 771cc68c5af90206a38343b7b1bbe9d5343eaf47,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/ScalarSupport.lean`.
   Interval grid lemmas are imported from accepted o226. -/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Grid

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

noncomputable section

/-- A scalar time cell finer than a native block meets at most nine closed
native blocks. Endpoints are included. -/
theorem exists_contact_time_blocks {q σ : ℝ} (hq : 0 < q) (hσ : 0 ≤ σ)
    (hσq : σ ≤ q) (τ : ℝ) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ 9 ∧
      ∀ (n : ℤ) (t : ℝ), |t - τ| ≤ σ →
        (n : ℝ) * q ≤ t → t ≤ ((n : ℝ) + 1) * q → n ∈ J := by
  refine ⟨intervalBins q τ (q + σ), ?_, ?_⟩
  · calc
      _ ≤ 2 * (q + σ) / q + 5 := card_intervalBins hq (by positivity) τ
      _ ≤ 9 := by
        have hh : 2 * (q + σ) / q ≤ 4 := (div_le_iff₀ hq).mpr (by nlinarith)
        linarith
  · intro n t ht hlo hhi
    have hcell : |(n : ℝ) * q - t| ≤ q := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    have hnear : |(n : ℝ) * q - τ| ≤ q + σ :=
      (abs_sub_le _ _ _).trans (add_le_add hcell ht)
    have hmem := mem_intervalBins hq hnear
    simpa only [mul_div_cancel_right₀ _ hq.ne', Int.floor_intCast] using hmem

/-- A bounded scalar base has a finite mesh table with the expected area budget. -/
theorem exists_bounded_scalar_base_table {σ H : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hH : 0 ≤ H) :
    ∃ B : Finset (Fin 2 → ℤ), (B.card : ℝ) * σ ^ 2 ≤ (2 * H + 5) ^ 2 ∧
      ∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ H) → (fun i => ⌊x i / σ⌋) ∈ B := by
  let J := intervalBins σ 0 H
  let B : Finset (Fin 2 → ℤ) := Fintype.piFinset fun _ => J
  have hJ : (J.card : ℝ) * σ ≤ 2 * H + 5 := by
    calc
      _ ≤ (2 * H / σ + 5) * σ :=
        mul_le_mul_of_nonneg_right (card_intervalBins hσ hH 0) hσ.le
      _ = 2 * H + 5 * σ := by field_simp <;> ring
      _ ≤ _ := by linarith
  refine ⟨B, ?_, ?_⟩
  · have hp := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hσ.le) hJ 2
    have hB : (B.card : ℝ) = (J.card : ℝ) ^ 2 := by simp [B]
    rw [hB]
    convert hp using 1 <;> ring
  · intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact mem_intervalBins hσ (by simpa only [sub_zero] using hx i)

def scalarEntryBins {ι : Type*} (a L : ℝ) (S : Finset ι) (f : ι → ℝ) : Finset ℤ := by
  classical
  exact S.biUnion fun i => intervalBins a (f i) (L * a)

theorem mem_scalarEntryBins {ι : Type*} {a L y : ℝ} (ha : 0 < a)
    (S : Finset ι) (f : ι → ℝ) (hy : ∃ i ∈ S, |y - f i| ≤ L * a) :
    ⌊y / a⌋ ∈ scalarEntryBins a L S f := by
  classical
  obtain ⟨i, hi, hfit⟩ := hy
  exact Finset.mem_biUnion.mpr ⟨i, hi, mem_intervalBins ha hfit⟩

theorem card_scalarEntryBins {ι : Type*} {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (S : Finset ι) (f : ι → ℝ) :
    ((scalarEntryBins a L S f).card : ℝ) ≤ (S.card : ℝ) * (2 * L + 5) := by
  classical
  calc
    _ ≤ ∑ i ∈ S, ((intervalBins a (f i) (L * a)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ S, (2 * L + 5) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := card_intervalBins ha (mul_nonneg hL ha.le) (f i)
      convert hh using 1 <;> field_simp <;> ring
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The finite native lists in the scalar cells give the exact finite support
table required by Scalar. Their mass floors have already been paid on the
original law; this is only finite aggregation, with no additional pruning. -/
theorem exists_scalar_support_of_entry_lists {Ω Q ι : Type*}
    (B : Finset Q) (S : Q → Finset ι) (center : Q → ι → ℝ)
    (code : Ω → Q) (value : Ω → ℝ) (E : Set Ω) {a L M : ℝ}
    (ha : 0 < a) (hL : 0 ≤ L)
    (hcard : ∀ q ∈ B, ((S q).card : ℝ) ≤ M)
    (hcover : ∀ z ∈ E, code z ∈ B ∧ ∃ i ∈ S (code z), |value z - center (code z) i| ≤ L * a) :
    ∃ F : Finset (Q × ℤ), (F.card : ℝ) ≤ (B.card : ℝ) * M * (2 * L + 5) ∧
      ∀ z ∈ E, (code z, ⌊value z / a⌋) ∈ F := by
  classical
  let F := B.biUnion fun q => (scalarEntryBins a L (S q) (center q)).image (Prod.mk q)
  refine ⟨F, ?_, ?_⟩
  · calc
      _ ≤ ∑ q ∈ B, (((scalarEntryBins a L (S q) (center q)).image (Prod.mk q)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ B, M * (2 * L + 5) := by
        apply Finset.sum_le_sum
        intro q hq
        calc
          _ ≤ ((scalarEntryBins a L (S q) (center q)).card : ℝ) := by
            exact_mod_cast Finset.card_image_le
          _ ≤ ((S q).card : ℝ) * (2 * L + 5) := card_scalarEntryBins ha hL _ _
          _ ≤ M * (2 * L + 5) := mul_le_mul_of_nonneg_right (hcard q hq) (by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  · intro z hz
    obtain ⟨hcode, hfit⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨code z, hcode,
      Finset.mem_image.mpr ⟨_, mem_scalarEntryBins ha _ _ hfit, rfl⟩⟩

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
