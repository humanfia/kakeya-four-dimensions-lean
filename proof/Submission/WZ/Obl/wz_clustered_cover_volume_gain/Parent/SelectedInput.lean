-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SelectedInput.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SelectedFamily

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SelectedFamily

open MeasureTheory Set Finset Interfaces

/-- Retained mass supplies density measured against the original fine count. -/
theorem retained_density {δ η τ m l : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} (P : Finset (Fin n))
    (hδ : 0 < δ) (hA : A δ η m l n x v Y)
    (hkeep : o (δ ^ τ) * ∑ i, μ (Y i) ≤ ∑ i ∈ P, μ (Z i)) :
    o (δ ^ (τ + η) * n * δ ^ 2) ≤ ∑ i ∈ P, μ (Z i) := by
  calc
    _ = o (δ ^ τ) * o (δ ^ η * n * δ ^ 2) := by
      rw [o, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.rpow_add hδ]
      congr 1
      ring
    _ ≤ o (δ ^ τ) * ∑ i, μ (Y i) := mul_le_mul_right hA.2.2.2.1 _
    _ ≤ _ := hkeep

/-- A retained subshading contains a quantitatively large number of fine tubes. -/
theorem retained_fine_card {δ η τ m l : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} (P : Finset (Fin n))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : A δ η m l n x v Y)
    (hZ : ∀ i ∈ P, Z i ⊆ Y i)
    (hkeep : o (δ ^ τ) * ∑ i, μ (Y i) ≤ ∑ i ∈ P, μ (Z i)) :
    δ ^ (τ + η) * n ≤ 384 * P.card := by
  have hdense := retained_density P hδ hA hkeep
  have hupper : (∑ i ∈ P, μ (Z i)) ≤ o (384 * P.card * δ ^ 2) := by
    calc
      _ ≤ ∑ _i ∈ P, o (384 * δ ^ 2) := Finset.sum_le_sum fun i hi =>
        (measure_mono ((hZ i hi).trans (hA.2.1 i).2.2.2)).trans
          (tube_volume_upper hδ hδ1 (x i) (v i) (hA.2.1 i).1)
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, o, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hdense.trans hupper)
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp hreal

/-- The complete selected family satisfies the normalized admissibility and
full-cover hypotheses used by the flat-box estimate. All losses are explicit
in one Frostman error budget. -/
theorem normalized_selected_input {δ η h τ η' ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} (Q : Finset (Fin N))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hηh : η ≤ h)
    (hη' : 0 ≤ η') (hden : τ + η ≤ η') (hh' : h ≤ η')
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (hkeep : o (δ ^ τ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S with f i ∈ Q, μ (Z i))
    (hbudget : 384 * δ ^ (-(τ + η + 2 * h)) ≤ δ ^ (-η')) :
    A δ η' (δ ^ (-η')) (δ ^ (-η')) (fine S f Q).card
        (x ∘ index (fine S f Q)) (v ∘ index (fine S f Q)) (Z ∘ index (fine S f Q)) ∧
      C δ η' (fine S f Q).card (x ∘ index (fine S f Q)) (v ∘ index (fine S f Q))
        (Z ∘ index (fine S f Q)) Finset.univ (Z ∘ index (fine S f Q))
        ρ Q.card (y ∘ index Q) (w ∘ index Q) (assign S f Q) := by
  classical
  let P := fine S f Q
  have hZ : ∀ i ∈ P, MeasurableSet (Z i) ∧ Z i ⊆ Y i := fun i _ =>
    ⟨(hC.1 i).1, (hC.1 i).2.1⟩
  have hcount := retained_fine_card P hδ hδ1 hA (fun i hi => (hZ i hi).2) hkeep
  have hP : P.Nonempty := by
    apply Finset.card_pos.mp
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
    have hpos : 0 < δ ^ (τ + η) * n := by positivity
    by_contra hp
    have hz : P.card = 0 := Nat.eq_zero_of_not_pos hp
    rw [hz, Nat.cast_zero, mul_zero] at hcount
    exact (hpos.trans_le hcount).false
  have hcoarse := retained_cover_card_bound hδ hδ1 hA hC Q hkeep
  have hratioC : δ ^ (-h) * N ≤ δ ^ (-η') * Q.card := by
    calc
      _ = δ ^ (-(τ + η + 2 * h)) * (δ ^ (τ + η + h) * N) := by
        rw [← mul_assoc, ← Real.rpow_add hδ,
          show -(τ + η + 2 * h) + (τ + η + h) = -h by ring]
      _ ≤ δ ^ (-(τ + η + 2 * h)) * (384 * Q.card) :=
        mul_le_mul_of_nonneg_left hcoarse (Real.rpow_nonneg hδ.le _)
      _ = (384 * δ ^ (-(τ + η + 2 * h))) * Q.card := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)
  have hbudgetA : 384 * δ ^ (-(τ + 2 * η)) ≤ δ ^ (-η') := by
    apply le_trans _ hbudget
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 384)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hratioA : δ ^ (-η) * n ≤ δ ^ (-η') * P.card := by
    calc
      _ = δ ^ (-(τ + 2 * η)) * (δ ^ (τ + η) * n) := by
        rw [← mul_assoc, ← Real.rpow_add hδ, show -(τ + 2 * η) + (τ + η) = -η by ring]
      _ ≤ δ ^ (-(τ + 2 * η)) * (384 * P.card) :=
        mul_le_mul_of_nonneg_left hcount (Real.rpow_nonneg hδ.le _)
      _ = (384 * δ ^ (-(τ + 2 * η))) * P.card := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudgetA (Nat.cast_nonneg _)
  have hPdense : o (δ ^ η' * P.card * δ ^ 2) ≤ ∑ i ∈ P, μ (Z i) := by
    apply le_trans _ (retained_density P hδ hA hkeep)
    apply ENNReal.ofReal_le_ofReal
    have hp : (P.card : ℝ) ≤ n := Nat.cast_le.mpr (by simpa using P.card_le_univ)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hden) hp
        (Nat.cast_nonneg _) (Real.rpow_nonneg hδ.le _)) (sq_nonneg δ)
  have hselected := admissible_subshading P hA hP hZ hPdense hratioA
  constructor
  · refine ⟨hselected.1, hselected.2.1, hselected.2.2.1, hselected.2.2.2.1,
      ?_, hselected.2.2.2.2.2⟩
    intro W hW
    apply (hselected.2.2.2.2.1 W hW).trans
    gcongr
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg (hηh.trans hh'))
  · exact cover_complete_fibers Q hδ hδ1 hη' hh' hC hratioC

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SelectedFamily
