import Submission.Obl.k4_two_velocity_row_list_completion.Completion
import Submission.Obl.k4_two_velocity_row_list_completion.Palette
import Submission.Obl.k4_two_velocity_row_list_completion.PairFiber
import Submission.Obl.k4_two_velocity_row_list_completion.ScalarDegree
import Submission.Obl.k4_two_velocity_row_list_completion.ScaleSelection

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace Submission.Obl.k4_two_velocity_row_list_completion

open Submission.Obl.k4_row_cell_regularization

/-- The continuous row-list completion at one scale. The position record is arbitrary;
the proof uses the original finite law and the original probability palette. -/
theorem continuous_completion {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (position : Ω → Fin 2 → ℤ)
    (velocity evaluation : Ω → ℝ) (row : Ω → Fin 2 → ℝ)
    (π : Measure ℝ) [IsProbabilityMeasure π]
    (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ)
    {ξ E K R S : ℝ} (hξ : 0 < ξ) (hξE : ξ ≤ E) (hE1 : E ≤ 1)
    (hK : 1 ≤ K) (hR : 2 ≤ R) (hKR : K + 2 ≤ R) (hmesh : ξ ≤ 1 / R)
    (hnear : K * (2 / R) ^ S ≤ (1 / K) / 2)
    (hvelocity : ∀ p, |velocity p| ≤ K)
    (hrow : ∀ᵐ p ∂μ, (∀ e, |row p e| ≤ K) ∧
      |row p 0 + velocity p * row p 1 - evaluation p| ≤ K * E)
    (hlistcard : ∀ q j, ((lists q j).card : ℝ) ≤ K)
    (hlists : ∀ᵐ p ∂μ, ⌊evaluation p / E⌋ ∈ lists (position p) ⌊velocity p / ξ⌋)
    (hpalette : ∀ x s : ℝ, ξ ≤ s → s ≤ 1 →
      π (Icc (x - s) (x + s)) ≤ ENNReal.ofReal (K * s ^ S))
    (hconditional : ∀ (q r : Fin 2 → ℤ) (j : ℤ),
      μ {p | position p = q ∧ (fun e => ⌊row p e / E⌋) = r ∧ ⌊velocity p / ξ⌋ = j} ≤
        ENNReal.ofReal K * π (Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ)) *
          μ {p | position p = q ∧ (fun e => ⌊row p e / E⌋) = r}) :
    ∃ bins : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ),
      (∀ q, ((bins q).card : ℝ) ≤ 16384 * R ^ 10) ∧
      ∀ᵐ p ∂μ, (fun e => ⌊row p e / E⌋) ∈ bins (position p) := by
  have hE : 0 < E := hξ.trans_le hξE
  have hK0 : 0 ≤ K := by linarith
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hξ1 : ξ ≤ 1 := hξE.trans hE1
  let rowCode (p : Ω) : Fin 2 → ℤ := fun e => ⌊row p e / E⌋
  let code (p : Ω) : ℤ := ⌊velocity p / ξ⌋
  let D : Finset ℤ := Finset.Icc (-⌈K / ξ⌉) ⌈K / ξ⌉
  let weight (j : ℤ) : ℝ := (π (Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ))).toReal
  let center (j : ℤ) : ℝ := (j : ℝ) * ξ
  let allowed : Finset (Fin 2 → ℤ) :=
    Fintype.piFinset (fun _ => Finset.Icc ⌊-K / E⌋ ⌊K / E⌋)
  let good (p : Ω) : Prop := (∀ e, |row p e| ≤ K) ∧
    |row p 0 + velocity p * row p 1 - evaluation p| ≤ K * E ∧
      ⌊evaluation p / E⌋ ∈ lists (position p) (code p)
  let C : ℝ := 3 * K + 3
  let B : ℝ := K ^ 2 * (12 * R ^ 2 * C + 2) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgood : ∀ᵐ p ∂μ, good p := by
    filter_upwards [hrow, hlists] with p hp hl
    exact ⟨hp.1, hp.2, hl⟩
  have hallowed : ∀ᵐ p ∂μ, rowCode p ∈ allowed := by
    filter_upwards [hrow] with p hp
    exact Fintype.mem_piFinset.mpr fun e =>
      Finset.mem_Icc.mpr (floor_mem_sym_range hE (hp.1 e))
  have hcenter (j : ℤ) (hj : j ∈ D) : |center j| ≤ R := by
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
    have hjlo' : -(⌈K / ξ⌉ : ℝ) ≤ j := by exact_mod_cast hjlo
    have hjhi' : (j : ℝ) ≤ ⌈K / ξ⌉ := by exact_mod_cast hjhi
    have hceil := Int.ceil_lt_add_one (K / ξ)
    have hmul := mul_lt_mul_of_pos_right hceil hξ
    have hfrac : K / ξ * ξ = K := div_mul_cancel₀ K hξ.ne'
    rw [add_mul, hfrac, one_mul] at hmul
    have habs : |(j : ℝ)| ≤ (⌈K / ξ⌉ : ℝ) := abs_le.mpr ⟨hjlo', hjhi'⟩
    calc
      |center j| = |(j : ℝ)| * ξ := by dsimp only [center]; rw [abs_mul, abs_of_pos hξ]
      _ ≤ (⌈K / ξ⌉ : ℝ) * ξ := mul_le_mul_of_nonneg_right habs hξ.le
      _ ≤ R := by linarith
  have hcompat (q r : Fin 2 → ℤ) (j : ℤ)
      (hc : Compatible position rowCode code good q r j) :
      ∃ L ∈ lists q j, |(r 0 : ℝ) + center j * (r 1 : ℝ) - (L : ℝ)| ≤ C := by
    obtain ⟨p, hp, hq, hr, hj⟩ := hc
    have he := rounded_evaluation hξ hξE hE1 (hvelocity p) hp.1 hp.2.1
    refine ⟨⌊evaluation p / E⌋, ?_, ?_⟩
    · simpa only [hq, hj] using hp.2.2
    · change |(rowCode p 0 : ℝ) + (code p : ℝ) * ξ * (rowCode p 1 : ℝ) -
        (⌊evaluation p / E⌋ : ℝ)| ≤ C at he
      simpa only [hr, hj, center, mul_assoc] using he
  have hpairs (q : Fin 2 → ℤ) (j : ℤ) (hj : j ∈ D)
      (k : ℤ) (hk : k ∈ D) (hsep : 1 / R ≤ |center k - center j|) :
      ((allowed.filter (fun r => Compatible position rowCode code good q r j ∧
        Compatible position rowCode code good q r k)).card : ℝ) ≤ B := by
    have hsub : allowed.filter (fun r => Compatible position rowCode code good q r j ∧
        Compatible position rowCode code good q r k) ⊆
        allowed.filter (fun r =>
          (∃ L ∈ lists q j, |(r 0 : ℝ) + center j * (r 1 : ℝ) - (L : ℝ)| ≤ C) ∧
          (∃ L ∈ lists q k, |(r 0 : ℝ) + center k * (r 1 : ℝ) - (L : ℝ)| ≤ C)) := by
      intro r hr
      obtain ⟨hr, h₁, h₂⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hr, hcompat q r j h₁, hcompat q r k h₂⟩
    calc
      _ ≤ _ := Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ (lists q j).card * ((lists q k).card : ℝ) * (12 * R ^ 2 * C + 2) ^ 2 :=
        pair_fiber_card allowed (lists q j) (lists q k) hR1 hC
          (hcenter j hj) (hcenter k hk) hsep
      _ ≤ B := mul_le_mul_of_nonneg_right
        (by simpa only [pow_two] using
          mul_le_mul (hlistcard q j) (hlistcard q k) (Nat.cast_nonneg _) hK0)
        (sq_nonneg _)
  have hnear' (j : ℤ) (hj : j ∈ D) :
      (∑ k ∈ D, if |center k - center j| < 1 / R then weight k else 0) ≤
        (1 / K) / 2 := by
    have h := palette_near_cap π D hξ hK0 hmesh
      (by simpa only [mul_one_div] using (div_le_one hR0).mpr hR) hpalette (center j)
    have hh : K * (2 * (1 / R)) ^ S ≤ (1 / K) / 2 := by
      simpa only [mul_one_div] using hnear
    exact h.trans hh
  obtain ⟨bins, hbins, haebins⟩ := complete_row_states μ position rowCode code good allowed
    D weight center (show 0 < K by linarith) (show 0 ≤ B by dsimp [B]; positivity)
    (fun _ _ => ENNReal.toReal_nonneg)
    (by simpa only [weight, binWeight, Measure.real] using sum_binWeight_le_one hξ π D)
    (fun p => velocity_code_mem hξ (hvelocity p)) hgood hallowed
    (fun q r j hj => by
      have hw : ENNReal.ofReal (weight j) =
          π (Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ)) :=
        ENNReal.ofReal_toReal (by finiteness)
      rw [hw]
      exact hconditional q r j) hnear' hpairs
  exact ⟨bins, fun q => (hbins q).trans (row_count_polynomial hK hR hKR), haebins⟩

end Submission.Obl.k4_two_velocity_row_list_completion
