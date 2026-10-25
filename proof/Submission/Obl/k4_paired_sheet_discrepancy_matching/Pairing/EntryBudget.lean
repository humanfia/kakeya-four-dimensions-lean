/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/EntryBudget.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SampleLaws

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set

/-- World and time fibres cancel the original frame-density scale. -/
theorem weighted_entry_count_budget {m W q : ℕ} (hq : 0 < q)
    (world : Fin m → Fin W) (time : Fin m → Fin q) (ω : Fin W → ℝ)
    (hω : ∀ γ, 0 ≤ ω γ) (hωsum : ∑ γ, ω γ = 1)
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A)
    (hcount : ∀ γ j, ((Finset.univ.filter (fun i => world i = γ ∧ time i = j)).card : ℝ)
      ≤ A / σ) :
    (∑ i, ω (world i) * σ / (q : ℝ)) ≤ A := by
  classical
  let key : Fin m → Fin W × Fin q := fun i => (world i, time i)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ = ∑ k : Fin W × Fin q, ∑ i ∈ Finset.univ.filter (fun i => key i = k),
        ω (world i) * σ / (q : ℝ) :=
      (Finset.sum_fiberwise Finset.univ key _).symm
    _ ≤ ∑ k : Fin W × Fin q, A * ω k.1 / (q : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have hconst : (∑ i ∈ Finset.univ.filter (fun i => key i = k),
          ω (world i) * σ / (q : ℝ)) =
          ((Finset.univ.filter (fun i => key i = k)).card : ℝ) * (ω k.1 * σ / (q : ℝ)) := by
        calc _ = ∑ _i ∈ Finset.univ.filter (fun i => key i = k), ω k.1 * σ / (q : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [show world i = k.1 from congrArg Prod.fst (Finset.mem_filter.mp hi).2]
          _ = _ := by simp [nsmul_eq_mul]
      rw [hconst]
      have hc : ((Finset.univ.filter (fun i => key i = k)).card : ℝ) ≤ A / σ := by
        rcases k with ⟨γ, j⟩
        simpa only [key, Prod.mk.injEq] using hcount γ j
      calc _ ≤ (A / σ) * (ω k.1 * σ / (q : ℝ)) :=
            mul_le_mul_of_nonneg_right hc
              (div_nonneg (mul_nonneg (hω k.1) hσ.le) hqR.le)
        _ = A * ω k.1 / (q : ℝ) := by field_simp [hσ.ne', hqR.ne']
    _ = A := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have heq (γ : Fin W) : (q : ℝ) * (A * ω γ / (q : ℝ)) = A * ω γ := by
        field_simp [hqR.ne']
      simp_rw [heq]
      rw [← Finset.mul_sum, hωsum, mul_one]

namespace NormalizationStep.TestedSample

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

theorem sum_sourceCeiling_le (hω : ∀ γ, 0 ≤ ωk γ) (hωsum : ∑ γ, ωk γ = 1)
    (hNk : 0 < Nk) : (∑ i, s.sourceCeiling (s.frame i)) ≤ Nk ^ (2 * a) := by
  have hc := weighted_entry_count_budget (by positivity : 0 < 2 ^ s.T)
    (fun i => s.γ (s.frame i)) (fun i => s.j (s.frame i)) ωk hω hωsum
    s.σ_pos (Real.rpow_nonneg hNk.le a) s.hcount
  have heq : (∑ i, s.sourceCeiling (s.frame i)) =
      Nk ^ a * (∑ i, ωk (s.γ (s.frame i)) * s.σ / ((2 ^ s.T : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [sourceCeiling, frameWeight, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [heq]
  calc _ ≤ Nk ^ a * Nk ^ a :=
        mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hNk.le a)
    _ = Nk ^ (2 * a) := by rw [← Real.rpow_add hNk]; congr 1; ring

theorem beta_budget (hω : ∀ γ, 0 ≤ ωk γ) (hωsum : ∑ γ, ωk γ = 1)
    (hNk : 0 < Nk) :
    (∑ i, ωk (s.γ (s.frame i)) * s.β i / (2 : ℝ) ^ s.T) ≤ Nk ^ (2 * a) := by
  refine (Finset.sum_le_sum (fun i _ => ?_)).trans (s.sum_sourceCeiling_le hω hωsum hNk)
  change _ ≤ s.frameWeight (s.frame i) * (s.σ * Nk ^ a)
  have hβ := mul_le_mul_of_nonneg_left (s.hβ i).2.1
    (s.frameWeight_nonneg hω (s.frame i))
  convert hβ using 1 <;> dsimp [frameWeight] <;> ring

end NormalizationStep.TestedSample

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
