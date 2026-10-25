import Submission.Obl.k4_row_cell_regularization.IncidencePoints

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace Submission.Obl.k4_two_velocity_row_list_completion

open Submission.Obl.k4_row_cell_regularization

/-- The accepted projection-rounding estimate, with the scalar evaluation also rounded. -/
theorem rounded_evaluation {ξ E K V H : ℝ} {T : Fin 2 → ℝ}
    (hξ : 0 < ξ) (hξE : ξ ≤ E) (hE1 : E ≤ 1)
    (hV : |V| ≤ K) (hT : ∀ e, |T e| ≤ K)
    (hfit : |T 0 + V * T 1 - H| ≤ K * E) :
    |(⌊T 0 / E⌋ : ℝ) + (⌊V / ξ⌋ : ℝ) * ξ * (⌊T 1 / E⌋ : ℝ) -
      (⌊H / E⌋ : ℝ)| ≤ 3 * K + 3 := by
  let F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ) := fun _ => {fun e => ⌊T e / E⌋}
  have hp : ((), (0 : ℝ)) ∈ goodSet ξ E K (fun _ : Unit => 0)
      (fun _ => V) (fun _ => H) (fun _ => T) F := by
    exact ⟨⟨le_rfl, zero_le_one⟩, hT, by simp [F], hfit⟩
  have he := traj_proj_snd hξ (hξE.trans hE1) hξE
    (b := fun _ : Unit => 0) (v := fun _ => V) (H := fun _ => H)
    (T := fun _ => T) (F := F) (fun _ => by simpa using hV) hp
  change |(⌊T 0 / E⌋ : ℝ) + (⌊V / ξ⌋ : ℝ) * ξ * (⌊T 1 / E⌋ : ℝ) - H / E| ≤
    3 * K + 2 at he
  have hf := real_floor_error (H / E)
  have ht := abs_add_le
    ((⌊T 0 / E⌋ : ℝ) + (⌊V / ξ⌋ : ℝ) * ξ * (⌊T 1 / E⌋ : ℝ) - H / E)
    (H / E - (⌊H / E⌋ : ℝ))
  have hid : (⌊T 0 / E⌋ : ℝ) + (⌊V / ξ⌋ : ℝ) * ξ * (⌊T 1 / E⌋ : ℝ) - H / E +
      (H / E - (⌊H / E⌋ : ℝ)) =
      (⌊T 0 / E⌋ : ℝ) + (⌊V / ξ⌋ : ℝ) * ξ * (⌊T 1 / E⌋ : ℝ) -
        (⌊H / E⌋ : ℝ) := by ring
  rw [hid] at ht
  linarith

/-- The bounded velocities lie in the symmetric finite range used for palette counting. -/
theorem velocity_code_mem {ξ K V : ℝ} (hξ : 0 < ξ) (hV : |V| ≤ K) :
    ⌊V / ξ⌋ ∈ Finset.Icc (-⌈K / ξ⌉) ⌈K / ξ⌉ := by
  have hvlo : -(K / ξ) ≤ V / ξ := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (abs_le.mp hV).1 hξ.le
  have hvhi : V / ξ ≤ K / ξ := div_le_div_of_nonneg_right (abs_le.mp hV).2 hξ.le
  apply Finset.mem_Icc.mpr
  constructor
  · simpa only [Int.floor_neg] using Int.floor_le_floor hvlo
  · exact (Int.floor_le_floor hvhi).trans (Int.floor_le_ceil _)

/-- Every positive row state is contained in the bounded integer box. -/
theorem positive_state_box {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (position : Ω → Q) (row : Ω → Fin 2 → ℝ)
    {E K : ℝ} (hE : 0 < E)
    (hrow : ∀ᵐ p ∂μ, ∀ e, |row p e| ≤ K) (q : Q) (r : Fin 2 → ℤ)
    (hmass : μ {p | position p = q ∧ (fun e => ⌊row p e / E⌋) = r} ≠ 0) :
    ∀ e, |(r e : ℝ)| ≤ K / E + 1 := by
  have hex : ∃ p, (∀ e, |row p e| ≤ K) ∧ position p = q ∧
      (fun e => ⌊row p e / E⌋) = r := by
    by_contra h
    apply hmass
    apply measure_mono_null (t := {p | ¬∀ e, |row p e| ≤ K}) _ (ae_iff.mp hrow)
    intro p hp hb
    exact h ⟨p, hb, hp⟩
  obtain ⟨p, hp, hpos, hr⟩ := hex
  intro e
  have hs : |row p e / E| ≤ K / E := by
    rw [abs_div, abs_of_pos hE]
    exact div_le_div_of_nonneg_right (hp e) hE.le
  have hlo := Int.floor_le (row p e / E)
  have hhi := Int.lt_floor_add_one (row p e / E)
  have he : (r e : ℝ) = (⌊row p e / E⌋ : ℝ) := by rw [← hr]
  rw [he, abs_le]
  obtain ⟨hslo, hshi⟩ := abs_le.mp hs
  constructor <;> linarith

end Submission.Obl.k4_two_velocity_row_list_completion
