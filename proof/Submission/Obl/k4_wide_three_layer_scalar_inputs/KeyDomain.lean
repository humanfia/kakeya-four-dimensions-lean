import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.LabelGraph

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set
open Inherited.Native

/-- Every actual horizontal incidence in the slot lies in the whole key
rectangle. The small drift is absorbed by its unused transverse margin. -/
theorem actual_point_in_key_domain {α : Type} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} {χ m q t₀ ζ t : ℝ} {key : Fin 3 → ℤ} {l : α}
    (hχ : 0 < χ) (hm : 0 < m) (hq : 0 < q)
    (hkey : slotKey b χ m t₀ l = key) (hhor : |b l 4 + b l 0| ≤ ζ)
    (hsmall : q * (ζ + χ) ≤ m / 2) (ht : t ∈ Icc t₀ (t₀ + q)) :
    ∃ τ ∈ Icc (0 : ℝ) 1, ∃ y ∈ Icc (-1 : ℝ) 1,
      t = t₀ + q * τ ∧ b l 1 + t * b l 4 = domY χ m q key τ y := by
  let τ := (t - t₀) / q
  have hτ : τ ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [ht.1]) hq.le,
      (div_le_one hq).mpr (by linarith [ht.2])⟩
  have heqt : t₀ + q * τ = t := by dsimp [τ]; field_simp; ring
  have hnear := key_Y_near hχ hm.ne' hq.le hkey hhor hτ
  rw [heqt] at hnear
  let d := (b l 1 + t * b l 4 - domY χ m q key τ (sliceY b m t₀ l)) / (2 * m)
  have hd : |d| ≤ 1 / 4 := by
    dsimp [d]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * m), div_le_iff₀ (by positivity : 0 < 2 * m)]
    linarith
  have hs := sliceY_mem b m t₀ l
  refine ⟨τ, hτ, sliceY b m t₀ l + d, ?_, heqt.symm, ?_⟩
  · rw [abs_le] at hd
    constructor <;> linarith [hs.1, hs.2, hd.1, hd.2]
  · dsimp [d]
    unfold domY
    field_simp
    ring

end Submission.Obl.k4_wide_three_layer_scalar_inputs
