/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file CoarseRows.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.NormalStrips

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- Choose one actual row in every occupied assigned coarse physical
cell. First common-choice comparison then controls its normal derivative
on every original active incidence, without discarding any label. -/
theorem exists_assigned_normal_rows
    (E : Set ScalarIncidence) (G : ScalarIncidence → Fin 2 → ℝ)
    {b ρ B K ζ H ε : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ z ∈ E, ∀ e, |G z e| ≤ B)
    (hcompare : ∀ z ∈ E, ∀ z' ∈ E,
      ‖G z - G z'‖ ≤ K * (‖scalarPosition z - scalarPosition z'‖ + ζ))
    (hvelocity : ∀ z ∈ E, |z.1.2 1| ≤ H)
    (hgraph : ∀ z ∈ E,
      |z.1.2 3 + 2 * z.2 * z.1.2 4 - G z 0 - G z 1 * z.1.2 1| ≤ ε) :
    ∃ row : (Fin 3 → ℤ) → Fin 2 → ℝ,
      (∀ q e, |row q e| ≤ B) ∧
      (∀ z ∈ E, ∀ e,
        |G z e - row (cell ρ (leftCorner b (cell b (scalarPosition z)))) e| ≤
          K * (ρ + 2 * b + ζ)) ∧
      ∀ z ∈ E,
        |(normalPolynomial
          (row (cell ρ (leftCorner b (cell b (scalarPosition z))))) z.1).derivative.eval z.2| ≤
          ε + K * (ρ + 2 * b + ζ) * (1 + H) := by
  classical
  let code (z : ScalarIncidence) := cell ρ (leftCorner b (cell b (scalarPosition z)))
  let row (q : Fin 3 → ℤ) : Fin 2 → ℝ :=
    if hq : ∃ z ∈ E, code z = q then G (Classical.choose hq) else 0
  have hrow (q : Fin 3 → ℤ) (e : Fin 2) : |row q e| ≤ B := by
    dsimp only [row]
    split_ifs with hq
    · exact hbound _ (Classical.choose_spec hq).1 e
    · simpa using hB
  have hclose (z : ScalarIncidence) (hz : z ∈ E) (e : Fin 2) :
      |G z e - row (code z) e| ≤ K * (ρ + 2 * b + ζ) := by
    have hq : ∃ z' ∈ E, code z' = code z := ⟨z, hz, rfl⟩
    let z' := Classical.choose hq
    have hz' : z' ∈ E := (Classical.choose_spec hq).1
    have hcode : code z' = code z := (Classical.choose_spec hq).2
    have hdist : ‖scalarPosition z - scalarPosition z'‖ ≤ ρ + 2 * b :=
      same_assigned_cell_distance hb hρ _ _ hcode.symm
    have hh := (norm_le_pi_norm (G z - G z') e).trans
      ((hcompare z hz z' hz').trans
        (mul_le_mul_of_nonneg_left (add_le_add hdist le_rfl) hK))
    simpa only [row, dite_eq_left hq, z', Real.norm_eq_abs, Pi.sub_apply] using hh
  refine ⟨row, hrow, hclose, ?_⟩
  intro z hz
  exact normal_derivative_bound (row (code z)) (G z) z.1 z.2
    (hvelocity z hz) (hgraph z hz) (hclose z hz)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
