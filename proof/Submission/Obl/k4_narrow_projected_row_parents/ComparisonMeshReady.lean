import Submission.Obl.k4_narrow_projected_row_parents.CommonMeshPowers
import Submission.Obl.k4_narrow_projected_row_parents.VariablePaletteCaps

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Filter
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type} [MeasurableSpace α]

/-- Fixed physical resolution and exact original native caps for the actual
common widths. The major width need not itself be a prescribed power. -/
theorem eventually_comparison_mesh_ready (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcaps : a.Caps p) {s lo hi E T : ℝ}
    (hs : 0 ≤ s) (hlo : 0 < lo) (q χ m σ : ℕ → ℝ)
    (hχ : ∀ᶠ k in atTop, p.N k ^ (-hi) ≤ χ k ∧ χ k ≤ p.N k ^ (-lo))
    (hm : ∀ᶠ k in atTop, p.N k ^ (-E) ≤ m k ∧ m k ≤ q k)
    (hσ : ∀ᶠ k in atTop, p.N k ^ (-T) ≤ σ k) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop, ∃ v : ℝ,
      χ k = p.N k ^ (-v) ∧
      (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * q k * σ k ∧
      (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * χ k * σ k ∧
      (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * m k * σ k ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ s → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
        a.mu k {w | a.cell (p.N k) r k w = z ∧
          ⌊MvPolynomial.eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-t)⌋ = j ∧
          ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
          ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * t)) *
            a.pi k {w : ℝ | ⌊w / p.N k ^ (-v)⌋ = v₀} := by
  let P : ℝ := |E| + |hi|
  let r : ℝ := P + |T| + 1
  have hr : 0 < r := by dsimp [r, P]; positivity
  have hEP : E ≤ P := by dsimp [P]; linarith [le_abs_self E, abs_nonneg hi]
  have hhiP : hi ≤ P := by dsimp [P]; linarith [le_abs_self hi, abs_nonneg E]
  have hTr : T ≤ |T| := le_abs_self T
  have hresolve := eventually_common_mesh_resolution p hp P |T|
  have hnative := NativeCaps.eventually_joint_caps_variable_palette p hp a hcaps hr hs hlo χ hχ
  refine ⟨r, hr, ?_⟩
  filter_upwards [hχ, hm, hσ, hresolve, hnative] with k hχk hmk hσk hres hcap
  have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
  have hNgt : 1 < p.N k := by linarith [hp.1 k]
  have hσlower : p.N k ^ (-|T|) ≤ σ k :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hTr)).trans hσk
  have hmlower : p.N k ^ (-P) ≤ m k :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hEP)).trans hmk.1
  have hχlower : p.N k ^ (-P) ≤ χ k :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hhiP)).trans hχk.1
  obtain ⟨v, _, _, hv⟩ := exists_mesh_exponent hNgt hχk.1 hχk.2
  refine ⟨v, hv.symm, hres (q k) (σ k) (hmlower.trans hmk.2) hσlower,
    hres (χ k) (σ k) hχlower hσlower, hres (m k) (σ k) hmlower hσlower, ?_⟩
  intro t ht hts z j v₀
  simpa only [hv, ite_true] using hcap t ht hts true z j v₀

end Submission.Obl.k4_narrow_projected_row_parents
