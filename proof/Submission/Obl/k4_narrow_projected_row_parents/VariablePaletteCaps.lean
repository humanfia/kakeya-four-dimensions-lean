import Submission.Obl.k4_narrow_projected_row_parents.ModelBridge
import Submission.Obl.k4_narrow_projected_row_parents.MeshExponent

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set Filter
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type} [MeasurableSpace α]

/-- Uniform original caps read an arbitrary palette width in a fixed power band
exactly, including aligned widths that are not a fixed power of `N`. -/
theorem eventually_joint_caps_variable_palette (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcap : a.Caps p) {r S lo hi : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hlo : 0 < lo) (χ : ℕ → ℝ)
    (hχ : ∀ᶠ k in atTop, p.N k ^ (-hi) ≤ χ k ∧ χ k ≤ p.N k ^ (-lo)) :
    ∀ᶠ k in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ S → ∀ h : Bool,
      ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = z ∧
        ⌊(if h then MvPolynomial.eval (a.x k w.1 w.2) (a.P k) else (a.x k w.1 w.2) 3) /
          p.N k ^ (-s)⌋ = j ∧ ⌊a.b k w.1 3 / χ k⌋ = v₀} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
          a.pi k {w : ℝ | ⌊w / χ k⌋ = v₀} := by
  let R : ℝ := 2 + r + r⁻¹ + lo + lo⁻¹ + |hi| + S
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hli : 0 < lo⁻¹ := inv_pos.mpr hlo
  have hR : 1 < R := by dsimp [R]; linarith [abs_nonneg hi]
  have hrR : r ≤ R := by dsimp [R]; linarith [abs_nonneg hi]
  have hSR : S ≤ R := by dsimp [R]; linarith [abs_nonneg hi]
  have hhiR : hi ≤ R := by dsimp [R]; linarith [le_abs_self hi]
  have hRr : R⁻¹ ≤ r := by
    have h : r⁻¹ ≤ R := by dsimp [R]; linarith [abs_nonneg hi]
    simpa only [inv_inv] using inv_anti₀ hri h
  have hRlo : R⁻¹ ≤ lo := by
    have h : lo⁻¹ ≤ R := by dsimp [R]; linarith [abs_nonneg hi]
    simpa only [inv_inv] using inv_anti₀ hli h
  filter_upwards [hcap R hR, hχ] with k hk hχk
  obtain ⟨v, hvlo, hvhi, hv⟩ := exists_mesh_exponent
    (show 1 < p.N k by linarith [hp.1 k]) hχk.1 hχk.2
  intro s hs hsS h z j v₀
  have h := (hk r s v hRr hrR hs (hsS.trans hSR) (hRlo.trans hvlo) (hvhi.trans hhiR)).2.2 h z j v₀
  simpa only [hv] using h

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
