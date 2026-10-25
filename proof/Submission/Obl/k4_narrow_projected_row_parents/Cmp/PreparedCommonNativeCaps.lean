/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedCommonNativeCaps.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonNativeCaps
import Submission.Obl.k4_general_parent_projected_layers.Model
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedBaseCaps

/-! Actual prepared-model caps in the literal common comparison frame. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Lib.K4MovingMeshBoxes
open scoped ENNReal

noncomputable section

/-- The literal true branch of the frozen palette-joint mesh caps supplies the
common-frame native caps. Its only cap input is the frozen field specialized to
the selected physical mesh and velocity exponents. -/
theorem prepared_common_native_caps {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {k : ℕ} {r v S q g m σ : ℝ} (hS : 0 ≤ S) (hq : 0 < q) (hm : 0 < m) (hσ : 0 < σ)
    (c : Code)
    (hresolve : ∀ i, (∑ j, |coordMatrix q (p.N k ^ (-v)) g m c i j| * p.N k ^ (-r)) ≤ σ)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ S → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = z ∧
        ⌊MvPolynomial.eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-s)⌋ = j ∧
        ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        a.pi k {w : ℝ | ⌊w / p.N k ^ (-v)⌋ = v₀})
    {R : ℝ} (hR : p.N k ^ (-S) ≤ R) (z : Fin 3 → ℤ) (j : ℤ) :
    a.mu k {w | Submission.Lib.K4MovingMeshBoxes.baseMesh σ
        (coords q (p.N k ^ (-v)) g m c (point (a.b k w.1) w.2)) = z ∧
      ⌊MvPolynomial.eval (a.x k w.1 w.2) (a.P k) / R⌋ = j ∧
      ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = c 1} ≤
    ENNReal.ofReal (27000000 * p.K k * (2 * p.K k + 5) * q * (p.N k ^ (-v)) * m * R ^ p.d * σ ^ 3) *
      a.pi k {w : ℝ | ⌊w / p.N k ^ (-v)⌋ = c 1} := by
  have hN : 1 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hN0 : 0 < p.N k := zero_lt_one.trans hN
  have hK : 0 ≤ p.K k := (zero_le_one : (0 : ℝ) ≤ 1).trans (hp.2.2.1.1 k)
  haveI : IsProbabilityMeasure (a.pi k) := (hcommon k).2.2.1
  apply common_frame_native_caps (a.mu k) (fun w => point (a.b k w.1) w.2)
    (fun w => MvPolynomial.eval (a.x k w.1 w.2) (a.P k)) (fun w => a.b k w.1 3)
    (a.pi k) hN hS hp.2.2.2.1 hK hK hq (Real.rpow_pos_of_pos hN0 _) hm
    (Real.rpow_pos_of_pos hN0 _) hσ c hresolve (a.ae_native_signal_bound p hcommon k)
    (fun s hs hsS z' j' v₀ => ?_) hR z j
  have h := hcap s hs hsS z' j' v₀
  convert h using 1
  · rfl
  · simp only [native_cap_widths hN0, mul_assoc]

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
