/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeWitnesses.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeAssignments
import Submission.Obl.k4_horizontal_strict_parameter_step.InheritedWitnesses

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The original fitted witness pays its fourth-power time volume at every
horizontal rate. This uses the whole unchanged assignment prior. -/
theorem original_witness_floor {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hν : IsProbabilityMeasure (cfg.ν k)) (hN : 0 < cfg.N k) (hK : 0 < cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ) (i : Fin (cfg.n k s)) :
    ENNReal.ofReal (cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3) ≤
      cfg.μ k (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)) := by
  letI := hν
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hlo := (cfg.prior_bounds a hν hN hK hℓ i).1
  have hprior : ENNReal.ofReal
      (cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2) ≤
        cfg.ν k (cfg.A k s i) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (cfg.ν k) _)]
    exact ENNReal.ofReal_le_ofReal hlo
  have hm := mul_le_mul_right hprior (ENNReal.ofReal (cfg.timeLength k s / cfg.K k))
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ cfg.timeLength k s / cfg.K k)] at hm
  apply (le_of_eq ?_).trans (hm.trans (a.witness_lower i))
  congr 1
  field_simp <;> ring

/-- Positive original incidence mass forces at least one true label, so the
native hidden equation and contact defect hold without critical-rate validity. -/
theorem native_equation {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hμ : cfg.μ k univ ≠ 0) :
    cfg.P k = MvPolynomial.X (3 : Fin 4) ∧
      ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) := by
  have hn : 0 < cfg.n k s := by
    by_contra hn
    have hz : cfg.n k s = 0 := Nat.eq_zero_of_not_pos hn
    have hf : ∀ᵐ p ∂cfg.μ k, False := a.covers.mono (by
      rintro p ⟨i, hi, ht⟩
      have hi' := i.isLt
      omega)
    apply hμ
    simpa only [ae_iff, not_false_eq_true, Set.setOf_true] using hf
  exact ⟨a.native_hidden ⟨0, hn⟩, a.horizontal_equation ⟨0, hn⟩⟩

/-- Nested child assignments inherit the parent's full affine fit without
altering any original child witness floor. -/
theorem inherited_witness_mass {k : ℕ} {s t : ℝ}
    (a : cfg.AssignmentLevel k s) (a' : cfg.AssignmentLevel k t)
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (i : Fin (cfg.n k t)) (j : Fin (cfg.n k s))
    (hA : cfg.A k t i ⊆ cfg.A k s j)
    (hI : Data.I (cfg.T k t) (cfg.j k t i) ⊆ Data.I (cfg.T k s) (cfg.j k s j)) :
    cfg.μ k ((cfg.B k t i ∩ cfg.B k s j) ×ˢ Data.I (cfg.T k t) (cfg.j k t i)) =
      cfg.μ k (cfg.B k t i ×ˢ Data.I (cfg.T k t) (cfg.j k t i)) := by
  exact child_ancestor_witness_mass (cfg.ν k) (cfg.μ k) _ hdom _
    (cfg.j k s) (cfg.A k s) (cfg.B k s) a.fitted_subset a.disjoint a.covers j
    (cfg.B k t i) (Data.I (cfg.T k t) (cfg.j k t i))
    ((a'.fitted_subset i).trans hA) hI

end NativeModel

end Submission.Obl.k4_horizontal_strict_parameter_step
