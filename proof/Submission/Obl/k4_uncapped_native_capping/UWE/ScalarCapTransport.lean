/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/ScalarCapTransport.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/ScalarCapTransport.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.NativeGridCap
import Submission.Obl.k4_uncapped_native_capping.UWE.ScalarCandidates

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- Transport an original continuous packet cap to the exact five-coefficient
scalar law. The multiplier is the inverse FIXED original packet budget. -/
theorem scalar_cap_of_original_packet_cap
    (ρ law : Measure Incidence) (β : ENNReal) (t₀ q Z : ℝ)
    (e : EuclideanSpace ℝ (Fin 2))
    (hlaw : law = β • ρ.map (fun p : Incidence => (p.1, (p.2 - t₀) / q)))
    (b : Trajectory → Fin 5 → ℝ) (hb : Measurable b)
    (P : MvPolynomial (Fin 4) ℝ)
    (hcoord : ∀ᵐ p ∂ρ,
      scalarY (b p.1) ((p.2 - t₀) / q) = (inner ℝ e (y p.1 p.2) - Z) / q ∧
      scalarX (b p.1) ((p.2 - t₀) / q) = MvPolynomial.eval (x p.1 p.2) P)
    (a : ℝ) (j : ℤ) (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U)
    (C : ENNReal)
    (hcap : ρ {p | packetProjection e t₀ Z q p ∈ U ∧
      ⌊MvPolynomial.eval (x p.1 p.2) P / a⌋ = j} ≤ C * volume U) :
    law {p | (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
      ⌊scalarX (b p.1) p.2 / a⌋ = j} ≤ β * C * volume U := by
  have hY : Measurable (fun p : Incidence =>
      (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2))) := by
    unfold scalarY
    fun_prop
  have hX : Measurable (fun p : Incidence => ⌊scalarX (b p.1) p.2 / a⌋) := by
    unfold scalarX
    fun_prop
  have hE : MeasurableSet {p : Incidence |
      (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
      ⌊scalarX (b p.1) p.2 / a⌋ = j} :=
    (hU.preimage hY).inter (measurableSet_eq_fun hX measurable_const)
  rw [hlaw, Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop) hE]
  have heq : ρ ((fun p : Incidence => (p.1, (p.2 - t₀) / q)) ⁻¹'
      {p | (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
        ⌊scalarX (b p.1) p.2 / a⌋ = j}) =
      ρ {p | packetProjection e t₀ Z q p ∈ U ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / a⌋ = j} := by
    apply measure_congr
    filter_upwards [hcoord] with p hp
    apply propext
    simp only [mem_preimage, mem_ofPred_eq, hp.1, hp.2, packetProjection]
  rw [heq]
  simpa only [mul_assoc] using mul_le_mul' (le_refl β) hcap

/-- The angular scalar cap uses the same original law and coordinate map. -/
theorem scalar_angular_cap_of_original_packet_cap
    (ρ law : Measure Incidence) (β : ENNReal) (t₀ q Z : ℝ)
    (e : EuclideanSpace ℝ (Fin 2))
    (hlaw : law = β • ρ.map (fun p : Incidence => (p.1, (p.2 - t₀) / q)))
    (b : Trajectory → Fin 5 → ℝ) (hb : Measurable b)
    (P : MvPolynomial (Fin 4) ℝ)
    (hcoord : ∀ᵐ p ∂ρ,
      scalarY (b p.1) ((p.2 - t₀) / q) = (inner ℝ e (y p.1 p.2) - Z) / q ∧
      scalarX (b p.1) ((p.2 - t₀) / q) = MvPolynomial.eval (x p.1 p.2) P ∧
      b p.1 1 = inner ℝ e (v p.1))
    (a w : ℝ) (j k : ℤ) (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U)
    (C : ENNReal)
    (hcap : ρ {p | packetProjection e t₀ Z q p ∈ U ∧
      ⌊MvPolynomial.eval (x p.1 p.2) P / a⌋ = j ∧ ⌊inner ℝ e (v p.1) / w⌋ = k} ≤ C * volume U) :
    law {p | (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
      ⌊scalarX (b p.1) p.2 / a⌋ = j ∧ ⌊b p.1 1 / w⌋ = k} ≤ β * C * volume U := by
  have hY : Measurable (fun p : Incidence =>
      (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2))) := by
    unfold scalarY
    fun_prop
  have hX : Measurable (fun p : Incidence => ⌊scalarX (b p.1) p.2 / a⌋) := by
    unfold scalarX
    fun_prop
  have hV : Measurable (fun p : Incidence => ⌊b p.1 1 / w⌋) := by fun_prop
  have hE : MeasurableSet {p : Incidence |
      (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
      ⌊scalarX (b p.1) p.2 / a⌋ = j ∧ ⌊b p.1 1 / w⌋ = k} :=
    (hU.preimage hY).inter ((measurableSet_eq_fun hX measurable_const).inter
      (measurableSet_eq_fun hV measurable_const))
  rw [hlaw, Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop) hE]
  have heq : ρ ((fun p : Incidence => (p.1, (p.2 - t₀) / q)) ⁻¹'
      {p | (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
        ⌊scalarX (b p.1) p.2 / a⌋ = j ∧ ⌊b p.1 1 / w⌋ = k}) =
      ρ {p | packetProjection e t₀ Z q p ∈ U ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / a⌋ = j ∧ ⌊inner ℝ e (v p.1) / w⌋ = k} := by
    apply measure_congr
    filter_upwards [hcoord] with p hp
    apply propext
    simp only [mem_preimage, mem_ofPred_eq, hp.1, hp.2.1, hp.2.2, packetProjection]
  rw [heq]
  simpa only [mul_assoc] using mul_le_mul' (le_refl β) hcap

/-- The physical time factor cancels exactly against the full original budget;
the only geometric density ratio left is the balanced determinant/prior ratio. -/
theorem fixed_packet_budget_cancel {q a J K : ℝ} (hq : 0 < q) (ha : 0 < a) :
    (ENNReal.ofReal q * ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (4 * K ^ 2 * q * J) =
      ENNReal.ofReal (4 * K ^ 2 * J / a) := by
  have heq : 4 * K ^ 2 * q * J = (q * a) * (4 * K ^ 2 * J / a) := by
    field_simp
  have hb0 : ENNReal.ofReal q * ENNReal.ofReal a ≠ 0 := by
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hq))
      (ne_of_gt (ENNReal.ofReal_pos.mpr ha))
  have hbtop : ENNReal.ofReal q * ENNReal.ofReal a ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [heq, ENNReal.ofReal_mul (mul_nonneg hq.le ha.le), ENNReal.ofReal_mul hq.le,
    ← mul_assoc, ENNReal.inv_mul_cancel hb0 hbtop, one_mul]

end Submission.Obl.k4_uncapped_native_capping.UWE
