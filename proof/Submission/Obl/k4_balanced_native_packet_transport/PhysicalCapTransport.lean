import Submission.Obl.k4_balanced_native_packet_transport.SelectedBlockLaws
import Submission.Obl.k4_balanced_native_packet_transport.PhysicalCoordinates
import Submission.Obl.k4_balanced_native_packet_transport.ScalarCapAssembly

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Set
open Submission.Obl.k4_native_finite_terminal_atlas_lift (normalizedIncidenceEquiv)
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

/-- A physical cap with its full fixed budget cancels that same budget in
the unit-block law. -/
theorem selectedBlockLaw_cap
    (ν : Measure Traj) (A : Set Traj) (t₀ q : ℝ) (hq : 0 < q)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤)
    (hsource : s • μ ≤ ν.prod volume)
    (E : Set Inc) (hE : MeasurableSet E) (c : ENNReal)
    (hcap : ((ν.prod volume).restrict H)
      (normalizedIncidenceEquiv (MeasurableEquiv.refl Traj) t₀ q hq.ne' ⁻¹' E) ≤
      (ENNReal.ofReal q * ν A) * c) :
    selectedBlockLaw ν A t₀ q hq s μ H E ≤ c := by
  have hselected : s • μ.restrict H ≤ (ν.prod volume).restrict H := by
    rw [← Measure.restrict_smul]
    exact Measure.restrict_mono le_rfl hsource
  rw [selectedBlockLaw, unitBlockLaw, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply
      (normalizedIncidenceEquiv (MeasurableEquiv.refl Traj) t₀ q hq.ne').measurable hE]
  calc
    _ ≤ (ENNReal.ofReal q * ν A)⁻¹ *
        ((ν.prod volume).restrict H)
          (normalizedIncidenceEquiv (MeasurableEquiv.refl Traj) t₀ q hq.ne' ⁻¹' E) :=
      mul_le_mul' le_rfl (hselected _)
    _ ≤ (ENNReal.ofReal q * ν A)⁻¹ * ((ENNReal.ofReal q * ν A) * c) :=
      mul_le_mul' le_rfl hcap
    _ = c := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel (mul_ne_zero (ENNReal.ofReal_pos.mpr hq).ne' hA)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin), one_mul]

theorem selectedBlockLaw_test_cap
    (ν : Measure Traj) (A : Set Traj) (t₀ q : ℝ) (hq : 0 < q)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc) (hH : MeasurableSet H)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤)
    (hsource : s • μ ≤ ν.prod volume)
    (E V : Set Inc) (hE : MeasurableSet E) (c : ENNReal)
    (hcoord : ∀ p ∈ H, (p.1, (p.2 - t₀) / q) ∈ E ↔ p ∈ V)
    (hcap : ((ν.prod volume).restrict H) V ≤ (ENNReal.ofReal q * ν A) * c) :
    selectedBlockLaw ν A t₀ q hq s μ H E ≤ c := by
  apply selectedBlockLaw_cap ν A t₀ q hq s μ H hA hAfin hsource E hE c
  have heq : ((ν.prod volume).restrict H)
      (normalizedIncidenceEquiv (MeasurableEquiv.refl Traj) t₀ q hq.ne' ⁻¹' E) =
      ((ν.prod volume).restrict H) V := by
    apply measure_congr
    filter_upwards [ae_restrict_mem hH] with p hp
    exact propext (hcoord p hp)
  rw [heq]
  exact hcap

theorem measurableSet_scalar_pure_event (b : Traj → Fin 5 → ℝ) (hb : Measurable b)
    (a : ℝ) (j : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E) :
    MeasurableSet {p : Inc | WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∈ E ∧
      ⌊scalarX (b p.1) p.2 / a⌋ = j} := by
  have hbase : Measurable (fun p : Inc =>
      (WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] : EuclideanSpace ℝ (Fin 2))) := by
    unfold scalarY
    fun_prop
  have hsignal : Measurable (fun p : Inc => ⌊scalarX (b p.1) p.2 / a⌋) := by
    unfold scalarX
    fun_prop
  exact (hE.preimage hbase).inter (measurableSet_eq_fun hsignal measurable_const)

theorem measurableSet_scalar_angular_event (b : Traj → Fin 5 → ℝ) (hb : Measurable b)
    (a w : ℝ) (j k : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E) :
    MeasurableSet {p : Inc | WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∈ E ∧
      ⌊scalarX (b p.1) p.2 / a⌋ = j ∧ ⌊b p.1 1 / w⌋ = k} := by
  have hslope : Measurable (fun p : Inc => ⌊b p.1 1 / w⌋) := by fun_prop
  convert (measurableSet_scalar_pure_event b hb a j E hE).inter
    (measurableSet_eq_fun hslope measurable_const) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff]
  tauto

/-- All original continuous pure and angular caps pass to the selected law.
The exact scalar coefficients and full assignment prior are unchanged. -/
theorem native_selectedBlockLaw_caps
    {N χ d r m S U : ℝ} (hN : 0 < N)
    (ν : Measure Traj) (A : Set Traj) (t₀ q offset center : ℝ) (hq : 0 < q)
    (v : Fin 3 → ℝ) (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc) (hH : MeasurableSet H)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤)
    (hsource : s • μ ≤ ν.prod volume) (hsub : ∀ p ∈ H, p.1 ∈ A)
    (hregular : RegularScalarLaw N χ d r m S U ((ν A)⁻¹ • ν.restrict A)
      (selectedBlockLaw ν A t₀ q hq s μ H)
      (nativeCoeff P t₀ q ((offset - center) / q) (fun i => v i / q) A))
    (hpure : ∀ (a : ℝ) (j : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
      0 ≤ a → a ≤ r → MeasurableSet E →
      ((ν.prod volume).restrict H) {p | physicalScalarBase t₀ q offset center v p ∈ E ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-a)⌋ = j} ≤
          (ENNReal.ofReal q * ν A) * ENNReal.ofReal (N ^ χ * (N ^ (-a)) ^ d) * volume E)
    (hangular : ∀ (a : ℝ) (j k : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
      0 < a → a ≤ U → MeasurableSet E →
      ((ν.prod volume).restrict H) {p | physicalScalarBase t₀ q offset center v p ∈ E ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j ∧
        ⌊physicalScalarSlope v p.1 / N ^ (-a)⌋ = k} ≤
          (ENNReal.ofReal q * ν A) *
            ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d * N ^ (-S * a)) * volume E) :
    ScalarCaps N χ d r m S U ((ν A)⁻¹ • ν.restrict A)
      (selectedBlockLaw ν A t₀ q hq s μ H)
      (nativeCoeff P t₀ q ((offset - center) / q) (fun i => v i / q) A) := by
  let b := nativeCoeff P t₀ q ((offset - center) / q) (fun i => v i / q) A
  apply ScalarCaps.of_continuous hN hregular
  · intro a j E ha har hE
    apply selectedBlockLaw_test_cap ν A t₀ q hq s μ H hH hA hAfin hsource
      {p | WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∈ E ∧
        ⌊scalarX (b p.1) p.2 / N ^ (-a)⌋ = j}
      {p | physicalScalarBase t₀ q offset center v p ∈ E ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-a)⌋ = j}
      (measurableSet_scalar_pure_event b hregular.1 _ _ _ hE) _
    · intro p hp
      obtain ⟨hbase, hsignal, _⟩ :=
        nativeCoeff_physical_coordinates P hP t₀ q offset center hq.ne' v (hsub p hp)
      change (_ ∈ E ∧ ⌊scalarX (b p.1) ((p.2 - t₀) / q) / N ^ (-a)⌋ = j) ↔ _
      rw [hbase, hsignal]
      rfl
    · simpa only [mul_assoc] using hpure a j E ha har hE
  · intro a j k E ha haU hE
    apply selectedBlockLaw_test_cap ν A t₀ q hq s μ H hH hA hAfin hsource
      {p | WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∈ E ∧
        ⌊scalarX (b p.1) p.2 / N ^ (-r)⌋ = j ∧ ⌊b p.1 1 / N ^ (-a)⌋ = k}
      {p | physicalScalarBase t₀ q offset center v p ∈ E ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j ∧
        ⌊physicalScalarSlope v p.1 / N ^ (-a)⌋ = k}
      (measurableSet_scalar_angular_event b hregular.1 _ _ _ _ _ hE) _
    · intro p hp
      obtain ⟨hbase, hsignal, hslope⟩ :=
        nativeCoeff_physical_coordinates P hP t₀ q offset center hq.ne' v (hsub p hp)
      change (_ ∈ E ∧ ⌊scalarX (b p.1) ((p.2 - t₀) / q) / N ^ (-r)⌋ = j ∧
        ⌊b p.1 1 / N ^ (-a)⌋ = k) ↔ _
      change b p.1 1 = physicalScalarSlope v p.1 at hslope
      rw [hbase, hsignal, hslope]
      rfl
    · simpa only [mul_assoc] using hangular a j k E ha haU hE

end
end Submission.Obl.k4_balanced_native_packet_transport
