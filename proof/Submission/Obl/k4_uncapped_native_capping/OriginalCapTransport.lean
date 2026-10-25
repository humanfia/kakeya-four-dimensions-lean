/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/OriginalCapTransport.lean. Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.NativeCoordinates
import Submission.Obl.k4_uncapped_native_capping.ScalarCapAssembly

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

/-- Applying a common physical mask preserves original domination on that
same mask, with no normalization or change of the budget. -/
theorem original_domination_restrict_preimage
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ρ : Measure β) (R : ENNReal) (f : α → β)
    (hf : Measurable f) (H : Set β) (hH : MeasurableSet H)
    (hdom : R • Measure.map f μ ≤ ρ) :
    R • Measure.map f (μ.restrict (f ⁻¹' H)) ≤ ρ.restrict H := by
  rw [← Measure.restrict_map hf hH, ← Measure.restrict_smul]
  exact Measure.restrict_mono le_rfl hdom

/-- Original domination suffices for cap transport; the analytical law need
not have been constructed by any particular normalization formula. -/
theorem original_law_test_cap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ρ : Measure β) (R : ENNReal) (f : α → β)
    (hf : Measurable f) (hR : R ≠ 0) (hRfinite : R ≠ ⊤)
    (hdom : R • Measure.map f μ ≤ ρ)
    (E : Set α) (V : Set β) (hV : MeasurableSet V)
    (hcoord : ∀ᵐ z ∂μ, z ∈ E ↔ f z ∈ V)
    (c : ENNReal) (hcap : ρ V ≤ R * c) : μ E ≤ c := by
  have htest : μ E = μ (f ⁻¹' V) :=
    measure_congr (hcoord.mono (fun _ h => propext h))
  have hbound : R * μ E ≤ R * c := by
    rw [htest]
    calc
      _ = (R • Measure.map f μ) V := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf hV]
      _ ≤ ρ V := hdom V
      _ ≤ _ := hcap
  calc
    μ E = R⁻¹ * (R * μ E) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hR hRfinite, one_mul]
    _ ≤ R⁻¹ * (R * c) := mul_le_mul' le_rfl hbound
    _ = c := by rw [← mul_assoc, ENNReal.inv_mul_cancel hR hRfinite, one_mul]

def packetAxis (q : ℝ) (v : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![q * v 1, q * v 2]

def physicalProjection (e : EuclideanSpace ℝ (Fin 2)) (t₀ Z q : ℝ) (p : Inc) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(p.2 - t₀) / q, (inner ℝ e (y p.1 p.2) - Z) / q]

theorem measurable_physicalProjection (e : EuclideanSpace ℝ (Fin 2)) (t₀ Z q : ℝ) :
    Measurable (physicalProjection e t₀ Z q) := by
  unfold physicalProjection y x
  fun_prop

/-- The geometric axis `q * tangent` reads the exact native scalar slope
and base, with the original native polynomial as signal. -/
theorem nativeCoeff_expanded_projection
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q offset : ℝ) (hq : q ≠ 0) (v' : Fin 3 → ℝ) (hv : v' 0 = 0)
    {A : Set Traj} {z : Inc} (hz : z.1 ∈ A) :
    let b := nativeCoeff P t₀ q offset v' A z.1
    let p : Inc := (z.1, t₀ + q * z.2)
    WithLp.toLp 2 ![z.2, scalarY b z.2] =
        physicalProjection (packetAxis q v') t₀ (-q * offset) q p ∧
      scalarX b z.2 = MvPolynomial.eval (x p.1 p.2) P ∧
      b 1 = inner ℝ (packetAxis q v') (v z.1) := by
  dsimp only
  refine ⟨?_, nativeCoeff_scalarX P hP t₀ q offset v' hz z.2, ?_⟩
  · rw [nativeCoeff_scalarY P t₀ q offset v' hz]
    ext i
    fin_cases i
    · simp [physicalProjection]
      field_simp
    · simp [physicalProjection, packetAxis, PiLp.inner_apply, Fin.sum_univ_two,
        Fin.sum_univ_three, y, x, hv]
      field_simp
      ring
  · simp [nativeCoeff, hz, packetAxis, PiLp.inner_apply, Fin.sum_univ_two,
      Fin.sum_univ_three, x, v, hv]
    ring

theorem measurableSet_projected_pure_event
    (P : MvPolynomial (Fin 4) ℝ) (e : EuclideanSpace ℝ (Fin 2)) (t₀ Z q w : ℝ)
    (j : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E) :
    MeasurableSet {p : Inc | physicalProjection e t₀ Z q p ∈ E ∧
      ⌊MvPolynomial.eval (x p.1 p.2) P / w⌋ = j} := by
  exact (hE.preimage (measurable_physicalProjection e t₀ Z q)).inter
    (measurableSet_eq_fun
      ((P.continuous_eval.measurable.comp
        (show Measurable (fun p : Inc => x p.1 p.2) by unfold x; fun_prop)).div_const _).floor
      measurable_const)

theorem measurableSet_projected_angular_event
    (P : MvPolynomial (Fin 4) ℝ) (e : EuclideanSpace ℝ (Fin 2)) (t₀ Z q w a : ℝ)
    (j k : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E) :
    MeasurableSet {p : Inc | physicalProjection e t₀ Z q p ∈ E ∧
      ⌊MvPolynomial.eval (x p.1 p.2) P / w⌋ = j ∧ ⌊inner ℝ e (v p.1) / a⌋ = k} := by
  convert (measurableSet_projected_pure_event P e t₀ Z q w j E hE).inter
    (measurableSet_eq_fun
      (show Measurable (fun p : Inc => ⌊inner ℝ e (v p.1) / a⌋) by unfold v; fun_prop)
      measurable_const) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff]
  tauto

/-- Projected caps on an original dominating law give all frozen scalar
caps for an arbitrary normalized law with the same full budget. -/
theorem native_law_caps_of_original_domination
    {N χ d s m S U : ℝ} (hN : 0 < N)
    (ν : Measure Traj) (A : Set Traj) (t₀ q offset : ℝ) (hq : 0 < q)
    (v' : Fin 3 → ℝ) (hv : v' 0 = 0) (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (μ ρ : Measure Inc)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤)
    (hdom : (ENNReal.ofReal q * ν A) •
      Measure.map (fun z : Inc => (z.1, t₀ + q * z.2)) μ ≤ ρ)
    (hsupport : ∀ᵐ z ∂μ, z.1 ∈ A)
    (hregular : RegularScalarLaw N χ d s m S U ((ν A)⁻¹ • ν.restrict A) μ
      (nativeCoeff P t₀ q offset v' A))
    (hpure : ∀ (r : ℝ) (j : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
      0 ≤ r → r ≤ s → MeasurableSet E →
      ρ {p | physicalProjection (packetAxis q v') t₀ (-q * offset) q p ∈ E ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j} ≤
          (ENNReal.ofReal q * ν A) * ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d) * volume E)
    (hangular : ∀ (r : ℝ) (j k : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
      0 < r → r ≤ U → MeasurableSet E →
      ρ {p | physicalProjection (packetAxis q v') t₀ (-q * offset) q p ∈ E ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-s)⌋ = j ∧
        ⌊inner ℝ (packetAxis q v') (v p.1) / N ^ (-r)⌋ = k} ≤
          (ENNReal.ofReal q * ν A) *
            ENNReal.ofReal (N ^ χ * (N ^ (-s)) ^ d * N ^ (-S * r)) * volume E) :
    ScalarCaps N χ d s m S U ((ν A)⁻¹ • ν.restrict A) μ
      (nativeCoeff P t₀ q offset v' A) := by
  let b := nativeCoeff P t₀ q offset v' A
  have hbudget : ENNReal.ofReal q * ν A ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hq).ne' hA
  have hfinite : ENNReal.ofReal q * ν A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
  apply ScalarCaps.of_continuous hN hregular
  · intro r j E hr hrs hE
    refine original_law_test_cap μ ρ (ENNReal.ofReal q * ν A)
      (fun z : Inc => (z.1, t₀ + q * z.2)) (by fun_prop) hbudget hfinite hdom
      {z | WithLp.toLp 2 ![z.2, scalarY (b z.1) z.2] ∈ E ∧
        ⌊scalarX (b z.1) z.2 / N ^ (-r)⌋ = j}
      {p | physicalProjection (packetAxis q v') t₀ (-q * offset) q p ∈ E ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j}
      (measurableSet_projected_pure_event P _ _ _ _ _ _ _ hE) ?_
      (ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d) * volume E) ?_
    · filter_upwards [hsupport] with z hz
      obtain ⟨hbase, hsignal, _⟩ := nativeCoeff_expanded_projection P hP t₀ q offset hq.ne' v' hv hz
      change (_ ∈ E ∧ ⌊scalarX (b z.1) z.2 / N ^ (-r)⌋ = j) ↔ _
      rw [hbase, hsignal]
    · simpa only [mul_assoc] using hpure r j E hr hrs hE
  · intro r j k E hr hrU hE
    refine original_law_test_cap μ ρ (ENNReal.ofReal q * ν A)
      (fun z : Inc => (z.1, t₀ + q * z.2)) (by fun_prop) hbudget hfinite hdom
      {z | WithLp.toLp 2 ![z.2, scalarY (b z.1) z.2] ∈ E ∧
        ⌊scalarX (b z.1) z.2 / N ^ (-s)⌋ = j ∧ ⌊b z.1 1 / N ^ (-r)⌋ = k}
      {p | physicalProjection (packetAxis q v') t₀ (-q * offset) q p ∈ E ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-s)⌋ = j ∧
        ⌊inner ℝ (packetAxis q v') (v p.1) / N ^ (-r)⌋ = k}
      (measurableSet_projected_angular_event P _ _ _ _ _ _ _ _ _ hE) ?_
      (ENNReal.ofReal (N ^ χ * (N ^ (-s)) ^ d * N ^ (-S * r)) * volume E) ?_
    · filter_upwards [hsupport] with z hz
      obtain ⟨hbase, hsignal, hslope⟩ := nativeCoeff_expanded_projection P hP t₀ q offset hq.ne' v' hv hz
      change b z.1 1 = _ at hslope
      change (_ ∈ E ∧ ⌊scalarX (b z.1) z.2 / N ^ (-s)⌋ = j ∧ ⌊b z.1 1 / N ^ (-r)⌋ = k) ↔ _
      rw [hbase, hsignal, hslope]
    · simpa only [mul_assoc] using hangular r j k E hr hrU hE

end
end Submission.Obl.k4_uncapped_native_capping
