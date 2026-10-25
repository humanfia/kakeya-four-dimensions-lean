import Submission.Obl.k4_scalar_guarded_tangent_preparation.UnnormalizedMeasured

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

/-- Joint caps survive finite readout of the state code. Reference masses
are summed on the original law, before the likelihood mask. -/
theorem state_union_joint_cap
    {Ω β : Type*} [MeasurableSpace Ω] (σ ρ : Measure Ω)
    (Y : Ω → ℕ) (Z : Ω → β) (hY : Measurable Y) (s : Finset ℕ)
    (C : ℝ≥0∞) (p : β → ℝ≥0∞)
    (hcap : ∀ e z, ρ {x | Y x = e ∧ Z x = z} ≤ C * σ {x | Y x = e} * p z)
    (z : β) :
    ρ {x | Y x ∈ s ∧ Z x = z} ≤ C * σ {x | Y x ∈ s} * p z := by
  classical
  have hcover : {x | Y x ∈ s ∧ Z x = z} ⊆
      ⋃ e ∈ s, {x | Y x = e ∧ Z x = z} := by
    rintro x ⟨hxY, hxZ⟩
    exact mem_iUnion₂.mpr ⟨Y x, hxY, rfl, hxZ⟩
  have hsum : (∑ e ∈ s, σ {x | Y x = e}) = σ {x | Y x ∈ s} := by
    exact sum_measure_preimage_singleton s (fun e _ => hY (measurableSet_singleton e))
  calc
    _ ≤ ρ (⋃ e ∈ s, {x | Y x = e ∧ Z x = z}) := measure_mono hcover
    _ ≤ ∑ e ∈ s, ρ {x | Y x = e ∧ Z x = z} := measure_biUnion_finset_le s _
    _ ≤ ∑ e ∈ s, C * σ {x | Y x = e} * p z := Finset.sum_le_sum (fun e _ => hcap e z)
    _ = C * (∑ e ∈ s, σ {x | Y x = e}) * p z := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [hsum]

/-- The original total mass cancels against its fixed palette identity.
The resulting ceiling applies to the masked numerator only. -/
theorem original_joint_to_fixed_palette
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (σ ρ : Measure Ω) [IsFiniteMeasure σ] [IsFiniteMeasure ρ]
    (π : Measure Λ) [IsFiniteMeasure π] (E F V : Set Ω) (B : Set Λ)
    {R : ℝ} (hR : 0 ≤ R) (htotal : 0 < σ.real univ)
    (hpalette : σ.real V = σ.real univ * π.real B)
    (hcap : ρ.real E * σ.real univ ≤ R * σ.real F * σ.real V) :
    ρ E ≤ ENNReal.ofReal R * σ F * π B := by
  have hreal : ρ.real E ≤ R * σ.real F * π.real B := by
    apply (mul_le_mul_iff_left₀ htotal).mp
    calc
      _ ≤ R * σ.real F * σ.real V := hcap
      _ = (R * σ.real F * π.real B) * σ.real univ := by rw [hpalette]; ring
  apply (ENNReal.toReal_le_toReal (measure_ne_top ρ E) (by finiteness)).mp
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR] using hreal

/-- A tested finite-code event is a union of the unchanged state fibers.
This applies to the grid rectangles predicted by a finite history. -/
theorem predicted_event_joint_cap
    {Ω β : Type*} [MeasurableSpace Ω] {n : ℕ} (σ ρ : Measure Ω)
    (X : Ω → Fin n) (hX : Measurable X) (Y : Fin n → ℕ) (Z : Fin n → β)
    (P : Set Ω) (Q : ℕ → Prop) (hP : ∀ x, x ∈ P ↔ Q (Y (X x)))
    (C : ℝ≥0∞) (p : β → ℝ≥0∞)
    (hcap : ∀ e z, ρ {x | Y (X x) = e ∧ Z (X x) = z} ≤
      C * σ {x | Y (X x) = e} * p z) (z : β) :
    ρ (P ∩ {x | Z (X x) = z}) ≤ C * σ P * p z := by
  classical
  let s := (Finset.univ.image Y).filter Q
  have hP' : P = {x | Y (X x) ∈ s} := by
    ext x
    simp only [s, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq, hP]
    exact ⟨fun h => ⟨⟨X x, rfl⟩, h⟩, fun h => h.2⟩
  rw [hP']
  exact state_union_joint_cap σ ρ (fun x => Y (X x)) (fun x => Z (X x))
    ((measurable_of_finite Y).comp hX) s C p hcap z

/-- Null exceptional code fibers may be removed using the original law;
every submeasure of that law has the same predicted-event readout. -/
theorem predicted_event_joint_cap_ae
    {Ω β : Type*} [MeasurableSpace Ω] {n : ℕ} (σ ρ : Measure Ω) (hρ : ρ ≤ σ)
    (X : Ω → Fin n) (hX : Measurable X) (Y : Fin n → ℕ) (Z : Fin n → β)
    (P : Set Ω) (Q : ℕ → Prop) (hP : ∀ᵐ x ∂σ, x ∈ P ↔ Q (Y (X x)))
    (C : ℝ≥0∞) (p : β → ℝ≥0∞)
    (hcap : ∀ e z, ρ {x | Y (X x) = e ∧ Z (X x) = z} ≤
      C * σ {x | Y (X x) = e} * p z) (z : β) :
    ρ (P ∩ {x | Z (X x) = z}) ≤ C * σ P * p z := by
  let P' := {x | Q (Y (X x))}
  have hPσ : P =ᵐ[σ] P' := by
    filter_upwards [hP] with x hx
    exact propext hx
  have hPρ : P =ᵐ[ρ] P' := (Measure.absolutelyContinuous_of_le hρ).ae_eq hPσ
  rw [measure_congr (ae_eq_set_inter hPρ Filter.EventuallyEq.rfl), measure_congr hPσ]
  exact predicted_event_joint_cap σ ρ X hX Y Z P' Q (fun _ => Iff.rfl) C p hcap z

end Submission.Obl.k4_scalar_guarded_tangent_preparation
