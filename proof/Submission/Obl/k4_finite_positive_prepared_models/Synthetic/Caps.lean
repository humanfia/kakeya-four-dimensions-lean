import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.ModelDefs

/-!
# Cell caps of the synthetic model

A cell of side `ε` in time, position at that time and transverse position, a hidden bin of
width `ε' ≤ 2^(-e g)` and a slope event `V` have joint sample-time mass at most
`ε³ · 2 · 2^(-e₁ g) · P(β u₃ ∈ V)`: the time, the transverse position, the hidden coordinate
and the position given the slope are independent, each spread with bounded density. Written by
x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

theorem floor_div_eq_iff {x ε : ℝ} (hε : 0 < ε) (z : ℤ) :
    ⌊x / ε⌋ = z ↔ x ∈ Ico ((z : ℝ) * ε) ((z : ℝ) * ε + ε) := by
  rw [Int.floor_eq_iff, mem_Ico, le_div_iff₀ hε, div_lt_iff₀ hε]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

namespace Synth

variable (S : Synth)

theorem measurable_hidl : Measurable (fun l : ℕ × (Fin 6 → ℝ) =>
    hid S.e S.e₁ S.G l.1 (l.2 2)) :=
  (measurable_hid S.e S.e₁ S.G).comp
    (measurable_fst.prodMk ((measurable_pi_apply 2).comp measurable_snd))

/-- **Cell cap.** -/
theorem cap_core {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (q0 q1 q2 a : ℤ) {V : Set ℝ}
    (hV : MeasurableSet V) {g : ℕ} (hg : g ≤ S.G) (hgε : ε' ≤ 1 / 2 ^ (S.e * g)) :
    ((P S.M).prod (volume : Measure ℝ)) {x : Ω × ℝ | ⌊x.2 / ε⌋ = q0 ∧
        ⌊(x.1.2.1.1 + x.2 * (S.β * x.1.2.1.2)) / ε⌋ = q1 ∧ ⌊x.1.2.2 / ε⌋ = q2 ∧
        ⌊hid S.e S.e₁ S.G x.1.1.1 x.1.1.2 / ε'⌋ = a ∧ S.β * x.1.2.1.2 ∈ V} ≤
      ENNReal.ofReal ε * ((2 * ((2 : ENNReal) ^ (S.e₁ * g))⁻¹) *
        ((ENNReal.ofReal ε * U {u | S.β * u ∈ V}) * ENNReal.ofReal ε)) := by
  set E : Set (Ω × ℝ) := {x : Ω × ℝ | ⌊x.2 / ε⌋ = q0 ∧
        ⌊(x.1.2.1.1 + x.2 * (S.β * x.1.2.1.2)) / ε⌋ = q1 ∧ ⌊x.1.2.2 / ε⌋ = q2 ∧
        ⌊hid S.e S.e₁ S.G x.1.1.1 x.1.1.2 / ε'⌋ = a ∧ S.β * x.1.2.1.2 ∈ V} with hE
  have hEm : MeasurableSet E := by
    have hh : Measurable (fun x : Ω × ℝ => hid S.e S.e₁ S.G x.1.1.1 x.1.1.2) :=
      (measurable_hid _ _ _).comp (measurable_fst.comp measurable_fst)
    refine (measurableSet_eq_fun (Int.measurable_floor.comp (by fun_prop)) measurable_const).inter
      ((measurableSet_eq_fun (Int.measurable_floor.comp (by fun_prop)) measurable_const).inter
      ((measurableSet_eq_fun (Int.measurable_floor.comp (by fun_prop)) measurable_const).inter
      ((measurableSet_eq_fun (Int.measurable_floor.comp (hh.div_const _)) measurable_const).inter
      (((measurable_const_mul _).comp (by fun_prop)) hV))))
  set C : ENNReal := (2 * ((2 : ENNReal) ^ (S.e₁ * g))⁻¹) *
    ((ENNReal.ofReal ε * U {u | S.β * u ∈ V}) * ENNReal.ofReal ε)
  have hsec : ∀ t, P S.M ((fun ω => (ω, t)) ⁻¹' E) ≤
      (Ico ((q0 : ℝ) * ε) ((q0 : ℝ) * ε + ε)).indicator (fun _ => C) t := by
    intro t
    by_cases ht : t ∈ Ico ((q0 : ℝ) * ε) ((q0 : ℝ) * ε + ε)
    · rw [indicator_of_mem ht]
      have hsub : (fun ω => (ω, t)) ⁻¹' E ⊆
          {p : ℕ × ℝ | hid S.e S.e₁ S.G p.1 p.2 ∈ Ico ((a : ℝ) * ε') ((a : ℝ) * ε' + ε')} ×ˢ
          ({p : ℝ × ℝ | p.1 + t * S.β * p.2 ∈ Ico ((q1 : ℝ) * ε) ((q1 : ℝ) * ε + ε) ∧
            S.β * p.2 ∈ V} ×ˢ Ico ((q2 : ℝ) * ε) ((q2 : ℝ) * ε + ε)) := by
        intro ω hω
        obtain ⟨-, h1, h2, h3, h4⟩ := hω
        refine ⟨(floor_div_eq_iff hε' a).mp h3, ⟨?_, h4⟩, (floor_div_eq_iff hε q2).mp h2⟩
        have := (floor_div_eq_iff hε q1).mp h1
        simpa [mul_assoc] using this
      calc P S.M ((fun ω => (ω, t)) ⁻¹' E)
          ≤ ((idx S.M).prod U) {p : ℕ × ℝ | hid S.e S.e₁ S.G p.1 p.2 ∈
              Ico ((a : ℝ) * ε') ((a : ℝ) * ε' + ε')} *
            ((U.prod U) {p : ℝ × ℝ | p.1 + t * S.β * p.2 ∈
              Ico ((q1 : ℝ) * ε) ((q1 : ℝ) * ε + ε) ∧ S.β * p.2 ∈ V} *
              U (Ico ((q2 : ℝ) * ε) ((q2 : ℝ) * ε + ε))) := P_mono_prod S.M hsub
        _ ≤ C := by
            refine mul_le_mul' (hid_cap S.he hg _ _ hgε) (mul_le_mul' ?_ ?_)
            · refine (UU_shear_le t S.β measurableSet_Ico hV).trans ?_
              rw [Real.volume_Ico]
              simp
            · refine (U_le_volume _).trans ?_
              rw [Real.volume_Ico]
              simp
    · rw [indicator_of_notMem ht]
      refine le_of_eq (measure_mono_null ?_ (measure_empty (μ := P S.M)))
      intro ω hω
      exact ht ((floor_div_eq_iff hε q0).mp hω.1)
  rw [Measure.prod_apply_symm hEm]
  calc ∫⁻ t, P S.M ((fun ω => (ω, t)) ⁻¹' E)
      ≤ ∫⁻ t, (Ico ((q0 : ℝ) * ε) ((q0 : ℝ) * ε + ε)).indicator (fun _ => C) t :=
        lintegral_mono hsec
    _ = C * volume (Ico ((q0 : ℝ) * ε) ((q0 : ℝ) * ε + ε)) :=
        lintegral_indicator_const measurableSet_Ico C
    _ = ENNReal.ofReal ε * C := by
        rw [Real.volume_Ico, mul_comm]
        congr 2
        ring

end Synth

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
