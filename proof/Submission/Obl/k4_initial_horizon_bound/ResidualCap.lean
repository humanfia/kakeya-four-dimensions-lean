import Submission.Lib.K4ContinuousPlanks.Continuous
import Submission.Obl.k4_initial_horizon_bound.Duration

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Lib.K4ContinuousPlanks

theorem trace_inner_le_of_endpoints
    (b u c w e : EuclideanSpace ℝ (Fin 2)) {r t : ℝ}
    (h₀ : |inner ℝ (b - c) e| ≤ r)
    (h₁ : |inner ℝ (b + u - c - w) e| ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |inner ℝ (b + t • u - c - t • w) e| ≤ r := by
  have heq : inner ℝ (b + t • u - c - t • w) e =
      (1 - t) * inner ℝ (b - c) e + t * inner ℝ (b + u - c - w) e := by
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    ring
  rw [heq]
  calc
    _ ≤ |(1 - t) * inner ℝ (b - c) e| +
        |t * inner ℝ (b + u - c - w) e| := abs_add_le _ _
    _ = (1 - t) * |inner ℝ (b - c) e| +
        t * |inner ℝ (b + u - c - w) e| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * r + t * r :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left h₁ ht.1)
    _ = r := by ring

theorem fullTracePlank_iff_endpoints
    (b u c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ) :
    InFullTracePlank b u c w e₁ e₂ a β ↔
      (|inner ℝ (b - c) e₁| ≤ a ∧ |inner ℝ (b - c) e₂| ≤ β) ∧
      (|inner ℝ (b + u - c - w) e₁| ≤ a ∧ |inner ℝ (b + u - c - w) e₂| ≤ β) := by
  constructor
  · intro h
    simpa only [zero_smul, one_smul, add_zero, sub_zero] using
      And.intro (h 0 (by simp)) (h 1 (by simp))
  · rintro ⟨h₀, h₁⟩ t ht
    exact ⟨trace_inner_le_of_endpoints b u c w e₁ h₀.1 h₁.1 ht,
      trace_inner_le_of_endpoints b u c w e₂ h₀.2 h₁.2 ht⟩

theorem measurableSet_fullTracePlank {α : Type*} [MeasurableSpace α]
    (b u : α → EuclideanSpace ℝ (Fin 2)) (hb : Measurable b) (hu : Measurable u)
    (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ) :
    MeasurableSet {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} := by
  simp only [fullTracePlank_iff_endpoints]
  have h₀ (e : EuclideanSpace ℝ (Fin 2)) : Measurable (fun x => |inner ℝ (b x - c) e|) := by
    fun_prop
  have h₁ (e : EuclideanSpace ℝ (Fin 2)) :
      Measurable (fun x => |inner ℝ (b x + u x - c - w) e|) := by fun_prop
  exact ((measurableSet_le (h₀ e₁) measurable_const).inter
    (measurableSet_le (h₀ e₂) measurable_const)).inter
    ((measurableSet_le (h₁ e₁) measurable_const).inter
      (measurableSet_le (h₁ e₂) measurable_const))

/-- The stopping rule for residual incidence mass gives a full-time cap
for the retained original prior, at the cost of the duration floor alone. -/
theorem residual_incidence_cap_to_prior {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (E : Set (α × ℝ)) (hE : MeasurableSet E)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (hb : Measurable b) (hu : Measurable u)
    (H : Set α) (hH : MeasurableSet H) {τ A : ℝ} (hτ : 0 < τ)
    (hduration : ∀ x ∈ H, ENNReal.ofReal τ ≤ incidenceDuration E x)
    (hstop : ∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ),
      ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 0 < a → a ≤ β →
      (ν.withDensity (incidenceDuration E))
        {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} ≤
          ENNReal.ofReal (A * a * β)) :
    MeasureFullPlankCap (ν.restrict H) b u (A / τ) := by
  intro c w e₁ e₂ a β he₁ he₂ he ha hab
  let S := {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β}
  have hS : MeasurableSet S := measurableSet_fullTracePlank b u hb hu c w e₁ e₂ a β
  have hbound : ENNReal.ofReal τ * (ν.restrict H) S ≤ ENNReal.ofReal (A * a * β) :=
    (retained_duration_prior_bound ν hE hS hH (ENNReal.ofReal τ)
      (fun x hx => hduration x hx.2)).trans (hstop c w e₁ e₂ a β he₁ he₂ he ha hab)
  have hdiv : (ν.restrict H) S ≤ ENNReal.ofReal (A * a * β) / ENNReal.ofReal τ := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using hbound
  have heq : A / τ * a * β = A * a * β / τ := by ring
  simpa only [heq, ENNReal.ofReal_div_of_pos hτ] using hdiv

end Submission.Obl.k4_initial_horizon_bound
