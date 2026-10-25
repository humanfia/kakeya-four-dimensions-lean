import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartDefs
import Submission.Obl.k4_horizontal_supercritical_three_projections.BlockCount
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.ScalarCaps

/-!
# Scalar cell caps of a chart (one index `k`)

A scalar cell of a chart, a hidden bin and optionally an interval of the scalar
slope `-2p` determine a sheared physical box of volume `≲ D²σ²β`. Integrating
the original joint caps of the direction bin over fine cubes gives the pure and
angular Scalar ceilings `K⁴ σ² ρ^d (β) π(direction) D²` (paper, Proposition 9.7,
"The scalar projection: measure ceilings and support").
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Parent
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The joint cap of a fixed direction bin, in the form used for cell caps. -/
def DirectionCap (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (π : Measure ℝ)
    (K δc χ ρ d : ℝ) (β : ℤ) : Prop :=
  ∀ (w : Fin 3 → ℤ) (j' : ℤ),
    μ {p | (fun e => ⌊(![p.2, b p.1 0 + p.2 * b p.1 3, b p.1 1 + p.2 * b p.1 4] :
        Fin 3 → ℝ) e / δc⌋) = w ∧ ⌊(b p.1 2 + p.2 * b p.1 5) / ρ⌋ = j' ∧
        ⌊b p.1 3 / χ⌋ = β} ≤
      ENNReal.ofReal (K * δc ^ 3 * ρ ^ d) * π {x | ⌊x / χ⌋ = β}

/-- **Cell cap with an intercept slice.** An incidence set of one chart, one scalar
cell, one hidden bin of width `ρ`, and with first intercept in an interval of
half-width `Dβ'` about `pa`, has mass `≤ 3·10⁶ K⁴ σ² β' D² ρ^d π(direction)`. -/
theorem sliced_cell_cap {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ} (hb : Measurable b)
    {π : Measure ℝ} {K D χ ζ σ ρ δc d β' pa : ℝ} {P Q β : ℤ} {z : Fin 2 → ℤ} {j : ℤ}
    (hK : 1 ≤ K) (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hσ : 0 < σ) (hρ : 0 < ρ)
    (hδc : 0 < δc) (hδcσ : δc ≤ D * σ ^ 2)
    (hσβ : σ ≤ β') (hβ1 : β' ≤ 1) (hχσ : χ ≤ D * σ) (hζσ : ζ ≤ D * σ) (hζ : 0 ≤ ζ)
    (hpa : |2 * ((P : ℝ) * D) - pa| ≤ 3 * K)
    (hcap : DirectionCap μ b π K δc χ ρ d β)
    (E : Set (α × ℝ))
    (hE : ∀ p ∈ E, p.1 ∈ chartSet b K ζ D χ P Q β ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
      chartCell D σ P Q (b p.1) p.2 = z ∧ ⌊(b p.1 2 + p.2 * b p.1 5) / ρ⌋ = j ∧
      |b p.1 0 - pa| ≤ D * β') :
    μ E ≤ ENNReal.ofReal (3 * 10 ^ 6 * K ^ 4 * σ ^ 2 * β' * D ^ 2 * ρ ^ d) *
      π {x | ⌊x / χ⌋ = β} := by
  classical
  rcases E.eq_empty_or_nonempty with hE0 | ⟨p₀, hp₀⟩
  · rw [hE0, measure_empty]; exact bot_le
  have hK₀ : 0 ≤ K := by linarith
  -- the cell corner is a time in `[0, 1]`
  obtain ⟨hc₀, ht₀, hz₀, -, -⟩ := hE p₀ hp₀
  have hτ : (z 0 : ℝ) * σ ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨hτ₀, -, -, -⟩ := chartCell_corner hσ hz₀
    have hz0 : (0 : ℤ) ≤ z 0 := by
      have h0 : ⌊p₀.2 / σ⌋ = z 0 := by rw [← hz₀]; rfl
      rw [← h0]; exact Int.floor_nonneg.mpr (div_nonneg ht₀.1 hσ.le)
    have : (0 : ℝ) ≤ (z 0 : ℝ) := by exact_mod_cast hz0
    exact ⟨mul_nonneg this hσ.le, hτ₀.trans ht₀.2⟩
  obtain ⟨-, -, -, -, -, -, -, hβχ, -, -, -⟩ := chartSet_bounds hD hχ hc₀
  have hσ1 : σ ≤ 1 := hσβ.trans hβ1
  have hDσ1 : D * σ ≤ 1 := by
    calc D * σ ≤ 1 * 1 := mul_le_mul hD1 hσ1 hσ.le zero_le_one
      _ = 1 := by ring
  have hχ1 : χ ≤ 1 := hχσ.trans hDσ1
  have hvK : |(β : ℝ) * χ| ≤ 3 * K := by linarith
  -- restrict to the direction bin
  set Sβ : Set (α × ℝ) := {p | ⌊b p.1 3 / χ⌋ = β} with hSβ
  have hSβm : MeasurableSet Sβ := by
    have h3 : Measurable fun p : α × ℝ => b p.1 3 :=
      (measurable_pi_apply 3).comp (hb.comp measurable_fst)
    exact (Int.measurable_floor.comp (h3.div_const χ)) (measurableSet_singleton β)
  have hESβ : E ⊆ Sβ := fun p hp => (hE p hp).1.2.2.2.2.2
  have hμE : μ E = μ.restrict Sβ E := (Measure.restrict_eq_self μ hESβ).symm
  rw [hμE]
  have hmain := scalar_chart_cell_joint_cap (μ.restrict Sβ) (fun p => b p.1) (fun p => p.2)
    (fun p => (b p.1 2 + p.2 * b p.1 5) / ρ - j) E
    (δ := δc) (D := D) (σ := σ) (β := β') (χ := χ) (ζ := ζ) (H := 3 * K) (X := 1)
    (V := K * ρ ^ d) (pc := (P : ℝ) * D) (qc := (Q : ℝ) * D) (pa := pa)
    (r₀ := (z 1 : ℝ) * σ) (v := (β : ℝ) * χ) (τ := (z 0 : ℝ) * σ)
    hδc hD ?_ ?_ ?_ (by linarith) zero_le_one hpa hvK hτ ?_ (π {x | ⌊x / χ⌋ = β}) ?_
  · refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have hvol := scalar_cell_box_volume hD.le hσ.le hσβ hβ1 hχ.le hχσ hζ hζσ
    have hρd : 0 ≤ ρ ^ d := Real.rpow_nonneg hρ.le d
    calc 819 * (3 * K) ^ 3 * σ * (D * β' + χ) * (D * σ + σ * (D * β') + ζ + χ) *
          (2 * 1 + 5) * (K * ρ ^ d)
        = 819 * 27 * 7 * K ^ 4 * ρ ^ d *
          (σ * (D * β' + χ) * (D * σ + σ * (D * β') + ζ + χ)) := by ring
      _ ≤ 819 * 27 * 7 * K ^ 4 * ρ ^ d * (8 * D ^ 2 * σ ^ 2 * β') :=
          mul_le_mul_of_nonneg_left hvol (mul_nonneg (by positivity) hρd)
      _ = (819 * 27 * 7 * 8) * (K ^ 4 * σ ^ 2 * β' * D ^ 2 * ρ ^ d) := by ring
      _ ≤ (3 * 10 ^ 6) * (K ^ 4 * σ ^ 2 * β' * D ^ 2 * ρ ^ d) :=
          mul_le_mul_of_nonneg_right (by norm_num)
            (mul_nonneg (by have : 0 ≤ β' := hσ.le.trans hσβ; positivity) hρd)
      _ = 3 * 10 ^ 6 * K ^ 4 * σ ^ 2 * β' * D ^ 2 * ρ ^ d := by ring
  · -- `δc ≤ σ`
    have : D * σ ^ 2 ≤ σ := by
      have hσ1 : σ ≤ 1 := hσβ.trans hβ1
      calc D * σ ^ 2 ≤ 1 * σ ^ 2 := mul_le_mul_of_nonneg_right hD1 (sq_nonneg σ)
        _ = σ * σ := by ring
        _ ≤ σ * 1 := mul_le_mul_of_nonneg_left hσ1 hσ.le
        _ = σ := by ring
    linarith
  · -- `δc ≤ Dβ' + χ`
    have : D * σ ^ 2 ≤ D * β' := by
      have hσ1 : σ ≤ 1 := hσβ.trans hβ1
      have : σ ^ 2 ≤ β' := by nlinarith
      exact mul_le_mul_of_nonneg_left this hD.le
    linarith
  · -- `δc ≤ Dσ + σDβ' + ζ + χ`
    have : D * σ ^ 2 ≤ D * σ := by
      have hσ1 : σ ≤ 1 := hσβ.trans hβ1
      have : σ ^ 2 ≤ σ := by nlinarith
      exact mul_le_mul_of_nonneg_left this hD.le
    have h2 : 0 ≤ σ * (D * β') := by
      have : 0 ≤ β' := hσ.le.trans hσβ
      positivity
    linarith
  · -- the box conditions
    intro p hp
    obtain ⟨hc, ht, hz, hj, hpa'⟩ := hE p hp
    obtain ⟨-, -, -, -, -, hv, -, -, -, -, he⟩ := chartSet_bounds hD hχ hc
    obtain ⟨hτ₀, hτ₁, hR₀, hR₁⟩ := chartCell_corner hσ hz
    obtain ⟨hf₀, hf₁⟩ := floor_cell_mem (x := b p.1 2 + p.2 * b p.1 5) hρ
    rw [hj] at hf₀ hf₁
    refine ⟨ht, ?_, hpa', hv, he, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
    · have h0 : (j : ℝ) ≤ (b p.1 2 + p.2 * b p.1 5) / ρ := by
        rw [le_div_iff₀ hρ]; exact hf₀
      have h1 : (b p.1 2 + p.2 * b p.1 5) / ρ < j + 1 := by
        rw [div_lt_iff₀ hρ]; exact hf₁
      rw [abs_le]; constructor <;> linarith
  · -- transport the joint cap of the direction bin
    intro w j'
    have hset : {q : α × ℝ | (fun e => ⌊(![q.2, b q.1 0 + q.2 * b q.1 3,
        b q.1 1 + q.2 * b q.1 4] : Fin 3 → ℝ) e / δc⌋) = w ∧
        ⌊(b q.1 2 + q.2 * b q.1 5) / ρ - j⌋ = j'} =
        {q : α × ℝ | (fun e => ⌊(![q.2, b q.1 0 + q.2 * b q.1 3,
        b q.1 1 + q.2 * b q.1 4] : Fin 3 → ℝ) e / δc⌋) = w ∧
        ⌊(b q.1 2 + q.2 * b q.1 5) / ρ⌋ = j' + j} := by
      ext q
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [Int.floor_sub_intCast] at h2
        omega
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [Int.floor_sub_intCast]
        omega
    calc μ.restrict Sβ {q | (fun e => ⌊(![q.2, b q.1 0 + q.2 * b q.1 3,
          b q.1 1 + q.2 * b q.1 4] : Fin 3 → ℝ) e / δc⌋) = w ∧
          ⌊(b q.1 2 + q.2 * b q.1 5) / ρ - j⌋ = j'}
        ≤ μ ({q | (fun e => ⌊(![q.2, b q.1 0 + q.2 * b q.1 3,
          b q.1 1 + q.2 * b q.1 4] : Fin 3 → ℝ) e / δc⌋) = w ∧
          ⌊(b q.1 2 + q.2 * b q.1 5) / ρ⌋ = j' + j} ∩ Sβ) := by
          rw [hset, Measure.restrict_apply' hSβm]
      _ ≤ μ {q | (fun e => ⌊(![q.2, b q.1 0 + q.2 * b q.1 3,
          b q.1 1 + q.2 * b q.1 4] : Fin 3 → ℝ) e / δc⌋) = w ∧
          ⌊(b q.1 2 + q.2 * b q.1 5) / ρ⌋ = j' + j ∧ ⌊b q.1 3 / χ⌋ = β} := by
          apply measure_mono
          rintro q ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h2, h3⟩
      _ ≤ ENNReal.ofReal (K * δc ^ 3 * ρ ^ d) * π {x | ⌊x / χ⌋ = β} := hcap w (j' + j)
      _ = ENNReal.ofReal (K * ρ ^ d * δc ^ 3) * π {x | ⌊x / χ⌋ = β} := by
          rw [show K * δc ^ 3 * ρ ^ d = K * ρ ^ d * δc ^ 3 by ring]

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
