/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ParameterCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.ReconstructionMesh
import Submission.Obl.k4_horizontal_strict_parameter_step.MovingGraphCaps
import Submission.Lib.K4MovingMeshBoxes.Projection

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

/-- Reconstructed parameters at the corner of a physical mesh cell. -/
def cellParameters (δ v : ℝ) (q : Fin 3 → ℤ) : Fin 3 → ℝ :=
  let τ := δ * (q 0 : ℝ)
  let p := δ * (q 1 : ℝ) - τ * v
  ![τ, p, δ * (q 2 : ℝ) + τ * p]

theorem meshParameters_eq_cellParameters (b : Fin 6 → ℝ) (δ v t : ℝ) :
    meshParameters b δ v t = cellParameters δ v (baseMesh δ (basePoint b t)) := by
  ext i
  fin_cases i <;> rfl

/-- A static parameter square moves through a physical box of the expected area,
up to the original contact and velocity-bin errors. -/
theorem static_square_mem_movingBox {b : Fin 6 → ℝ} {t time radius p₀ q₀ v w χ : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (htime : |t - time| ≤ radius)
    (hp : |b 0 - p₀| ≤ w) (hq : |b 1 - q₀| ≤ w)
    (hvel : |b 3 - v| ≤ χ) (hcontact : |b 4 + b 0| ≤ χ) :
    basePoint b t ∈ movingBox time radius ![p₀, q₀] ![v, -p₀] ![w + χ, 2 * w + χ] := by
  refine ⟨htime, ?_⟩
  intro i
  fin_cases i
  · change |b 0 + t * b 3 - (p₀ + t * v)| ≤ w + χ
    have heq : b 0 + t * b 3 - (p₀ + t * v) = b 0 - p₀ + t * (b 3 - v) := by ring
    rw [heq]
    calc
      _ ≤ |b 0 - p₀| + |t * (b 3 - v)| := abs_add_le _ _
      _ ≤ w + 1 * χ := add_le_add hp (by
        rw [abs_mul]
        exact mul_le_mul (by simpa only [abs_of_nonneg ht.1] using ht.2) hvel (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  · change |b 1 + t * b 4 - (q₀ + t * (-p₀))| ≤ 2 * w + χ
    have heq : b 1 + t * b 4 - (q₀ + t * (-p₀)) =
        (b 1 - q₀) + t * (b 4 + b 0) - t * (b 0 - p₀) := by ring
    rw [heq, sub_eq_add_neg]
    calc
      _ ≤ |b 1 - q₀| + |t * (b 4 + b 0)| + |-(t * (b 0 - p₀))| := abs_add_three _ _ _
      _ ≤ w + 1 * χ + 1 * w := by
        rw [abs_neg, abs_mul, abs_mul]
        exact add_le_add (add_le_add hq
          (mul_le_mul (by simpa only [abs_of_nonneg ht.1] using ht.2) hcontact (abs_nonneg _) (by norm_num)))
          (mul_le_mul (by simpa only [abs_of_nonneg ht.1] using ht.2) hp (abs_nonneg _) (by norm_num))
      _ = _ := by ring

/-- Integrating the original joint caps around a full-time predictor on a static parameter
square. The prior and the velocity condition are retained verbatim. -/
theorem integrated_parameter_graph_cap {α : Type} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (h : Fin 6 → ℝ)
    (condition : α × ℝ → Prop)
    {δ a radius L C χ K M D : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hdr : δ ≤ radius) (hL : 0 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 < D)
    (time p₀ q₀ v w offset : ℝ)
    (hvK : |v| ≤ K) (hvL : |v| ≤ L) (hpL : |p₀| ≤ L)
    (hdw : δ ≤ w + χ ∧ δ ≤ 2 * w + χ)
    (hmove : L * δ ≤ w + χ ∧ L * δ ≤ 2 * w + χ)
    (hcondition : ∀ p, condition p → p.2 ∈ Icc (0 : ℝ) 1 ∧
      |b p.1 3 - v| ≤ χ ∧ |b p.1 4 + b p.1 0| ≤ χ ∧ |b p.1 0| ≤ K ∧
      |predictorTimeSlope h (b p.1 0) (b p.1 1)| ≤ 2 * M)
    (hgrad : ∀ τ ∈ Icc (0 : ℝ) 1,
      |h 2 + h 3 * τ| ≤ 2 * M / D ∧ |h 4 + h 5 * τ| ≤ 2 * M / D)
    (hround : 2 * M * δ + (6 * M / D) * (χ + (K + 1) * δ) ≤ a)
    (hcell : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh δ (basePoint (b p.1) p.2) = q ∧
        ⌊(b p.1 2 + p.2 * b p.1 5) / a⌋ = j ∧ condition p} ≤ ENNReal.ofReal (C * δ ^ 3)) :
    μ {p | |p.2 - time| ≤ radius ∧ |b p.1 0 - p₀| ≤ w ∧ |b p.1 1 - q₀| ≤ w ∧
      |b p.1 2 + p.2 * b p.1 5 - (predictor h p.2 (b p.1 0) (b p.1 1) + offset)| ≤ a ∧ condition p} ≤
      ENNReal.ofReal (4200 * C * radius * (w + χ) * (2 * w + χ)) := by
  let z := fun p : α × ℝ => basePoint (b p.1) p.2
  let x := fun p : α × ℝ => b p.1 2 + p.2 * b p.1 5
  let H := fun p : α × ℝ => predictor h p.2 (b p.1 0) (b p.1 1) + offset
  let g := fun q => predictor h (cellParameters δ v q 0) (cellParameters δ v q 1)
    (cellParameters δ v q 2) + offset
  have happrox : ∀ p, z p ∈ movingBox time radius ![p₀, q₀] ![v, -p₀] ![w + χ, 2 * w + χ] →
      condition p → |H p - g (baseMesh δ (z p))| ≤ a := by
    intro p hp hc
    obtain ⟨ht, hvel, hcontact, hpos, hslope⟩ := hcondition p hc
    have hrec := (predictor_reconstruction_error hδ ht hvel hcontact hpos hvK hM hD hslope hgrad).trans hround
    rw [meshParameters_eq_cellParameters] at hrec
    convert hrec using 1 <;> dsimp [H, g, z] <;> congr 1 <;> ring
  have hb := moving_graph_cap μ z x H condition hδ ha hdr hL hC time
    ![p₀, q₀] ![v, -p₀] ![w + χ, 2 * w + χ]
    (by intro i; fin_cases i; exact hvL; change |-p₀| ≤ L; simpa only [abs_neg] using hpL)
    (by intro i; fin_cases i; exact hdw.1; exact hdw.2)
    (by intro i; fin_cases i; exact hmove.1; exact hmove.2) g happrox hcell
  apply le_trans (measure_mono ?_) hb
  rintro p ⟨htime, hp, hq, hfit, hc⟩
  exact ⟨static_square_mem_movingBox (hcondition p hc).1 htime hp hq
    (hcondition p hc).2.1 (hcondition p hc).2.2.1, hfit, hc⟩

end

end Submission.Obl.k4_horizontal_strict_parameter_step
