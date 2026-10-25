import Submission.Obl.k4_scalar_guarded_tangent_preparation.ReferenceLaws
import Submission.Obl.k4_scalar_guarded_tangent_preparation.ScalarCells
import Submission.Obl.k4_scalar_guarded_tangent_preparation.FixedVelocityPalette

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

open Submission.Obl.k4_scalar_linear_critical_extremizers

/-- The continuous pure ceiling reads out every base grid at a fixed
hidden depth. The original reference measure is unchanged. -/
theorem scalar_grid_pure_cap (σ : Measure Incidence) {N : ℝ} (hN : 0 < N)
    (B d r s : ℝ) (hB : 0 ≤ B)
    (hcap : σ.map (pureObservation N s) ≤
      ENNReal.ofReal (B * N ^ (-d * s)) •
        ((volume : Measure (Fin 2 → ℝ)).prod Measure.count))
    (q : Fin 2 → ℤ) (c : ℤ) :
    σ {z | baseBin N r z = q ∧ hiddenBin N s z = c} ≤
      ENNReal.ofReal (B * N ^ (-2 * r - d * s)) := by
  have ht : Measurable (fun z : Incidence => z.2) := measurable_snd
  have hl (i : Fin 5) : Measurable (fun z : Incidence => z.1.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hy : Measurable (fun z : Incidence => Split.y z.1 z.2) :=
    (hl 0).add (ht.mul (hl 1))
  have hY : Measurable (fun z : Incidence => (![z.2, Split.y z.1 z.2] : Fin 2 → ℝ)) := by
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact ht
    · exact hy
  have hX : Measurable (fun z : Incidence => Split.x z.1 z.2) :=
    ((hl 2).add (ht.mul (hl 3))).add ((ht.pow_const 2).mul (hl 4))
  have h := pure_cell_le (fun z : Incidence => ![z.2, Split.y z.1 z.2])
    (fun z => Split.x z.1 z.2) hY hX (Real.rpow_pos_of_pos hN (-r)) hcap q c
  rw [pure_cell_rpow hN B d r s hB] at h
  exact h

/-- The two requested grid depths may use different predictors from the
same coarse history. Likelihood caps use their original joint state. -/
theorem scalar_grid_joint_cap
    (σ ρ : Measure Incidence) [IsFiniteMeasure σ] (hm : σ univ ≠ 0) (hρ : ρ ≤ σ)
    {n : ℕ} (X : Incidence → Fin n) (hX : Measurable X)
    (Y : Fin n → ℕ) (Z : Fin n → ℤ) {N δ width R : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hwidth : 2 * δ ≤ width) (hR : 0 ≤ R)
    (hcode : ∀ᵐ z ∂σ, Z (X z) = (⌊z.1.2 1 / δ⌋ : ℤ))
    (hlikelihood : ∀ (e : ℕ) (z : ℤ),
      ρ.real {a | Y (X a) = e ∧ Z (X a) = z} * σ.real univ ≤
        R * σ.real {a | Y (X a) = e} * σ.real {a | Z (X a) = z})
    (B d r s : ℝ) (hB : 0 ≤ B)
    (hcap : σ.map (pureObservation N s) ≤
      ENNReal.ofReal (B * N ^ (-d * s)) •
        ((volume : Measure (Fin 2 → ℝ)).prod Measure.count))
    (qY : ℕ → Fin 2 → ℤ) (cY : ℕ → ℤ)
    (hqY : ∀ᵐ z ∂σ, baseBin N r z = qY (Y (X z)))
    (hcY : ∀ᵐ z ∂σ, hiddenBin N s z = cY (Y (X z)))
    (q : Fin 2 → ℤ) (c e : ℤ) :
    ρ {z | baseBin N r z = q ∧ hiddenBin N s z = c ∧ (⌊z.1.2 1 / width⌋ : ℤ) = e} ≤
      4 * (ENNReal.ofReal R * ENNReal.ofReal (B * N ^ (-2 * r - d * s))) *
        fixedVelocityPalette σ X Z δ {v | (⌊v / width⌋ : ℤ) = e} := by
  let P := {z : Incidence | baseBin N r z = q ∧ hiddenBin N s z = c}
  let Q := fun y => qY y = q ∧ cY y = c
  have hP : ∀ᵐ z ∂σ, z ∈ P ↔ Q (Y (X z)) := by
    filter_upwards [hqY, hcY] with z hzq hzc
    simp only [P, Q, Set.mem_ofPred_eq, hzq, hzc]
  have h := fixedVelocityPalette_joint_cap σ ρ hm hρ X hX Y Z (fun z => z.1.2 1)
    hδ hwidth hR hcode hlikelihood P Q hP e
  have hσ := scalar_grid_pure_cap σ hN B d r s hB hcap q c
  have hcell : {z | baseBin N r z = q ∧ hiddenBin N s z = c ∧ (⌊z.1.2 1 / width⌋ : ℤ) = e} =
      P ∩ {z | (⌊z.1.2 1 / width⌋ : ℤ) = e} := by
    ext z
    simp only [P, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [hcell]
  exact h.trans (mul_le_mul
    (mul_le_mul le_rfl (mul_le_mul le_rfl hσ bot_le bot_le) bot_le bot_le)
    le_rfl bot_le bot_le)

end Submission.Obl.k4_scalar_guarded_tangent_preparation
