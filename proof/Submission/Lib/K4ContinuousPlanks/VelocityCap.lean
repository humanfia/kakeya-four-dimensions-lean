/-
Adapted from: here:o018
-/
import Submission.Lib.K4ContinuousPlanks.Continuous

/-! A velocity-marginal ceiling implies the full-time plank cap used above. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4ContinuousPlanks

theorem exists_planar_orthonormalBasis (e₁ e₂ : EuclideanSpace ℝ (Fin 2))
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he : inner ℝ e₁ e₂ = 0) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      b 0 = e₁ ∧ b 1 = e₂ := by
  have hon : Orthonormal ℝ (![e₁, e₂] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    constructor
    · intro i
      fin_cases i <;> simp [he₁, he₂]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [real_inner_comm]
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)
  let b := OrthonormalBasis.mk hon (by rw [hspan])
  exact ⟨b, by simp [b], by simp [b]⟩

theorem volume_planar_basis_box
    (b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (c : EuclideanSpace ℝ (Fin 2)) (r : Fin 2 → ℝ) :
    volume {x | ∀ i, |inner ℝ (x - c) (b i)| ≤ r i} =
      ∏ i, ENNReal.ofReal (2 * r i) := by
  let T : EuclideanSpace ℝ (Fin 2) → Fin 2 → ℝ := fun x => (b.repr (x - c)).ofLp
  have hT : MeasurePreserving T volume volume := by
    exact (PiLp.volume_preserving_ofLp (Fin 2)).comp
      (b.measurePreserving_repr.comp (measurePreserving_add_right volume (-c)))
  have hcoord (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
      T x i = inner ℝ (x - c) (b i) := by
    simp only [T, OrthonormalBasis.repr_apply_apply, real_inner_comm]
  have heq : {x | ∀ i, |inner ℝ (x - c) (b i)| ≤ r i} = T ⁻¹' Icc (-r) r := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def, Pi.neg_apply, hcoord, abs_le,
      forall_and]
  rw [heq]
  have hm := congrArg (fun μ : Measure (Fin 2 → ℝ) => μ (Icc (-r) r)) hT.map_eq
  rw [Measure.map_apply hT.measurable measurableSet_Icc] at hm
  rw [hm, Real.volume_Icc_pi]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simp only [Pi.neg_apply]
  ring

theorem volume_planar_rectangle (c e₁ e₂ : EuclideanSpace ℝ (Fin 2))
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he : inner ℝ e₁ e₂ = 0)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) :
    volume {x | |inner ℝ (x - c) e₁| ≤ a ∧ |inner ℝ (x - c) e₂| ≤ β} =
      ENNReal.ofReal (4 * a * β) := by
  obtain ⟨b, hb₀, hb₁⟩ := exists_planar_orthonormalBasis e₁ e₂ he₁ he₂ he
  have heq : {x | |inner ℝ (x - c) e₁| ≤ a ∧ |inner ℝ (x - c) e₂| ≤ β} =
      {x | ∀ i : Fin 2, |inner ℝ (x - c) (b i)| ≤ (![a, β] : Fin 2 → ℝ) i} := by
    ext x
    simp only [mem_ofPred_eq, Fin.forall_fin_two, hb₀, hb₁, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [heq, volume_planar_basis_box]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * a)]
  congr 1
  ring

theorem velocity_strip_of_endpoints (b u c w e : EuclideanSpace ℝ (Fin 2)) {a : ℝ}
    (h₀ : |inner ℝ (b + (0 : ℝ) • u - c - (0 : ℝ) • w) e| ≤ a)
    (h₁ : |inner ℝ (b + (1 : ℝ) • u - c - (1 : ℝ) • w) e| ≤ a) :
    |inner ℝ (u - w) e| ≤ 2 * a := by
  have heq : inner ℝ (u - w) e =
      inner ℝ (b + (1 : ℝ) • u - c - (1 : ℝ) • w) e -
        inner ℝ (b + (0 : ℝ) • u - c - (0 : ℝ) • w) e := by
    simp only [zero_smul, one_smul, add_zero, sub_zero, inner_sub_left, inner_add_left]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

/-- Endpoints confine the velocity to a rectangle of twice the spatial radii.
The original prior, without incidence normalization, therefore has a full-time cap. -/
theorem measureFullPlankCap_of_velocity_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (b u : α → EuclideanSpace ℝ (Fin 2))
    (K : ℝ) (hK : 0 ≤ K)
    (hvel : ∀ Z : Set (EuclideanSpace ℝ (Fin 2)),
      μ (u ⁻¹' Z) ≤ ENNReal.ofReal K * volume Z) :
    MeasureFullPlankCap μ b u (16 * K) := by
  intro c w e₁ e₂ a β he₁ he₂ he ha hab
  let Z := {v : EuclideanSpace ℝ (Fin 2) |
    |inner ℝ (v - w) e₁| ≤ 2 * a ∧ |inner ℝ (v - w) e₂| ≤ 2 * β}
  have hsub : {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} ⊆ u ⁻¹' Z := by
    intro x hx
    have h₀ := hx 0 (by simp)
    have h₁ := hx 1 (by simp)
    exact ⟨velocity_strip_of_endpoints (b x) (u x) c w e₁ h₀.1 h₁.1,
      velocity_strip_of_endpoints (b x) (u x) c w e₂ h₀.2 h₁.2⟩
  calc
    _ ≤ μ (u ⁻¹' Z) := measure_mono hsub
    _ ≤ ENNReal.ofReal K * volume Z := hvel Z
    _ = _ := by
      rw [volume_planar_rectangle w e₁ e₂ he₁ he₂ he (by positivity) (by linarith),
        ← ENNReal.ofReal_mul hK]
      congr 1
      ring

end Submission.Lib.K4ContinuousPlanks
