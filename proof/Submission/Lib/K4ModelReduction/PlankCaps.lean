import Submission.Lib.K4ModelReduction.ProjectionSmoothing

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Full-time projected plank caps from the original full-slope density ceiling. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Set
open scoped ENNReal

theorem exists_planar_orthonormalBasis (e₁ e₂ : EuclideanSpace ℝ (Fin 2))
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he : inner ℝ e₁ e₂ = 0) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)), b 0 = e₁ ∧ b 1 = e₂ := by
  have hon : Orthonormal ℝ ![e₁, e₂] := by
    constructor
    · intro i
      fin_cases i <;> assumption
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact he
      · simpa [real_inner_comm] using he
      · exact False.elim (hij rfl)
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)
  refine ⟨OrthonormalBasis.mk hon hspan.ge, ?_, ?_⟩ <;> simp

theorem orthonormal_rectangle_volume
    (b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (w : EuclideanSpace ℝ (Fin 2)) {a β : ℝ} (ha : 0 ≤ a) (_hβ : 0 ≤ β) :
    volume {v : EuclideanSpace ℝ (Fin 2) |
      |inner ℝ (v - w) (b 0)| ≤ a ∧ |inner ℝ (v - w) (b 1)| ≤ β} =
      ENNReal.ofReal (4 * a * β) := by
  let F : EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ) := fun v => (b.repr (v - w)).ofLp
  have hF : MeasurePreserving F volume volume := by
    have h := (PiLp.volume_preserving_ofLp (Fin 2)).comp
      (b.measurePreserving_repr.comp (measurePreserving_add_right volume (-w)))
    convert h using 1
    funext v
    simp only [F, Function.comp_def, sub_eq_add_neg]
  have hset : {v : EuclideanSpace ℝ (Fin 2) |
      |inner ℝ (v - w) (b 0)| ≤ a ∧ |inner ℝ (v - w) (b 1)| ≤ β} =
      F ⁻¹' Icc ![-a, -β] ![a, β] := by
    ext v
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, F, OrthonormalBasis.repr_apply_apply,
      abs_le, real_inner_comm]
    tauto
  rw [hset, hF.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi,
    Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add, ← two_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem planar_rectangle_volume (w e₁ e₂ : EuclideanSpace ℝ (Fin 2))
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he : inner ℝ e₁ e₂ = 0)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) :
    volume {v : EuclideanSpace ℝ (Fin 2) |
      |inner ℝ (v - w) e₁| ≤ a ∧ |inner ℝ (v - w) e₂| ≤ β} =
      ENNReal.ofReal (4 * a * β) := by
  obtain ⟨b, hb₀, hb₁⟩ := exists_planar_orthonormalBasis e₁ e₂ he₁ he₂ he
  simpa only [hb₀, hb₁] using orthonormal_rectangle_volume b w ha hβ

theorem slope_rectangle_cylinder_volume (w e₁ e₂ : EuclideanSpace ℝ (Fin 2))
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he : inner ℝ e₁ e₂ = 0)
    {R a β : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (hβ : 0 ≤ β) :
    volume {s : EuclideanSpace ℝ (Fin 3) | |s 2| ≤ R ∧
      |inner ℝ (baseProjection s - w) e₁| ≤ a ∧
      |inner ℝ (baseProjection s - w) e₂| ≤ β} = ENNReal.ofReal (8 * R * a * β) := by
  let T : Set (EuclideanSpace ℝ (Fin 2)) :=
    {v | |inner ℝ (v - w) e₁| ≤ a ∧ |inner ℝ (v - w) e₂| ≤ β}
  have hT : MeasurableSet T := by
    unfold T
    measurability
  have hset : {s : EuclideanSpace ℝ (Fin 3) | |s 2| ≤ R ∧
      |inner ℝ (baseProjection s - w) e₁| ≤ a ∧
      |inner ℝ (baseProjection s - w) e₂| ≤ β} =
      {s | s 2 ∈ Icc (0 - R) (0 + R) ∧ baseProjection s ∈ T} := by
    ext s
    simp only [mem_ofPred_eq, T, mem_Icc, zero_sub, zero_add, abs_le]
  rw [hset, base_cylinder_volume 0 R T hT,
    planar_rectangle_volume w e₁ e₂ he₁ he₂ he ha hβ,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem baseProjection_add_smul (b s : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    baseProjection (b + t • s) = baseProjection b + t • baseProjection s := by
  ext i
  rfl

theorem velocity_inner_le_of_full_time
    (b v c w e : EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |inner ℝ (b + t • v - c - t • w) e| ≤ a) :
    |inner ℝ (v - w) e| ≤ 2 * a := by
  have h₀ := h 0 (by simp)
  have h₁ := h 1 (by simp)
  simp only [zero_smul, add_zero, sub_zero] at h₀
  simp only [one_smul] at h₁
  have heq : v - w = (b + v - c - w) - (b - c) := by abel
  rw [heq, inner_sub_left]
  exact (abs_sub _ _).trans (by linarith)

/-- A full three-slope density ceiling and a bounded hidden slope give
the full-time projected plank cap. The event and its slope image need
not be assumed measurable: all comparisons are outer-measure comparisons. -/
theorem projected_full_time_plank_cap {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (b s : X → EuclideanSpace ℝ (Fin 3)) {Λ R : ℝ}
    (hΛ : 0 ≤ Λ) (hR : 0 ≤ R)
    (hdom : ∀ Z : Set (EuclideanSpace ℝ (Fin 3)),
      μ {l | s l ∈ Z} ≤ ENNReal.ofReal Λ * volume Z)
    (hhidden : ∀ᵐ l ∂μ, |s l 2| ≤ R)
    (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2))
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he : inner ℝ e₁ e₂ = 0)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) :
    μ {l | ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (baseProjection (b l + t • s l) - c - t • w) e₁| ≤ a ∧
      |inner ℝ (baseProjection (b l + t • s l) - c - t • w) e₂| ≤ β} ≤
        ENNReal.ofReal (32 * Λ * R * a * β) := by
  let F : Set X := {l | ∀ t ∈ Icc (0 : ℝ) 1,
    |inner ℝ (baseProjection (b l + t • s l) - c - t • w) e₁| ≤ a ∧
    |inner ℝ (baseProjection (b l + t • s l) - c - t • w) e₂| ≤ β}
  let Z : Set (EuclideanSpace ℝ (Fin 3)) := {v | |v 2| ≤ R ∧
    |inner ℝ (baseProjection v - w) e₁| ≤ 2 * a ∧
    |inner ℝ (baseProjection v - w) e₂| ≤ 2 * β}
  have hsubset : ∀ᵐ l ∂μ, l ∈ F → s l ∈ Z := by
    filter_upwards [hhidden] with l hl
    intro hfull
    refine ⟨hl, ?_, ?_⟩
    · apply velocity_inner_le_of_full_time (baseProjection (b l)) (baseProjection (s l)) c w e₁ a
      intro t ht
      simpa only [baseProjection_add_smul] using (hfull t ht).1
    · apply velocity_inner_le_of_full_time (baseProjection (b l)) (baseProjection (s l)) c w e₂ β
      intro t ht
      simpa only [baseProjection_add_smul] using (hfull t ht).2
  have hvol : volume Z = ENNReal.ofReal (32 * R * a * β) := by
    calc
      _ = ENNReal.ofReal (8 * R * (2 * a) * (2 * β)) :=
        slope_rectangle_cylinder_volume w e₁ e₂ he₁ he₂ he hR (by positivity) (by positivity)
      _ = _ := by congr 1; ring
  calc
    _ = μ F := rfl
    _ ≤ μ {l | s l ∈ Z} := measure_mono_ae hsubset
    _ ≤ ENNReal.ofReal Λ * volume Z := hdom Z
    _ = _ := by
      rw [hvol, ← ENNReal.ofReal_mul hΛ]
      congr 1
      ring

end Submission.Lib.K4ModelReduction
