import Submission.Obl.k4_coarsened_outer_horizon_composition.Observations
import Submission.Obl.k4_multilinear_kakeya.Plane

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal

noncomputable def baseCross (κ t₀ t₁ : ℝ) (c u : E2)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Set E3 :=
  {z | z 0 ∈ Icc t₀ t₁ ∧
    ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - (z 0) • u)‖ ≤ κ}

lemma measurableSet_baseCross (κ t₀ t₁ : ℝ) (c u : E2)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : MeasurableSet (baseCross κ t₀ t₁ c u Q) := by
  have ht : MeasurableSet {z : E3 | z 0 ∈ Icc t₀ t₁} :=
    measurableSet_Icc.preimage (by fun_prop)
  have hs : Measurable (fun z : E3 =>
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - (z 0) • u)‖) := by fun_prop
  exact ht.inter (measurableSet_le hs measurable_const)

/-- The base of a chart has reference volume bounded by its true-floor Jacobian. -/
theorem volume_baseCross {κ t₀ t₁ : ℝ} (hκ : 0 ≤ κ) (ht : t₀ ≤ t₁)
    (c u : E2) (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) :
    volume (baseCross κ t₀ t₁ c u Q) ≤ ENNReal.ofReal (4 * κ ^ 2 * (t₁ - t₀) * |Q.det|) := by
  let qu : E2 := Matrix.toEuclideanLin Q⁻¹ u
  let qc : E2 := Matrix.toEuclideanLin Q⁻¹ c
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    !![1, 0, 0; -qu 0, Q⁻¹ 0 0, Q⁻¹ 0 1; -qu 1, Q⁻¹ 1 0, Q⁻¹ 1 1]
  let box : Set (Fin 3 → ℝ) := Icc ![t₀, qc 0 - κ, qc 1 - κ] ![t₁, qc 0 + κ, qc 1 + κ]
  have hdet : A.det = Q.det⁻¹ := by
    calc
      A.det = (Q⁻¹).det := by
        rw [Matrix.det_fin_two]
        norm_num [A, Matrix.det_fin_three, Matrix.vecHead, Matrix.vecTail, Function.comp_def]
      _ = _ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hdetA : A.det ≠ 0 := by rw [hdet]; exact inv_ne_zero hQ
  have hcoords (z : E3) (e : Fin 2) :
      (A.mulVec (WithLp.ofLp z)) e.succ = qc e +
        (Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - (z 0) • u)) e := by
    fin_cases e <;>
      simp [A, qc, qu, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring
  have hsub : baseCross κ t₀ t₁ c u Q ⊆
      (fun z : E3 => A.mulVec (WithLp.ofLp z)) ⁻¹' box := by
    intro z hz
    change (t₀ ≤ z 0 ∧ z 0 ≤ t₁) ∧ _ at hz
    have hcoord (e : Fin 2) :
        qc e - κ ≤ (A.mulVec (WithLp.ofLp z)) e.succ ∧
          (A.mulVec (WithLp.ofLp z)) e.succ ≤ qc e + κ := by
      have hnorm : |(Matrix.toEuclideanLin Q⁻¹
          (WithLp.toLp 2 ![z 1, z 2] - c - (z 0) • u)) e| ≤ κ :=
        (PiLp.norm_apply_le _ e).trans hz.2
      rw [hcoords]
      exact ⟨by linarith [(abs_le.mp hnorm).1], by linarith [(abs_le.mp hnorm).2]⟩
    constructor <;> intro e <;> fin_cases e
    · simpa [A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hz.1.1
    · exact (hcoord 0).1
    · exact (hcoord 1).1
    · simpa [A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hz.1.2
    · exact (hcoord 0).2
    · exact (hcoord 1).2
  have hvolbox : volume box = ENNReal.ofReal ((t₁ - t₀) * (2 * κ) * (2 * κ)) := by
    rw [Real.volume_Icc_pi, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_def, Fin.succ_zero_eq_one]
    have hs (v : ℝ) : v + κ - (v - κ) = 2 * κ := by ring
    rw [hs, hs, ← ENNReal.ofReal_mul (sub_nonneg.mpr ht),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (t₁ - t₀) * (2 * κ))]
  calc
    _ ≤ volume ((fun z : E3 => A.mulVec (WithLp.ofLp z)) ⁻¹' box) := measure_mono hsub
    _ = ENNReal.ofReal |A.det⁻¹| * volume box :=
      Submission.Obl.k4_multilinear_kakeya.matrix_preimage_volume A hdetA measurableSet_Icc
    _ = _ := by
      rw [hdet, inv_inv, hvolbox, ← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      ring

end Submission.Obl.k4_coarsened_outer_horizon_composition
