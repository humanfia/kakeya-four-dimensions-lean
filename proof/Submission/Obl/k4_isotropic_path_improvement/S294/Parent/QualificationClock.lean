-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.QualificationClock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/QualificationClock.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Cartesian.QualWitness
import Submission.Lib.K4PolynomialNorming.PolynomialRemezCoefficients

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set Polynomial

noncomputable section

namespace QualificationClock

/-- Write an original-time polynomial in normalized block time. -/
def retime (t₀ h : ℝ) (Q : Polynomial ℝ) : Polynomial ℝ :=
  Q.comp (C t₀ + C h * X)

@[simp] theorem eval_retime (t₀ h : ℝ) (Q : Polynomial ℝ) (s : ℝ) :
    (retime t₀ h Q).eval s = Q.eval (t₀ + h * s) := by
  simp [retime]

theorem degree_retime (t₀ : ℝ) {h : ℝ} (hh : h ≠ 0)
    {Q : Polynomial ℝ} {M : ℕ} (hQ : Q.natDegree ≤ M) :
    (retime t₀ h Q).natDegree ≤ M := by
  have ha : (C t₀ + C h * X).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    simp [natDegree_C, natDegree_C_mul_X h hh]
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hQ ha).trans_eq (Nat.mul_one M))

theorem eval_bound {Q : Polynomial ℝ} {M : ℕ} {K : ℝ}
    (hQ : Q.natDegree ≤ M) (hK : 0 ≤ K) (hc : ∀ n, |Q.coeff n| ≤ K)
    {t : ℝ} (ht : |t| ≤ 2) : |Q.eval t| ≤ (M + 1 : ℕ) * K * 2 ^ M := by
  rw [eval_eq_sum_range' (Nat.lt_succ_iff.mpr hQ)]
  calc
    _ ≤ ∑ n ∈ Finset.range (M + 1), |Q.coeff n * t ^ n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (M + 1), K * 2 ^ M := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hc n)
        ((pow_le_pow_left₀ (abs_nonneg _) ht _).trans
          (pow_le_pow_right₀ (by norm_num) hnM)) (by positivity) hK
    _ = _ := by simp; ring

/-- A constant depending only on degree pays for changing the clock. -/
def coefficientCost (M : ℕ) : ℝ :=
  (1 + 8 * (M + 1 : ℕ)) ^ M * ((M + 1 : ℕ) * 2 ^ M)

theorem coefficientCost_pos (M : ℕ) : 0 < coefficientCost M := by
  unfold coefficientCost
  positivity

theorem coeff_retime {Q : Polynomial ℝ} {M : ℕ} {K t₀ h : ℝ}
    (hQ : Q.natDegree ≤ M) (hK : 0 ≤ K) (hc : ∀ n, |Q.coeff n| ≤ K)
    (ht₀ : 0 ≤ t₀) (ht₀1 : t₀ ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ) :
    |(retime t₀ h Q).coeff n| ≤ coefficientCost M * K := by
  have hvalues : ∀ s ∈ Icc (0 : ℝ) 1,
      |(retime t₀ h Q).eval s| ≤ (M + 1 : ℕ) * K * 2 ^ M := by
    intro s hs
    rw [eval_retime]
    apply eval_bound hQ hK hc
    rw [abs_of_nonneg (add_nonneg ht₀ (mul_nonneg hh.le hs.1))]
    nlinarith [mul_le_mul hh1 hs.2 hs.1 (by norm_num : (0 : ℝ) ≤ 1)]
  have hc' := Submission.Lib.K4PolynomialNorming.real_polynomial_coeff_le_of_small_values
    (retime t₀ h Q) M (degree_retime t₀ hh.ne' hQ) (Icc 0 1) 1 1
    ((M + 1 : ℕ) * K * 2 ^ M) (by norm_num) (by norm_num) (by positivity)
    (by simp) (fun s hs => by simpa only [abs_of_nonneg hs.1] using hs.2) hvalues n
  convert hc' using 1 <;> simp only [coefficientCost, div_one] <;> ring

/-- Normalized duration uses the same original measurable times and the
exact factor inverse block length. -/
theorem volume_retime (t₀ : ℝ) {h : ℝ} (hh : 0 < h) (R : Set ℝ) :
    volume ((fun s => t₀ + h * s) ⁻¹' R) = ENNReal.ofReal h⁻¹ * volume R := by
  have heq : (fun s => t₀ + h * s) ⁻¹' R =
      (fun s => h * s) ⁻¹' ((fun t => t₀ + t) ⁻¹' R) := rfl
  rw [heq, Real.volume_preimage_mul_left hh.ne',
    MeasureTheory.measure_preimage_add, abs_of_pos (inv_pos.mpr hh)]

/-- A native qualification becomes a Cartesian witness in the same
original block. Only the clock and a degree-dependent coefficient factor
change; the reference incidence set and indexed trajectory stay fixed. -/
theorem qualWitness_of_native {Λ σ ι : Type*} [MeasurableSpace Λ]
    (Eref : Set (Λ × ℝ)) (hE : MeasurableSet Eref)
    (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st)) (lab : Λ × ℝ → ι)
    {M T : ℕ} {K err dur t₀ h : ℝ} (hK : 0 ≤ K)
    (ht₀ : 0 ≤ t₀) (ht₀1 : t₀ ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hblock : Eref ⊆ univ ×ˢ Icc t₀ (t₀ + h))
    {w : Λ × ℝ}
    (hq : Qualification.Jets2.NativeQualified Eref lab (Gs ∘ st) M T K err dur w) :
    Cartesian.QualWitness Eref st Gs t₀ h M (coefficientCost M * K) err (dur / h) w := by
  rcases hq with ⟨Q, hdeg, hcoeff, hpoint, hmass⟩
  let R : Set ℝ := {t | (w.1, t) ∈ Eref ∧
    ∀ j, |Gs (st (w.1, t)) j - (Q j).eval t| ≤ err}
  have hRm : MeasurableSet R := by
    apply (hE.preimage (measurable_const.prodMk measurable_id)).inter
    have hm : Measurable (fun t : ℝ => (w.1, t)) := measurable_const.prodMk measurable_id
    have hfit j : MeasurableSet {t : ℝ |
        |Gs (st (w.1, t)) j - (Q j).eval t| ≤ err} :=
      measurableSet_le (((measurable_pi_apply j).comp
        (hG.comp hm)).sub (Q j).continuous.measurable).abs measurable_const
    exact (MeasurableSet.iInter hfit).congr (by
      ext t
      simp only [mem_iInter, mem_setOf_eq]
      rfl)
  have hRmass : ENNReal.ofReal dur ≤ volume R := hmass.trans (measure_mono (by
    intro t ht
    exact ⟨ht.2.1, ht.2.2.2⟩))
  let E := (fun s => t₀ + h * s) ⁻¹' R
  refine ⟨fun j => retime t₀ h (Q j), fun j => degree_retime t₀ hh.ne' (hdeg j),
    fun j n => coeff_retime (hdeg j) hK (hcoeff j) ht₀ ht₀1 hh hh1 n, ?_,
    E, hRm.preimage (by fun_prop), ?_, ?_, ?_⟩
  · intro j
    simpa only [Function.comp_apply, eval_retime,
      show t₀ + h * ((w.2 - t₀) / h) = w.2 by field_simp; ring]
      using hpoint j
  · intro s hs
    have hb := (hblock hs.1).2
    change t₀ ≤ t₀ + h * s ∧ t₀ + h * s ≤ t₀ + h at hb
    constructor <;> nlinarith
  · rw [show volume E = ENNReal.ofReal h⁻¹ * volume R from volume_retime t₀ hh R,
      ENNReal.ofReal_div_of_pos hh, div_eq_mul_inv,
      ← ENNReal.ofReal_inv_of_pos hh, mul_comm]
    exact mul_le_mul' le_rfl hRmass
  · intro s hs
    exact ⟨hs.1, fun j => by simpa only [eval_retime] using hs.2 j⟩

end QualificationClock

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
