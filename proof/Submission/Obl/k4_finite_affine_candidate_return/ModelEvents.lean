-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/ModelEvents.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.EStages

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory MvPolynomial

noncomputable section

/-- Whole-time model fits form a closed set in coefficient space. -/
theorem isClosed_fitS (H a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (I : Set ℝ) :
    IsClosed {l : Fin 6 → ℝ | fitS id H a Q l I} := by
  have hc (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
      Continuous (fun l : Fin 6 → ℝ => eval (exS id l t) P) := by
    apply P.continuous_eval.comp
    apply continuous_pi
    intro e
    fin_cases e <;> simp only [exS, id_eq] <;> fun_prop
  have heq : {l : Fin 6 → ℝ | fitS id H a Q l I} =
      ⋂ t, ⋂ (_ : t ∈ I),
        {l | |eval (exS id l t) Q| ≤ H * a} ∩
        {l | |eval (exS id l t) (pderiv (3 : Fin 4) Q)| ≤ H} ∩
        {l | |eval (exS id l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ H / a} := by
    ext l
    simp only [fitS, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, and_assoc]
  rw [heq]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    ((isClosed_le (hc Q t).abs continuous_const).inter
      (isClosed_le (hc (pderiv (3 : Fin 4) Q) t).abs continuous_const)).inter
        (isClosed_le (hc (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q)) t).abs continuous_const)

/-- Measurability requires only measurable recorded coefficients. -/
theorem measurableSet_fitS {α : Type} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b)
    (H a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (I : Set ℝ) :
    MeasurableSet {l : α | fitS b H a Q l I} :=
  hb (isClosed_fitS H a Q I).measurableSet

/-- A quadratic model-candidate event is measurable. -/
theorem measurableSet_quadraticEvent {α : Type} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (B : Set α) (hB : MeasurableSet B)
    (T : ℕ) (j : Fin (2 ^ T)) (H a lower : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    MeasurableSet {p : α × ℝ | p.1 ∈ B ∧ p.2 ∈ IS T j ∧
      fitS b H a Q p.1 (IS T j) ∧
      lower ≤ |eval (exS b p.1 p.2) (pderiv (3 : Fin 4) Q)|} := by
  have hm : Measurable (fun p : α × ℝ =>
      eval (exS b p.1 p.2) (pderiv (3 : Fin 4) Q)) := by
    apply (pderiv (3 : Fin 4) Q).continuous_eval.measurable.comp
    apply Measurable.of_eval
    intro e
    fin_cases e <;> simp only [exS] <;> fun_prop
  exact (hB.preimage measurable_fst).inter
    ((measurableSet_Icc.preimage measurable_snd).inter
      (((measurableSet_fitS hb H a Q (IS T j)).preimage measurable_fst).inter
        (measurableSet_le measurable_const hm.abs)))

/-- A velocity-strip model-candidate event is measurable. -/
theorem measurableSet_stripEvent {α : Type} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (B : Set α) (hB : MeasurableSet B)
    (T : ℕ) (j : Fin (2 ^ T)) (z : Fin 2 → ℝ) (width : ℝ) :
    MeasurableSet {p : α × ℝ | p.1 ∈ B ∧ p.2 ∈ IS T j ∧
      |b p.1 4 - z 0 - z 1 * b p.1 3| ≤ width} := by
  apply (hB.preimage measurable_fst).inter
    ((measurableSet_Icc.preimage measurable_snd).inter ?_)
  have hm : Measurable (fun p : α × ℝ => |b p.1 4 - z 0 - z 1 * b p.1 3|) := by
    fun_prop
  exact measurableSet_le hm measurable_const

end

end Submission.Obl.k4_finite_affine_candidate_return
