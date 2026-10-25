import Submission.Obl.k4_scalar_conditional_crop_worlds.SignFormat
import Submission.Obl.k4_scalar_conditional_crop_worlds.Assembly
import Submission.Obl.k4_scalar_conditional_crop_worlds.Geometry
import Submission.Obl.k4_scalar_marked_packet_recovery.MarkedMeasure

open MeasureTheory Set MvPolynomial Finset

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- The crop event after the scalar affine normalization. -/
def normalizedMarkedEvent (H J : ℕ) (mark : Fin H → Fin J → Bool) : Set State :=
  {p | p ∈ MarkedEvent H J mark ∧ p.1.2 0 ∈ Ico (0 : ℝ) 1 ∧ p.1.2 1 ∈ Ico (0 : ℝ) 1}

lemma marked_section_boolFormat (H J : ℕ) (mark : Fin H → Fin J → Bool) (i : ℕ) :
    k4_dyadic_crop_worlds.BoolFormat (2 * (J : ℝ)) 1
      {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ MarkedEvent H J mark} := by
  classical
  let p : Fin (J + J) → MvPolynomial (Fin 6) ℝ := Fin.addCases
    (fun z : Fin J => X 5 - C ((z : ℝ) / (J : ℝ)))
    (fun z : Fin J => X 5 - C (((z : ℝ) + 1) / (J : ℝ)))
  let pred : (Fin (J + J) → Bool) → Bool := fun v => decide
    (∃ j : Fin H, i = j.val ∧ ∃ z : Fin J, mark j z = true ∧
      v (Fin.castAdd J z) = true ∧ v (Fin.natAdd J z) = false)
  refine ⟨J + J, by push_cast; linarith, p, ?_, pred, ?_⟩
  · intro j
    refine Fin.addCases (m := J) (n := J) (fun z => ?_) (fun z => ?_) j
    · simpa only [p, Fin.addCases_left] using
        (totalDegree_sub_C_le (X (5 : Fin 6) : MvPolynomial (Fin 6) ℝ) _).trans_eq (totalDegree_X 5)
    · simpa only [p, Fin.addCases_right] using
        (totalDegree_sub_C_le (X (5 : Fin 6) : MvPolynomial (Fin 6) ℝ) _).trans_eq (totalDegree_X 5)
  · intro b
    simp only [Set.mem_ofPred_eq, MarkedEvent, pred, decide_eq_true_eq, p,
      Fin.addCases_left, Fin.addCases_right, map_sub, eval_X, eval_C,
      decide_eq_false_iff_not, not_le, sub_nonneg, sub_neg, Set.mem_Ico]

lemma normalized_section_boolFormat (H J : ℕ) (mark : Fin H → Fin J → Bool) (i : ℕ) :
    k4_dyadic_crop_worlds.BoolFormat (8 + 2 * (J : ℝ)) 1
      {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ normalizedMarkedEvent H J mark} := by
  have hunit := k4_dyadic_crop_worlds.unitPlanar_format (n := 6) (![0, 1, 0, 1] : Fin 4 → Fin 6)
  have htime := marked_section_boolFormat H J mark i
  have h := hunit.inter htime
  have hset : {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ normalizedMarkedEvent H J mark} =
      k4_dyadic_crop_worlds.unitPlanar (![0, 1, 0, 1] : Fin 4 → Fin 6) ∩
      {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ MarkedEvent H J mark} := by
    ext b
    simp only [normalizedMarkedEvent, k4_dyadic_crop_worlds.unitPlanar, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.castSucc_zero, Fin.castSucc_one, Fin.isValue, Fin.forall_fin_zero, and_true]
    tauto
  rw [hset]
  simpa only [max_self] using h

lemma event_format_budget {N : ℝ} (hN : 2 ≤ N) (M : ℕ) {J : ℕ}
    (hJ : (J : ℝ) ≤ N ^ M) : 8 + 2 * (J : ℝ) ≤ N ^ (M + 4) := by
  have hNM : (1 : ℝ) ≤ N ^ M := one_le_pow₀ (by linarith)
  have hN4 : (16 : ℝ) ≤ N ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ N ^ 4 := pow_le_pow_left₀ (by norm_num) hN 4
  rw [pow_add]
  nlinarith

lemma normalizedMarkedEvent_data {N : ℝ} (hN : 2 ≤ N) (M H J : ℕ)
    (hH : (H : ℝ) ≤ N ^ M) (hJ : (J : ℝ) ≤ N ^ M) (hJ0 : 0 < J)
    (mark : Fin H → Fin J → Bool) : EventData (N ^ (M + 4)) 1 (normalizedMarkedEvent H J mark) := by
  have hunit : 1 ≤ N ^ (M + 4) := one_le_pow₀ (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmark := k4_scalar_marked_packet_recovery.measurableSet_markedEvent mark
    change MeasurableSet {p : State | p ∈ MarkedEvent H J mark ∧ _ ∧ _}
    exact hmark.inter ((measurableSet_Ico.preimage (by fun_prop)).inter
      (measurableSet_Ico.preimage (by fun_prop)))
  · intro p hp
    exact k4_scalar_marked_packet_recovery.markedEvent_subset_unit hJ0 mark hp.1
  · rintro p ⟨⟨j, hj, hz⟩, _⟩
    have hjH : (j.val : ℝ) ≤ H := by exact_mod_cast j.isLt.le
    have hpow : N ^ M ≤ N ^ (M + 4) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [hj]
    exact hjH.trans (hH.trans hpow)
  · intro i
    apply format_of_boolFormat hunit
    exact (normalized_section_boolFormat H J mark i).mono (event_format_budget hN M hJ) le_rfl

/-- A marked event only records the label and time, so its crop is exactly the normalized
unit square in the first two coefficients, with the same marks. -/
lemma conditionalEvent_marked_eq_normalized {N : ℝ} (hN : 0 < N) (u : ℝ)
    (H J : ℕ) (mark : Fin H → Fin J → Bool) (q : Label) :
    conditionalEvent N u (MarkedEvent H J mark) q = normalizedMarkedEvent H J mark := by
  ext p
  exact mem_cropEvent_iff hN q (MarkedEvent H J mark) p

lemma conditionalEvent_marked_data {N : ℝ} (hN : 2 ≤ N) (u : ℝ)
    (M H J : ℕ) (hH : (H : ℝ) ≤ N ^ M) (hJ : (J : ℝ) ≤ N ^ M) (hJ0 : 0 < J)
    (mark : Fin H → Fin J → Bool) (q : Label) :
    EventData (N ^ (M + 4)) 1 (conditionalEvent N u (MarkedEvent H J mark) q) := by
  rw [conditionalEvent_marked_eq_normalized (by linarith : 0 < N)]
  exact normalizedMarkedEvent_data hN M H J hH hJ hJ0 mark

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
