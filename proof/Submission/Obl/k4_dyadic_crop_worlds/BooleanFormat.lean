import Submission.Obl.k4_dyadic_crop_worlds.Definitions
import Submission.Obl.k4_eligibility_sign_description.Families

namespace Submission.Obl.k4_dyadic_crop_worlds

open MeasureTheory Set MvPolynomial
noncomputable section

lemma BoolFormat.mono {n D D' : ℕ} {R R' : ℝ} {S : Set (Fin n → ℝ)}
    (h : BoolFormat R D S) (hR : R ≤ R') (hD : D ≤ D') : BoolFormat R' D' S := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  exact ⟨m, hm.trans hR, p, fun i => (hp i).trans hD, b, hb⟩

lemma BoolFormat.measurableSet {n D : ℕ} {R : ℝ} {S : Set (Fin n → ℝ)}
    (h : BoolFormat R D S) : MeasurableSet S := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  have hcoord (i : Fin m) : Measurable (fun x : Fin n → ℝ => decide (0 ≤ eval x (p i))) := by
    have hs : MeasurableSet {x : Fin n → ℝ | 0 ≤ eval x (p i)} :=
      measurableSet_le measurable_const (continuous_eval (p i)).measurable
    apply measurable_to_bool
    simpa only [preimage, mem_singleton_iff, decide_eq_true_eq] using hs

  have hmeas : Measurable (fun x : Fin n → ℝ => b (fun i => decide (0 ≤ eval x (p i)))) :=
    (measurable_of_finite b).comp (Measurable.of_eval hcoord)
  have heq : S = {x | b (fun i => decide (0 ≤ eval x (p i))) = true} := Set.ext hb
  rw [heq]
  exact measurableSet_eq_fun hmeas measurable_const

lemma BoolFormat.inter {n D D' : ℕ} {R R' : ℝ} {S T : Set (Fin n → ℝ)}
    (hS : BoolFormat R D S) (hT : BoolFormat R' D' T) :
    BoolFormat (R + R') (max D D') (S ∩ T) := by
  classical
  obtain ⟨m, hm, p, hp, b, hb⟩ := hS
  obtain ⟨m', hm', p', hp', b', hb'⟩ := hT
  refine ⟨m + m', by exact_mod_cast add_le_add hm hm', Fin.addCases p p', ?_,
    fun v => b (fun i => v (Fin.castAdd m' i)) && b' (fun i => v (Fin.natAdd m i)), ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using (hp j).trans (le_max_left D D')
    · simpa only [Fin.addCases_right] using (hp' j).trans (le_max_right D D')
  · intro x
    simp only [mem_inter_iff, Bool.and_eq_true, Fin.addCases_left, Fin.addCases_right]
    exact and_congr (hb x) (hb' x)

lemma BoolFormat.affine_preimage {n m D : ℕ} {R : ℝ} {S : Set (Fin n → ℝ)}
    (hS : BoolFormat R D S) (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) :
    BoolFormat R D ((fun x i => eval x (f i)) ⁻¹' S) := by
  obtain ⟨r, hr, p, hp, b, hb⟩ := hS
  refine ⟨r, hr, fun i => aeval f (p i), ?_, b, ?_⟩
  · exact fun i => (k4_eligibility_sign_description.degree_aeval_le (p i) f hf).trans (hp i)
  · intro x
    simpa only [mem_preimage, k4_eligibility_sign_description.eval_aeval_real] using hb (fun i => eval x (f i))

def unitPlanar {n : ℕ} (c : Fin 4 → Fin n) : Set (Fin n → ℝ) :=
  {x | ∀ j, x (c j) ∈ Ico (0 : ℝ) 1}

lemma unitPlanar_format {n : ℕ} (c : Fin 4 → Fin n) :
    BoolFormat 8 1 (unitPlanar c) := by
  classical
  let p : Fin (4 + 4) → MvPolynomial (Fin n) ℝ :=
    Fin.addCases (fun j => X (c j)) (fun j => X (c j) - C 1)
  let b : (Fin (4 + 4) → Bool) → Bool :=
    fun v => decide (∀ j, v (Fin.castAdd 4 j) = true ∧ v (Fin.natAdd 4 j) = false)
  refine ⟨8, by norm_num, p, ?_, b, ?_⟩
  · intro i
    refine Fin.addCases (m := 4) (n := 4) (fun j => ?_) (fun j => ?_) i
    · simp only [p, Fin.addCases_left, totalDegree_X, le_refl]
    · simpa only [p, Fin.addCases_right] using (totalDegree_sub_C_le (X (c j) : MvPolynomial (Fin n) ℝ) 1).trans_eq (totalDegree_X (c j))
  · intro x
    simp only [unitPlanar, mem_setOf_eq, mem_Ico, b, decide_eq_true_eq,
      p, Fin.addCases_left, Fin.addCases_right, eval_X, map_sub, eval_C,
      decide_eq_false_iff_not, not_le]
    simp only [sub_neg, lt_add_iff_pos_right, sub_lt_zero]

end
end Submission.Obl.k4_dyadic_crop_worlds
