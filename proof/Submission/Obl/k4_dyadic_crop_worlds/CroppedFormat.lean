import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat
import Submission.Obl.k4_dyadic_crop_worlds.Volume

namespace Submission.Obl.k4_dyadic_crop_worlds

open MeasureTheory Set MvPolynomial
noncomputable section

def croppedRegion (A : Set Coeff) (a : ℝ) (q : Label) : Set Coeff :=
  cropCoeff a q '' {x | x ∈ A ∧ (0, x) ∈ cell a q}

lemma uncrop_mem_cell_iff {a : ℝ} (ha : a ≠ 0) (q : Label) (x : Coeff) (i : ℕ) :
    (i, uncropCoeff a q x) ∈ cell a q ↔ x ∈ unitPlanar planarCoord := by
  rw [mem_cell_iff]
  change (∀ j, ⌊uncropCoeff a q x (planarCoord j) / a⌋ = q j) ↔ _
  have heval (j : Fin 4) : uncropCoeff a q x (planarCoord j) / a = x (planarCoord j) + (q j : ℝ) := by
    fin_cases j <;> simp [uncropCoeff, planarCoord, ha]
  simp_rw [heval, Int.floor_eq_iff]
  apply forall_congr'
  intro j
  change ((q j : ℝ) ≤ x (planarCoord j) + (q j : ℝ) ∧
    x (planarCoord j) + (q j : ℝ) < (q j : ℝ) + 1) ↔
    (0 ≤ x (planarCoord j) ∧ x (planarCoord j) < 1)
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma croppedRegion_eq {a : ℝ} (ha : a ≠ 0) (q : Label) (A : Set Coeff) :
    croppedRegion A a q = uncropCoeff a q ⁻¹' A ∩ unitPlanar planarCoord := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hycell⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [mem_preimage, uncrop_cropCoeff ha] using hyA
    · exact fun j => cropCoeff_planar_mem hycell j
  · rintro ⟨hxA, hxunit⟩
    refine ⟨uncropCoeff a q x, ⟨hxA, (uncrop_mem_cell_iff ha q x 0).2 hxunit⟩,
      crop_uncropCoeff ha q x⟩

def uncropPolynomial (a : ℝ) (q : Label) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![C a * (X 0 + C (q 0 : ℝ)), C a * (X 1 + C (q 1 : ℝ)), X 2,
    C a * (X 3 + C (q 2 : ℝ)), C a * (X 4 + C (q 3 : ℝ)), X 5]

lemma uncropPolynomial_eval (a : ℝ) (q : Label) (x : Coeff) :
    (fun i => eval x (uncropPolynomial a q i)) = uncropCoeff a q x := by
  ext i
  fin_cases i <;> simp [uncropPolynomial, uncropCoeff]

lemma uncropPolynomial_degree (a : ℝ) (q : Label) :
    ∀ i, (uncropPolynomial a q i).totalDegree ≤ 1 := by
  intro i
  have h (j : Fin 6) (r : ℝ) : (C a * (X j + C r) : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 := by
    exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
      ((totalDegree_add _ _).trans (by simp))
  fin_cases i
  · exact h 0 (q 0)
  · exact h 1 (q 1)
  · simp [uncropPolynomial]
  · exact h 3 (q 2)
  · exact h 4 (q 3)
  · simp [uncropPolynomial]

lemma croppedRegion_format {R a : ℝ} {D : ℕ} {A : Set Coeff}
    (hA : BoolFormat R D A) (ha : a ≠ 0) (q : Label) :
    BoolFormat (R + 8) (max D 1) (croppedRegion A a q) := by
  rw [croppedRegion_eq ha]
  have hf := hA.affine_preimage (uncropPolynomial a q) (uncropPolynomial_degree a q)
  have heval : (fun x i => eval x (uncropPolynomial a q i)) = uncropCoeff a q :=
    funext (uncropPolynomial_eval a q)
  rw [heval] at hf
  exact hf.inter (unitPlanar_format planarCoord)

lemma croppedRegion_bound {R a : ℝ} {q : Label} {A : Set Coeff} (hR : 1 ≤ R)
    (hA : ∀ x ∈ A, ∀ i, |x i| ≤ R) : ∀ x ∈ croppedRegion A a q, ∀ i, |x i| ≤ R := by
  rintro _ ⟨y, ⟨hyA, hycell⟩, rfl⟩
  exact cropCoeff_bound hR hycell (hA y hyA)

/-- Seven-variable inverse substitution, keeping the time variable. -/
def uncropPolynomial7 (a : ℝ) (q : Label) : Fin 7 → MvPolynomial (Fin 7) ℝ :=
  ![C a * (X 0 + C (q 0 : ℝ)), C a * (X 1 + C (q 1 : ℝ)), X 2,
    C a * (X 3 + C (q 2 : ℝ)), C a * (X 4 + C (q 3 : ℝ)), X 5, X 6]

def uncrop7 (a : ℝ) (q : Label) (x : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![a * (x 0 + (q 0 : ℝ)), a * (x 1 + (q 1 : ℝ)), x 2,
    a * (x 3 + (q 2 : ℝ)), a * (x 4 + (q 3 : ℝ)), x 5, x 6]

lemma uncropPolynomial7_eval (a : ℝ) (q : Label) (x : Fin 7 → ℝ) :
    (fun i => eval x (uncropPolynomial7 a q i)) = uncrop7 a q x := by
  ext i
  fin_cases i <;> simp [uncropPolynomial7, uncrop7]

lemma uncropPolynomial7_degree (a : ℝ) (q : Label) :
    ∀ i, (uncropPolynomial7 a q i).totalDegree ≤ 1 := by
  intro i
  have h (j : Fin 7) (r : ℝ) : (C a * (X j + C r) : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 := by
    exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
      ((totalDegree_add _ _).trans (by simp))
  fin_cases i
  · exact h 0 (q 0)
  · exact h 1 (q 1)
  · simp [uncropPolynomial7]
  · exact h 3 (q 2)
  · exact h 4 (q 3)
  · simp [uncropPolynomial7]
  · simp [uncropPolynomial7]

lemma event_section_crop_eq {a : ℝ} (ha : a ≠ 0) (q : Label) (E : Set Incident) (i : ℕ) :
    {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ cropEvent E a q} =
      uncrop7 a q ⁻¹' {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ E} ∩
        unitPlanar (fun j => (planarCoord j).castSucc) := by
  have hcoeff (x : Fin 7 → ℝ) :
      (fun j : Fin 6 => uncrop7 a q x j.castSucc) =
        uncropCoeff a q (fun j : Fin 6 => x j.castSucc) := by
    ext j
    fin_cases j <;> rfl
  ext x
  change ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ cropEvent E a q ↔ _
  have heq : ((i, fun j : Fin 6 => x j.castSucc), x 6) =
      cropPoint a q ((i, uncropCoeff a q (fun j : Fin 6 => x j.castSucc)), x 6) := by
    simp only [cropPoint, cropLine, crop_uncropCoeff ha]
  rw [heq, cropEvent, (cropPoint_injective ha q).mem_set_image]
  simp only [mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage, mem_setOf_eq]
  rw [hcoeff]
  change (((i, uncropCoeff a q (fun j : Fin 6 => x j.castSucc)), x 6) ∈ E ∧
    (i, uncropCoeff a q (fun j : Fin 6 => x j.castSucc)) ∈ cell a q) ↔ _
  exact and_congr Iff.rfl (uncrop_mem_cell_iff ha q _ i)

lemma cropEvent_format {R a : ℝ} {D : ℕ} {E : Set Incident}
    (hR : 1 ≤ R) (hE : EventFormat R D E) (ha : a ≠ 0) (q : Label) :
    EventFormat (R + 8) (max D 1) (cropEvent E a q) := by
  obtain ⟨hEm, hEt, hEb, hEf⟩ := hE
  refine ⟨measurable_cropEvent ha q hEm, cropEvent_time hEt a q, ?_, ?_⟩
  · intro z hz
    obtain ⟨hi, hx⟩ := cropEvent_bound hR hEb z hz
    exact ⟨by linarith, fun e => (hx e).trans (by linarith)⟩
  · intro i
    rw [event_section_crop_eq ha]
    have hf := (hEf i).affine_preimage (uncropPolynomial7 a q) (uncropPolynomial7_degree a q)
    have heval : (fun x i => eval x (uncropPolynomial7 a q i)) = uncrop7 a q :=
      funext (uncropPolynomial7_eval a q)
    rw [heval] at hf
    exact hf.inter (unitPlanar_format _)

lemma restrict_component (a : ℝ) (q : Label) (i : ℕ) (A : Set Coeff) :
    (Measure.map (fun x => (i, x)) (volume.restrict A)).restrict (cell a q) =
      Measure.map (fun x => (i, x))
        (volume.restrict {x | x ∈ A ∧ (0, x) ∈ cell a q}) := by
  rw [Measure.restrict_map (by fun_prop) (measurable_cell a q),
    Measure.restrict_restrict ((measurable_cell a q).preimage (by fun_prop))]
  congr 2
  ext x
  change ((i, x) ∈ cell a q ∧ x ∈ A) ↔ (x ∈ A ∧ (0, x) ∈ cell a q)
  simp only [cell, mem_setOf_eq]
  tauto

lemma map_crop_component {a : ℝ} (ha : a ≠ 0) (q : Label) (i : ℕ) (A : Set Coeff) :
    Measure.map (cropLine a q)
      ((Measure.map (fun x => (i, x)) (volume.restrict A)).restrict (cell a q)) =
      ENNReal.ofReal (a ^ 4) • Measure.map (fun x => (i, x))
        (volume.restrict (croppedRegion A a q)) := by
  rw [restrict_component, Measure.map_map (continuous_cropLine a q).measurable (by fun_prop)]
  have heq : cropLine a q ∘ (fun x => (i, x)) = (fun x => (i, x)) ∘ cropCoeff a q := rfl
  rw [heq, ← Measure.map_map (by fun_prop) (show Measurable (cropCoeff a q) from (coeffHomeomorph ha q).continuous.measurable),
    map_cropCoeff_restrict ha q, Measure.map_smul _ (by fun_prop)]
  rfl

lemma cropPrior_format {R a δ p : ℝ} {D : ℕ} {ν : Measure Line}
    (hR : 1 ≤ R) (hν : PriorFormat R D ν) (ha : 0 < a) (ha1 : a ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hp : δ ≤ p) (q : Label) :
    PriorFormat ((R + 8) / δ) (max D 1) (cropPrior ν a q p) := by
  classical
  obtain ⟨m, hm, c, i, A, hA, hνeq⟩ := hν
  have hRp : 0 ≤ R := by linarith
  have hscale : R + 8 ≤ (R + 8) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith
  have hsize : R ≤ (R + 8) / δ := (by linarith : R ≤ R + 8).trans hscale
  have hppos : 0 < p := hδ.trans_le hp
  have ha4 : a ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ ha.le ha1 4
  refine ⟨m, hm.trans hsize, (fun j => c j * a ^ 4 / p), i,
    (fun j => croppedRegion (A j) a q), ?_, ?_⟩
  · intro j
    obtain ⟨hc0, hcR, hi, hfmt, hcoord⟩ := hA j
    refine ⟨by positivity, ?_, hi.trans hsize,
      (croppedRegion_format hfmt ha.ne' q).mono hscale le_rfl,
      fun x hx b => (croppedRegion_bound hR hcoord x hx b).trans hsize⟩
    calc
      c j * a ^ 4 / p ≤ R / p := by gcongr; nlinarith
      _ ≤ R / δ := div_le_div_of_nonneg_left hRp hδ hp
      _ ≤ (R + 8) / δ := by gcongr; linarith
  · have hrestr : ν.restrict (cell a q) = ∑ j,
        (ENNReal.ofReal (c j)) •
          (Measure.map (fun x => (i j, x)) (volume.restrict (A j))).restrict (cell a q) := by
      rw [hνeq]
      have h := map_sum (Measure.restrictₗ (cell a q))
        (fun j => ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x)) (volume.restrict (A j)))
        Finset.univ
      change (∑ j, ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x))
        (volume.restrict (A j))).restrict (cell a q) = ∑ j,
          (ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x))
            (volume.restrict (A j))).restrict (cell a q) at h
      simpa only [Measure.restrict_smul] using h
    rw [cropPrior, hrestr, Measure.map_finset_sum (continuous_cropLine a q).measurable.aemeasurable,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Measure.map_smul _ (continuous_cropLine a q).measurable.aemeasurable,
      map_crop_component ha.ne' q, smul_smul, smul_smul]
    congr 1
    rw [ENNReal.ofReal_div_of_pos hppos, ENNReal.ofReal_mul (hA j).1]
    simp only [div_eq_mul_inv]
    ac_rfl

end
end Submission.Obl.k4_dyadic_crop_worlds
