/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/Atoms.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Interface

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

abbrev cell (J : ℕ) (z : Fin J) : Set ℝ :=
  Ico ((z : ℝ) / J) (((z : ℝ) + 1) / J)

abbrev intervalNoise (σ : ℝ) : Measure ℝ :=
  ENNReal.ofReal σ⁻¹ • volume.restrict (Icc 0 σ)

theorem intervalNoise_probability {σ : ℝ} (hσ : 0 < σ) :
    IsProbabilityMeasure (intervalNoise σ) := by
  constructor
  simp only [intervalNoise, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Icc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hσ.le), inv_mul_cancel₀ hσ.ne']
  simp

theorem noise_probability {σ : ℝ} (hσ : 0 < σ) : IsProbabilityMeasure (noise σ) := by
  letI : IsProbabilityMeasure (intervalNoise σ) := intervalNoise_probability hσ
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin 5 => intervalNoise σ))
  infer_instance

theorem noise_support {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ u ∂noise σ, ∀ i, u i ∈ Icc 0 σ := by
  letI : IsProbabilityMeasure (intervalNoise σ) := intervalNoise_probability hσ
  apply ae_all_iff.mpr
  intro i
  apply (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 5 => intervalNoise σ) (i := i)).eventually
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem measurable_event (H J : ℕ) (mark : Fin H → Fin J → Bool) :
    MeasurableSet (event H J mark) := by
  have heq : event H J mark = ⋃ j : Fin H, ⋃ z : Fin J,
      {p : Incidence | p.1.1 = (j : ℕ)} ∩
        {p : Incidence | mark j z = true} ∩ {p : Incidence | p.2 ∈ cell J z} := by
    ext p
    simp only [event, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    aesop
  rw [heq]
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro z
  exact ((measurableSet_eq_fun (by fun_prop) measurable_const).inter
    (by by_cases h : mark j z = true <;> simp [h])).inter
      (measurableSet_Ico.preimage measurable_snd)

theorem event_mono {H J : ℕ} {mark mark' : Fin H → Fin J → Bool}
    (h : ∀ j z, mark' j z = true → mark j z = true) :
    event H J mark' ⊆ event H J mark := by
  rintro p ⟨j, hj, z, hz, ht⟩
  exact ⟨j, hj, z, h j z hz, ht⟩

theorem law_mono {σ : ℝ} {H J : ℕ} {b : Fin H → Fin 5 → ℝ}
    {w : Fin H → ℝ} {mark mark' : Fin H → Fin J → Bool}
    (h : ∀ j z, mark' j z = true → mark j z = true) :
    law σ H J b w mark' ≤ law σ H J b w mark :=
  Measure.restrict_mono (event_mono h) le_rfl

theorem measurable_obs (N r : ℝ) : Measurable (obs N r) := by fun_prop

theorem measurable_aug (N r u : ℝ) : Measurable (aug N r u) := by fun_prop

theorem cell_subset {J : ℕ} (hJ : 0 < J) (z : Fin J) : cell J z ⊆ Ico (0 : ℝ) 1 := by
  intro t ht
  have hJr : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
  have hz : (z : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast z.isLt
  exact ⟨(div_nonneg (by positivity) hJr.le).trans ht.1,
    ht.2.trans_le ((div_le_one hJr).mpr hz)⟩

theorem cell_disjoint {J : ℕ} (hJ : 0 < J) : Pairwise (fun z z' : Fin J =>
    Disjoint (cell J z) (cell J z')) := by
  intro z z' hzz
  have hJr : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
  apply Set.disjoint_left.mpr
  intro t ht ht'
  have hne : z.val ≠ z'.val := fun h => hzz (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hz | hz
  · have hz' : (z : ℝ) + 1 ≤ (z' : ℝ) := by exact_mod_cast hz
    have := (div_le_div_of_nonneg_right hz' hJr.le).trans ht'.1
    exact (not_lt_of_ge this ht.2)
  · have hz' : (z' : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz
    have := (div_le_div_of_nonneg_right hz' hJr.le).trans ht.1
    exact (not_lt_of_ge this ht'.2)

theorem cell_volume {J : ℕ} (hJ : 0 < J) (z : Fin J) :
    volume (cell J z) = ENNReal.ofReal ((J : ℝ)⁻¹) := by
  rw [Real.volume_Ico]
  congr 1
  ring

abbrev atomMap {H : ℕ} (b : Fin H → Fin 5 → ℝ) (j : Fin H)
    (p : (Fin 5 → ℝ) × ℝ) : Incidence := (((j : ℕ), b j + p.1), p.2)

abbrev atom {H : ℕ} (σ : ℝ) (J : ℕ) (b : Fin H → Fin 5 → ℝ)
    (j : Fin H) (z : Fin J) : Measure Incidence :=
  (noise σ |>.prod (volume.restrict (cell J z))).map (atomMap b j)

theorem atom_mass {H J : ℕ} {σ : ℝ} (hσ : 0 < σ) (hJ : 0 < J)
    (b : Fin H → Fin 5 → ℝ) (j : Fin H) (z : Fin J) :
    atom σ J b j z univ = ENNReal.ofReal ((J : ℝ)⁻¹) := by
  letI := noise_probability hσ
  rw [atom, Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
    Measure.prod_apply MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    lintegral_const, measure_univ, mul_one]
  exact cell_volume hJ z


abbrev markedTimes {J : ℕ} (mark : Fin J → Bool) : Set ℝ :=
  {t | ∃ z, mark z = true ∧ t ∈ cell J z}

theorem measurable_markedTimes {J : ℕ} (mark : Fin J → Bool) :
    MeasurableSet (markedTimes mark) := by
  simp only [markedTimes, ofPred_exists]
  change MeasurableSet (⋃ z, {t | mark z = true ∧ t ∈ cell J z})
  apply MeasurableSet.iUnion
  intro z
  by_cases h : mark z = true
  · simpa only [h, true_and, ofPred_mem_eq] using (measurableSet_Ico : MeasurableSet (cell J z))
  · simp only [h, Bool.false_eq_true, false_and, ofPred_false, MeasurableSet.empty]

theorem event_atomMap {H J : ℕ} (b : Fin H → Fin 5 → ℝ) (j : Fin H)
    (mark : Fin H → Fin J → Bool) :
    atomMap b j ⁻¹' event H J mark = univ ×ˢ markedTimes (mark j) := by
  ext p
  simp only [event, atomMap, mem_preimage, mem_ofPred_eq, Prod.fst, Prod.snd,
    Nat.cast_id, Fin.val_inj, mem_prod, mem_univ, true_and, markedTimes]
  aesop

theorem law_eq_tag_sum {H J : ℕ} {σ : ℝ} (hσ : 0 < σ) (b : Fin H → Fin 5 → ℝ)
    (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) :
    law σ H J b w mark = ∑ j,
      ENNReal.ofReal (w j) •
        (noise σ |>.prod (volume.restrict (markedTimes (mark j)))).map (atomMap b j) := by
  classical
  letI := noise_probability hσ
  have hE := measurable_event H J mark
  have hprod (j : Fin H) :
      ((noise σ).map (fun u => ((j : ℕ), b j + u))).prod volume =
        (noise σ |>.prod volume).map (atomMap b j) := by
    have hm := Measure.map_prod_map (noise σ) (volume : Measure ℝ)
      (by fun_prop : Measurable (fun u : Fin 5 → ℝ => ((j : ℕ), b j + u)))
      (measurable_id : Measurable (id : ℝ → ℝ))
    rw [Measure.map_id] at hm
    have heq : Prod.map (fun u : Fin 5 → ℝ => ((j : ℕ), b j + u)) (id : ℝ → ℝ) =
        atomMap b j := by funext p; rfl
    rw [heq] at hm
    exact hm
  change ((∑ j, ENNReal.ofReal (w j) •
    (noise σ).map (fun u => ((j : ℕ), b j + u))).prod volume).restrict _ = _
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.restrict_sum _ hE,
    Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.prod_smul_left, Measure.restrict_smul, hprod j,
    Measure.restrict_map (by fun_prop) hE, event_atomMap,
    ← Measure.prod_restrict, Measure.restrict_univ]


theorem restrict_markedTimes {J : ℕ} (hJ : 0 < J) (mark : Fin J → Bool) :
    volume.restrict (markedTimes mark) =
      ∑ z, if mark z = true then volume.restrict (cell J z) else 0 := by
  classical
  let A : Fin J → Set ℝ := fun z => {t | mark z = true ∧ t ∈ cell J z}
  have hA (z : Fin J) : MeasurableSet (A z) := by
    by_cases h : mark z = true
    · simpa only [A, h, true_and, ofPred_mem_eq] using (measurableSet_Ico : MeasurableSet (cell J z))
    · simp only [A, h, Bool.false_eq_true, false_and, ofPred_false, MeasurableSet.empty]
  have hd : Pairwise (fun z z' => Disjoint (A z) (A z')) := by
    intro z z' hzz
    exact (cell_disjoint hJ hzz).mono (fun _ h => h.2) (fun _ h => h.2)
  have heq : markedTimes mark = ⋃ z, A z := by ext t; simp only [markedTimes, A, mem_iUnion, mem_ofPred_eq]
  rw [heq, Measure.restrict_iUnion hd hA, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : mark z = true
  · simp only [A, h, true_and, ofPred_mem_eq, ite_true]
  · simp only [A, h, Bool.false_eq_true, false_and, ofPred_false, Measure.restrict_empty, ite_false]

theorem law_eq_atoms {H J : ℕ} {σ : ℝ} (hσ : 0 < σ) (hJ : 0 < J)
    (b : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) :
    law σ H J b w mark = ∑ j, ∑ z,
      if mark j z = true then ENNReal.ofReal (w j) • atom σ J b j z else 0 := by
  classical
  letI := noise_probability hσ
  rw [law_eq_tag_sum hσ]
  apply Finset.sum_congr rfl
  intro j _
  letI (z : Fin J) : SFinite (if mark j z = true then volume.restrict (cell J z) else 0) := by
    split_ifs <;> infer_instance
  rw [restrict_markedTimes hJ, ← Measure.sum_fintype, Measure.prod_sum_right,
    Measure.sum_fintype, Measure.map_finset_sum' (by fun_prop : Measurable (atomMap b j)).aemeasurable,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : mark j z = true <;> simp [h, atom]

theorem law_mass {H J : ℕ} {σ : ℝ} (hσ : 0 < σ) (hJ : 0 < J)
    (b : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) :
    law σ H J b w mark univ = ∑ j, ∑ z,
      if mark j z = true then ENNReal.ofReal (w j) * ENNReal.ofReal ((J : ℝ)⁻¹) else 0 := by
  classical
  rw [law_eq_atoms hσ hJ]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : mark j z = true <;> simp [h, atom_mass hσ hJ]

theorem law_mass_le_one {H J : ℕ} {σ : ℝ} (hσ : 0 < σ) (hJ : 0 < J)
    (b : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    law σ H J b w mark univ ≤ 1 := by
  classical
  rw [law_mass hσ hJ]
  calc
    _ ≤ ∑ j : Fin H, ∑ _z : Fin J,
        ENNReal.ofReal (w j) * ENNReal.ofReal ((J : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro z _
      split_ifs <;> simp
    _ = (∑ j, ENNReal.ofReal (w j)) *
        ((J : ℝ≥0∞) * ENNReal.ofReal ((J : ℝ)⁻¹)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hw j), hsum]
      rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hJ), ENNReal.ofReal_natCast,
        ENNReal.mul_inv_cancel (by exact_mod_cast hJ.ne') (by simp)]
      simp

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
