import Submission.Obl.k4_dyadic_crop_worlds.Definitions

/-!
# The finite partition into crop cells

The cells `cell a q` are the fibres of the label map `labelOf a`. A prior in the polynomial
format lives in the coordinate box `[-R, R]^6`, so only the labels of the finite set
`labelBox n` with `n = ⌈R / a⌉₊` carry mass. Prior and selected masses add up over these labels.
-/

open MeasureTheory Set Finset

namespace Submission.Obl.k4_dyadic_crop_worlds

noncomputable section

/-! ### The dyadic side -/

lemma side_le_one {N u : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) : side N u ≤ 1 := by
  unfold side
  apply zpow_le_one_of_nonpos₀ (by norm_num)
  have : (0 : ℝ) ≤ u * Real.log N / Real.log 2 :=
    div_nonneg (mul_nonneg hu (Real.log_nonneg hN)) (Real.log_nonneg (by norm_num))
  have : (0 : ℤ) ≤ ⌊u * Real.log N / Real.log 2⌋ := Int.floor_nonneg.2 this
  omega

lemma rpow_neg_le_side {N u : ℝ} (hN : 0 < N) : N ^ (-u) ≤ side N u := by
  unfold side
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Real.rpow_intCast]
  have h : N ^ (-u) = (2 : ℝ) ^ (-(u * Real.log N / Real.log 2)) := by
    rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp
  rw [h]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  linarith [Int.floor_le (u * Real.log N / Real.log 2)]

lemma side_pos' (N u : ℝ) : 0 < side N u := zpow_pos (by norm_num) _

/-! ### Labels -/

/-- The crop label of a line. -/
def labelOf (a : ℝ) (l : Line) : Label := ![⌊l.2 0 / a⌋, ⌊l.2 1 / a⌋, ⌊l.2 3 / a⌋, ⌊l.2 4 / a⌋]

lemma cell_eq_preimage (a : ℝ) (q : Label) : cell a q = labelOf a ⁻¹' {q} := by
  ext l
  rw [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    ext j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h
    exact ⟨congr_fun h 0, congr_fun h 1, congr_fun h 2, congr_fun h 3⟩

lemma measurable_labelOf (a : ℝ) : Measurable (labelOf a) := by
  unfold labelOf
  apply measurable_pi_iff.2
  intro j
  fin_cases j <;> simp only [Fin.isValue] <;>
    exact Int.measurable_floor.comp (by fun_prop)

lemma measurableSet_labelOf_preimage (a : ℝ) (s : Set Label) :
    MeasurableSet (labelOf a ⁻¹' s) :=
  measurable_labelOf a (DiscreteMeasurableSpace.forall_measurableSet s)

/-- The labels with all four entries in `[-n, n]`. -/
def labelBox (n : ℕ) : Finset Label := Fintype.piFinset (fun _ => Finset.Icc (-(n : ℤ)) n)

lemma card_labelBox (n : ℕ) : (labelBox n).card = (2 * n + 1) ^ 4 := by
  rw [labelBox, Fintype.card_piFinset, Int.card_Icc]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

lemma floor_mem_Icc {x : ℝ} {n : ℕ} (hx : |x| ≤ n) : ⌊x⌋ ∈ Finset.Icc (-(n : ℤ)) n := by
  rw [abs_le] at hx
  rw [Finset.mem_Icc]
  constructor
  · apply Int.le_floor.2
    push_cast
    linarith
  · apply Int.floor_le_iff.2
    push_cast
    linarith

lemma labelOf_mem_labelBox {a R : ℝ} (ha : 0 < a) {n : ℕ} (hn : R / a ≤ n) {l : Line}
    (hl : ∀ b, |l.2 b| ≤ R) : labelOf a l ∈ labelBox n := by
  have key : ∀ b, |l.2 b / a| ≤ n := by
    intro b
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    calc |l.2 b| ≤ R := hl b
      _ = R / a * a := by field_simp
      _ ≤ n * a := mul_le_mul_of_nonneg_right hn ha.le
  rw [labelBox, Fintype.mem_piFinset]
  intro j
  fin_cases j
  · exact floor_mem_Icc (key 0)
  · exact floor_mem_Icc (key 1)
  · exact floor_mem_Icc (key 3)
  · exact floor_mem_Icc (key 4)

/-! ### Support of a formatted prior -/

/-- Lines outside the coordinate box `[-R, R]^6`. -/
def farLines (R : ℝ) : Set Line := {l | ∃ b, R < |l.2 b|}

lemma measurableSet_farLines (R : ℝ) : MeasurableSet (farLines R) := by
  have : farLines R = ⋃ b, {l : Line | R < |l.2 b|} := by
    ext l; simp [farLines]
  rw [this]
  refine MeasurableSet.iUnion fun b => ?_
  exact measurableSet_lt measurable_const (by fun_prop)

lemma priorFormat_far_null {R : ℝ} {D : ℕ} {ν : Measure Line} (hν : PriorFormat R D ν) :
    ν (farLines R) = 0 := by
  obtain ⟨m, -, c, i, A, hA, rfl⟩ := hν
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) (measurableSet_farLines R),
    Measure.restrict_apply ((measurableSet_farLines R).preimage (by fun_prop))]
  have : (fun x : Coeff => (i j, x)) ⁻¹' farLines R ∩ A j = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, farLines, Set.mem_ofPred_eq, mem_empty_iff_false,
      iff_false, not_and]
    rintro ⟨b, hb⟩ hx
    exact absurd ((hA j).2.2.2.2 x hx b) (not_le.2 hb)
  rw [this, measure_empty, smul_zero]

/-! ### Mass sums over the cells -/

lemma labelOf_preimage_compl_subset {a R : ℝ} (ha : 0 < a) {n : ℕ} (hn : R / a ≤ n) :
    labelOf a ⁻¹' (↑(labelBox n) : Set Label)ᶜ ⊆ farLines R := by
  intro l hl
  by_contra h
  simp only [farLines, Set.mem_ofPred_eq, not_exists, not_lt] at h
  exact hl (labelOf_mem_labelBox ha hn h)

/-- Masses of a measure on incidences add up over the cells of a finite label set carrying it. -/
lemma sum_cell_inter {μ : Measure Incident} {a : ℝ} (F : Finset Label)
    (hF : μ ((labelOf a ⁻¹' (↑F : Set Label)ᶜ) ×ˢ univ) = 0) (E : Set Incident) :
    ∑ q ∈ F, μ (E ∩ (cell a q ×ˢ univ)) = μ E := by
  set f : Incident → Label := fun z => labelOf a z.1 with hf
  have hfm : Measurable f := (measurable_labelOf a).comp measurable_fst
  have hfib : ∀ q, f ⁻¹' {q} = cell a q ×ˢ univ := by
    intro q
    ext z
    simp [hf, cell_eq_preimage]
  have h1 : ∑ q ∈ F, (μ.restrict E) (f ⁻¹' {q}) = (μ.restrict E) (f ⁻¹' ↑F) :=
    sum_measure_preimage_singleton F fun y _ => hfm (measurableSet_singleton y)
  have h2 : (μ.restrict E) (f ⁻¹' (↑F : Set Label)ᶜ) = 0 := by
    have hsub : f ⁻¹' (↑F : Set Label)ᶜ = (labelOf a ⁻¹' (↑F : Set Label)ᶜ) ×ˢ Set.univ := by
      ext z; simp [hf]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (by rw [hsub, hF]))
  have h3 : (μ.restrict E) (f ⁻¹' ↑F) + (μ.restrict E) (f ⁻¹' (↑F : Set Label)ᶜ) =
      (μ.restrict E) univ := by
    rw [Set.preimage_compl]
    exact measure_add_measure_compl (hfm (DiscreteMeasurableSpace.forall_measurableSet _))
  rw [h2, add_zero, Measure.restrict_apply_univ] at h3
  rw [← h3, ← h1]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Measure.restrict_apply (hfm (measurableSet_singleton q)), hfib, Set.inter_comm]

/-- Masses of a measure on lines add up over the cells of a finite label set carrying it. -/
lemma sum_cell {ν : Measure Line} {a : ℝ} (F : Finset Label)
    (hF : ν (labelOf a ⁻¹' (↑F : Set Label)ᶜ) = 0) :
    ∑ q ∈ F, ν (cell a q) = ν univ := by
  have h1 : ∑ q ∈ F, ν (labelOf a ⁻¹' {q}) = ν (labelOf a ⁻¹' ↑F) :=
    sum_measure_preimage_singleton F fun y _ => measurableSet_labelOf_preimage a {y}
  have h3 : ν (labelOf a ⁻¹' ↑F) + ν (labelOf a ⁻¹' (↑F : Set Label)ᶜ) = ν univ := by
    rw [Set.preimage_compl]
    exact measure_add_measure_compl (measurableSet_labelOf_preimage a _)
  rw [hF, add_zero] at h3
  rw [← h3, ← h1]
  simp_rw [cell_eq_preimage]

lemma selected_le_cell {ν : Measure Line} [SFinite ν] {E : Set Incident}
    (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (a : ℝ) (q : Label) :
    (ν.prod volume) (E ∩ (cell a q ×ˢ univ)) ≤ ν (cell a q) := by
  calc (ν.prod volume) (E ∩ (cell a q ×ˢ Set.univ)) ≤ (ν.prod volume) (cell a q ×ˢ Icc (0 : ℝ) 1) := by
        apply measure_mono
        rintro z ⟨hzE, hzc, -⟩
        exact ⟨hzc, (hE hzE).2⟩
    _ = ν (cell a q) := by
        rw [Measure.prod_prod, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

lemma selected_le_one {ν : Measure Line} [IsProbabilityMeasure ν] {E : Set Incident}
    (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) : (ν.prod volume) E ≤ 1 := by
  calc (ν.prod volume) E ≤ (ν.prod volume) (Set.univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hE
    _ = 1 := by
        rw [Measure.prod_prod, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one,
          measure_univ]

/-! ### The cell count -/

lemma card_labelBox_le {N : ℝ} (hN : 2 ≤ N) (M : ℕ) {u : ℝ} (hu4 : u ≤ 4) :
    ((labelBox ⌈N ^ M / side N u⌉₊).card : ℝ) ≤ N ^ (4 * M + 28) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  set a := side N u with ha
  have hapos : 0 < a := side_pos' N u
  set n := ⌈N ^ M / a⌉₊ with hn
  have hinv : a⁻¹ ≤ N ^ 4 := by
    have h1 : N ^ (-u) ≤ a := rpow_neg_le_side hN0
    have h2 : N ^ (-(4 : ℝ)) ≤ N ^ (-u) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h3 : N ^ (-(4 : ℝ)) = (N ^ 4)⁻¹ := by
      rw [Real.rpow_neg hN0.le]; norm_cast
    rw [h3] at h2
    rw [inv_le_comm₀ hapos (by positivity)]
    linarith
  have hRa : N ^ M / a ≤ N ^ (M + 4) := by
    rw [div_eq_mul_inv, pow_add]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hnle : (n : ℝ) ≤ N ^ (M + 4) + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ N ^ M / a by positivity)
    linarith
  have hN3 : (8 : ℝ) ≤ N ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN 3
  have hNM : (1 : ℝ) ≤ N ^ (M + 4) := one_le_pow₀ hN1
  have hbase : 2 * (n : ℝ) + 1 ≤ N ^ (M + 7) := by
    have : N ^ (M + 7) = N ^ (M + 4) * N ^ 3 := by rw [← pow_add]
    rw [this]
    nlinarith
  rw [card_labelBox]
  push_cast
  calc (2 * (n : ℝ) + 1) ^ 4 ≤ (N ^ (M + 7)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase 4
    _ = N ^ (4 * M + 28) := by rw [← pow_mul]; ring_nf

/-- The partition of one formatted world into finitely many crop cells, in real masses. -/
theorem world_partition {N : ℝ} (hN : 2 ≤ N) {M D : ℕ} {u : ℝ} (hu4 : u ≤ 4)
    {ν : Measure Line} [IsProbabilityMeasure ν] (hν : PriorFormat (N ^ M) D ν)
    {E : Set Incident} (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    ((labelBox ⌈N ^ M / side N u⌉₊).card : ℝ) ≤ N ^ (4 * M + 28) ∧
    ∑ q ∈ labelBox ⌈N ^ M / side N u⌉₊, (ν (cell (side N u) q)).toReal = 1 ∧
    ∑ q ∈ labelBox ⌈N ^ M / side N u⌉₊,
        ((ν.prod volume) (E ∩ (cell (side N u) q ×ˢ univ))).toReal =
      ((ν.prod volume) E).toReal ∧
    (∀ q, ((ν.prod volume) (E ∩ (cell (side N u) q ×ˢ univ))).toReal ≤
      (ν (cell (side N u) q)).toReal) ∧
    (ν.prod volume) E ≤ 1 := by
  set a := side N u with ha
  have hapos : 0 < a := side_pos' N u
  set F := labelBox ⌈N ^ M / a⌉₊ with hF
  have hnull : ν (labelOf a ⁻¹' (↑F : Set Label)ᶜ) = 0 :=
    measure_mono_null (labelOf_preimage_compl_subset hapos (Nat.le_ceil _))
      (priorFormat_far_null hν)
  have hnull' : (ν.prod (volume : Measure ℝ)) ((labelOf a ⁻¹' (↑F : Set Label)ᶜ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, hnull, zero_mul]
  refine ⟨card_labelBox_le hN M hu4, ?_, ?_, ?_, selected_le_one hE⟩
  · rw [← ENNReal.toReal_sum (fun q _ => measure_ne_top ν _), sum_cell F hnull, measure_univ,
      ENNReal.toReal_one]
  · rw [← ENNReal.toReal_sum, sum_cell_inter F hnull' E]
    intro q _
    exact ((selected_le_cell hE a q).trans_lt (measure_lt_top ν _)).ne
  · intro q
    exact ENNReal.toReal_mono (measure_ne_top ν _) (selected_le_cell hE a q)

end

end Submission.Obl.k4_dyadic_crop_worlds
