import Submission.Obl.k4_scalar_conditional_crop_worlds.Definitions
import Submission.Obl.k4_dyadic_crop_worlds.Partition
import Submission.Obl.k4_scalar_marked_packet_recovery.MarkedMeasure

open MeasureTheory Set Finset Filter

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- The scalar intercept and velocity record. -/
def labelOf (N u : ℝ) (l : Line) : Label :=
  ![⌊l.2 0 / N ^ (-u)⌋, ⌊l.2 1 / N ^ (-u)⌋]

lemma cell_eq_preimage (N u : ℝ) (q : Label) :
    scalarCell N u q = labelOf N u ⁻¹' {q} := by
  ext l
  change (_ ∧ _) ↔ labelOf N u l = q
  constructor
  · rintro ⟨h0, h1⟩
    ext j
    fin_cases j
    · exact h0
    · exact h1
  · intro h
    exact ⟨congr_fun h 0, congr_fun h 1⟩

lemma measurable_labelOf (N u : ℝ) : Measurable (labelOf N u) := by
  unfold labelOf
  apply measurable_pi_iff.2
  intro j
  fin_cases j <;> simp only [Fin.isValue] <;>
    exact Int.measurable_floor.comp (by fun_prop)

lemma measurableSet_labelOf_preimage (N u : ℝ) (s : Set Label) :
    MeasurableSet (labelOf N u ⁻¹' s) :=
  measurable_labelOf N u (DiscreteMeasurableSpace.forall_measurableSet s)

/-- The finite box of possible scalar crop labels. -/
def labelBox (n : ℕ) : Finset Label := Fintype.piFinset (fun _ => Finset.Icc (-(n : ℤ)) n)

lemma card_labelBox (n : ℕ) : (labelBox n).card = (2 * n + 1) ^ 2 := by
  rw [labelBox, Fintype.card_piFinset, Int.card_Icc]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

lemma labelOf_mem_labelBox {N u R : ℝ} (hN : 0 < N) {n : ℕ}
    (hn : R / N ^ (-u) ≤ n) {l : Line} (hl : ∀ e, |l.2 e| ≤ R) :
    labelOf N u l ∈ labelBox n := by
  have ha : 0 < N ^ (-u) := Real.rpow_pos_of_pos hN _
  have key : ∀ e, |l.2 e / N ^ (-u)| ≤ n := by
    intro e
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    calc |l.2 e| ≤ R := hl e
      _ = R / N ^ (-u) * N ^ (-u) := by field_simp
      _ ≤ n * N ^ (-u) := mul_le_mul_of_nonneg_right hn ha.le
  rw [labelBox, Fintype.mem_piFinset]
  intro j
  fin_cases j
  · exact k4_dyadic_crop_worlds.floor_mem_Icc (key 0)
  · exact k4_dyadic_crop_worlds.floor_mem_Icc (key 1)

/-- A subpower sequence admits a fixed polynomial envelope, including its finite prefix. -/
lemma exists_polynomial_envelope {N K : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k)
    (hK : Subpower N K) : ∃ B : ℕ, 1 ≤ B ∧ ∀ k, K k + 1 ≤ N k ^ B := by
  have htail : ∀ᶠ k in atTop, K k ≤ N k := by
    simpa using hK.2 1 one_pos
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 htail
  have hprefix : ∀ n : ℕ, ∃ B : ℕ, ∀ k < n, K k + 1 ≤ N k ^ B := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨B, hB⟩ := ih
      obtain ⟨C, hC⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
        (show (1 : ℝ) < N n by linarith [hN n])).eventually_gt_atTop (K n + 1)).exists
      refine ⟨max B C, fun k hk => ?_⟩
      by_cases hkn : k < n
      · exact (hB k hkn).trans (pow_le_pow_right₀ (by linarith [hN k]) (le_max_left _ _))
      · have : k = n := by omega
        subst k
        exact hC.le.trans (pow_le_pow_right₀ (by linarith [hN n]) (le_max_right _ _))
  obtain ⟨B, hB⟩ := hprefix k₀
  refine ⟨max B 2, by omega, fun k => ?_⟩
  by_cases hk : k < k₀
  · exact (hB k hk).trans (pow_le_pow_right₀ (by linarith [hN k]) (le_max_left _ _))
  · have hKk := hk₀ k (by omega)
    have hN1 : 1 ≤ N k := by linarith [hN k]
    have hpow : N k + 1 ≤ N k ^ 2 := by nlinarith [hN k]
    exact (show K k + 1 ≤ N k + 1 by linarith).trans
      (hpow.trans (pow_le_pow_right₀ hN1 (le_max_right _ _)))

lemma card_labelBox_le {N u : ℝ} (hN : 2 ≤ N) (B U : ℕ) (hu : u ≤ U) :
    ((labelBox ⌈N ^ B / N ^ (-u)⌉₊).card : ℝ) ≤ N ^ (2 * (B + U + 3)) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hRa : N ^ B / N ^ (-u) ≤ N ^ (B + U) := by
    rw [Real.rpow_neg hN0.le, div_inv_eq_mul, pow_add]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hN1 hu)
      (by positivity)
  have hnle : (⌈N ^ B / N ^ (-u)⌉₊ : ℝ) ≤ N ^ (B + U) + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ N ^ B / N ^ (-u) by positivity)
    linarith
  have hN3 : (8 : ℝ) ≤ N ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN 3
  have hNM : (1 : ℝ) ≤ N ^ (B + U) := one_le_pow₀ hN1
  have hbase : 2 * (⌈N ^ B / N ^ (-u)⌉₊ : ℝ) + 1 ≤ N ^ (B + U + 3) := by
    rw [pow_add]
    nlinarith
  rw [card_labelBox]
  push_cast
  calc (2 * (⌈N ^ B / N ^ (-u)⌉₊ : ℝ) + 1) ^ 2 ≤ (N ^ (B + U + 3)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbase 2
    _ = N ^ (2 * (B + U + 3)) := by rw [← pow_mul]; congr 1; omega

/-- The marked prior stays within the centers' bound plus the noise width. -/
lemma markedPrior_ae_bound {σ K : ℝ} (hσ : 0 < σ) {H : ℕ}
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (hb : ∀ j e, |b₀ j e| ≤ K) :
    ∀ᵐ l ∂MarkedPrior σ H b₀ w, ∀ e, |l.2 e| ≤ K + σ := by
  apply ae_finsetSum_measure_iff.mpr
  intro j hj
  apply Measure.ae_smul_measure
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  filter_upwards [k4_scalar_marked_packet_recovery.noise_ae_cube hσ] with u hu e
  change |b₀ j e + u e| ≤ K + σ
  exact (abs_add_le _ _).trans (add_le_add (hb j e) (by simpa [abs_of_nonneg (hu e).1] using (hu e).2))

/-- Finite scalar cell masses add to the prior mass. -/
lemma sum_cell {ν : Measure Line} {N u : ℝ} (F : Finset Label)
    (hF : ν (labelOf N u ⁻¹' (↑F : Set Label)ᶜ) = 0) :
    ∑ q ∈ F, ν (scalarCell N u q) = ν univ := by
  have h1 : ∑ q ∈ F, ν (labelOf N u ⁻¹' {q}) = ν (labelOf N u ⁻¹' ↑F) :=
    sum_measure_preimage_singleton F fun y _ => measurableSet_labelOf_preimage N u {y}
  have h3 : ν (labelOf N u ⁻¹' ↑F) + ν (labelOf N u ⁻¹' (↑F : Set Label)ᶜ) = ν univ := by
    rw [Set.preimage_compl]
    exact measure_add_measure_compl (measurableSet_labelOf_preimage N u _)
  rw [hF, add_zero] at h3
  rw [← h3, ← h1]
  simp_rw [cell_eq_preimage]

lemma sum_cell_inter {μ : Measure State} {N u : ℝ} (F : Finset Label)
    (hF : μ ((labelOf N u ⁻¹' (↑F : Set Label)ᶜ) ×ˢ univ) = 0) (E : Set State) :
    ∑ q ∈ F, μ (E ∩ (scalarCell N u q ×ˢ univ)) = μ E := by
  let f : State → Label := fun z => labelOf N u z.1
  have hfm : Measurable f := (measurable_labelOf N u).comp measurable_fst
  have hfib : ∀ q, f ⁻¹' {q} = scalarCell N u q ×ˢ univ := by
    intro q
    ext z
    simp [f, cell_eq_preimage]
  have h1 : ∑ q ∈ F, (μ.restrict E) (f ⁻¹' {q}) = (μ.restrict E) (f ⁻¹' ↑F) :=
    sum_measure_preimage_singleton F fun y _ => hfm (measurableSet_singleton y)
  have h2 : (μ.restrict E) (f ⁻¹' (↑F : Set Label)ᶜ) = 0 := by
    have hsub : f ⁻¹' (↑F : Set Label)ᶜ = (labelOf N u ⁻¹' (↑F : Set Label)ᶜ) ×ˢ Set.univ := by
      ext z; simp [f]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (by rw [hsub, hF]))
  have h3 : (μ.restrict E) (f ⁻¹' ↑F) + (μ.restrict E) (f ⁻¹' (↑F : Set Label)ᶜ) =
      (μ.restrict E) univ := by
    rw [Set.preimage_compl]
    exact measure_add_measure_compl (hfm (DiscreteMeasurableSpace.forall_measurableSet _))
  rw [h2, add_zero, Measure.restrict_apply_univ] at h3
  rw [← h3, ← h1]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Measure.restrict_apply (hfm (measurableSet_singleton q)), hfib, Set.inter_comm]

lemma selected_le_cell {ν : Measure Line} [SFinite ν] {E : Set State}
    (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (N u : ℝ) (q : Label) :
    (ν.prod volume) (E ∩ (scalarCell N u q ×ˢ univ)) ≤ ν (scalarCell N u q) := by
  calc (ν.prod volume) (E ∩ (scalarCell N u q ×ˢ Set.univ)) ≤
      (ν.prod volume) (scalarCell N u q ×ˢ Icc (0 : ℝ) 1) := by
        apply measure_mono
        rintro z ⟨hzE, hzc, -⟩
        exact ⟨hzc, (hE hzE).2⟩
    _ = ν (scalarCell N u q) := by
      rw [Measure.prod_prod, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

lemma selected_le_one {ν : Measure Line} [IsProbabilityMeasure ν] {E : Set State}
    (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) : (ν.prod volume) E ≤ 1 := by
  calc (ν.prod volume) E ≤ (ν.prod volume) (Set.univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hE
    _ = 1 := by simp [Measure.prod_prod]

/-- A bounded probability prior and its selected law have the same finite cell partition. -/
theorem world_partition {N : ℝ} (hN : 2 ≤ N) (B U : ℕ) {u : ℝ} (hu : u ≤ U)
    {ν : Measure Line} [IsProbabilityMeasure ν] (hν : ∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ N ^ B)
    {E : Set State} (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    ((labelBox ⌈N ^ B / N ^ (-u)⌉₊).card : ℝ) ≤ N ^ (2 * (B + U + 3)) ∧
    ∑ q ∈ labelBox ⌈N ^ B / N ^ (-u)⌉₊, (ν (scalarCell N u q)).toReal = 1 ∧
    ∑ q ∈ labelBox ⌈N ^ B / N ^ (-u)⌉₊,
      ((ν.prod volume) (E ∩ (scalarCell N u q ×ˢ univ))).toReal = ((ν.prod volume) E).toReal ∧
    (∀ q, ((ν.prod volume) (E ∩ (scalarCell N u q ×ˢ univ))).toReal ≤
      (ν (scalarCell N u q)).toReal) ∧ (ν.prod volume) E ≤ 1 := by
  let F := labelBox ⌈N ^ B / N ^ (-u)⌉₊
  have hN0 : 0 < N := by linarith
  have hnull : ν (labelOf N u ⁻¹' (↑F : Set Label)ᶜ) = 0 := by
    change ν {l | ¬labelOf N u l ∈ F} = 0
    apply ae_iff.1
    filter_upwards [hν] with l hl
    exact labelOf_mem_labelBox hN0 (Nat.le_ceil _) hl
  have hnull' : (ν.prod (volume : Measure ℝ))
      ((labelOf N u ⁻¹' (↑F : Set Label)ᶜ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, hnull, zero_mul]
  refine ⟨card_labelBox_le hN B U hu, ?_, ?_, ?_, selected_le_one hE⟩
  · rw [← ENNReal.toReal_sum (fun q _ => measure_ne_top ν _), sum_cell F hnull, measure_univ,
      ENNReal.toReal_one]
  · rw [← ENNReal.toReal_sum, sum_cell_inter F hnull' E]
    intro q _
    exact ((selected_le_cell hE N u q).trans_lt (measure_lt_top ν _)).ne
  · intro q
    exact ENNReal.toReal_mono (measure_ne_top ν _) (selected_le_cell hE N u q)

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
