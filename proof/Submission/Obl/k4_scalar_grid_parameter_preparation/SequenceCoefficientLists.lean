import Submission.Obl.k4_scalar_grid_parameter_preparation.SequenceEntryPruning

/-! A common original-law entry mask has subpower coefficient lists at all registered depths. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical ENNReal

theorem exists_sequence_coefficient_lists {X : Type*} [MeasurableSpace X]
    (N K L Hf : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hL : (∀ k, 1 ≤ L k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L k ≤ N k ^ ε)
    (hHf : (∀ k, 1 ≤ Hf k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Hf k ≤ N k ^ ε)
    (W : ℕ → ℕ) (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (θ : (k : ℕ) → Fin (W k) → Measure X) (hθ : ∀ k g, θ k g Set.univ ≤ 1)
    (μ : (k : ℕ) → Fin (W k) → Measure (X × ℝ)) (hμ : ∀ k g, IsFiniteMeasure (μ k g))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) (hπ : ∀ k g, IsFiniteMeasure (π k g))
    (E : (k : ℕ) → Fin (W k) → Set (X × ℝ))
    (hE : ∀ k g, MeasurableSet (E k g) ∧
      ∀ z ∈ E k g, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a z.1 e| ≤ K k)
    (Ξ : ℕ → Finset ℝ) (hΞ : ∀ k, ∀ r ∈ Ξ k, 0 < r)
    (hcard : ∀ᶠ k in atTop, ((Ξ k).card : ℝ) ≤ L k) (d : ℝ)
    (hprior : ∀ k g, ∀ r ∈ Ξ k, ∀ z ∈ E k g,
      ENNReal.ofReal (N k ^ (-((1 + d) * r)) / Hf k) *
        π k g (scalarVelocityBin (N k ^ (-r)) ⌊a z.1 1 / N k ^ (-r)⌋) ≤
        θ k g {l | scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a l) =
          scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1)})
    (hcap : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ),
      R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (c : ℤ),
        μ k g (E k g ∩ {z | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z) = q ∧
          (⌊a z.1 1 / N k ^ (-r)⌋ : ℤ) = c}) ≤
          ENNReal.ofReal (K k * N k ^ (-((2 + d) * r))) *
            π k g (scalarVelocityBin (N k ^ (-r)) c)) :
    ∃ (H : ℕ → ℝ) (F : (k : ℕ) → Fin (W k) → Set (X × ℝ)),
      ((∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      (∀ k, Hf k ≤ H k) ∧
      (∀ k g, MeasurableSet (F k g) ∧ F k g ⊆ E k g) ∧
      (∀ᶠ k in atTop, ∀ g, μ k g (E k g \ F k g) ≤ ENNReal.ofReal (1 / (100 * K k))) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ),
        R⁻¹ ≤ r → r ≤ R → r ∈ Ξ k → ∀ (q : Fin 3 → ℤ) (c : ℤ),
          {b : Fin 5 → ℤ | (μ k g).restrict (F k g) {z |
            physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z) = q ∧
            (⌊a z.1 1 / N k ^ (-r)⌋ : ℤ) = c ∧
            scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1) = b} ≠ 0}.Finite ∧
          ({b : Fin 5 → ℤ | (μ k g).restrict (F k g) {z |
            physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z) = q ∧
            (⌊a z.1 1 / N k ^ (-r)⌋ : ℤ) = c ∧
            scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1) = b} ≠ 0}.ncard : ℝ) ≤ H k := by
  classical
  obtain ⟨P,F,hP,hF,hloss,hentry⟩ := exists_sequence_coefficient_entries N K L hN hNt hK hL
    W a ha θ hθ μ E hE Ξ hΞ hcard
  have hNp (k) : 0 < N k := by linarith [hN k]
  let H := fun k => K k * P k * Hf k
  have hH := Submission.Obl.k4_tempered_grid_selection.subpower_mul hNp
    (Submission.Obl.k4_tempered_grid_selection.subpower_mul hNp hK hP) hHf
  have hHfH (k) : Hf k ≤ H k := by
    have hp : 1 ≤ K k * P k := by
      simpa only [one_mul] using mul_le_mul (hK.1 k) (hP.1 k)
        (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans (hK.1 k))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (zero_le_one.trans (hHf.1 k))
  refine ⟨H,F,hH,hHfH,hF,hloss,?_⟩
  intro R hR
  filter_upwards [hcap R hR] with k hk
  intro g r hr hr' hrΞ q c
  letI : IsFiniteMeasure (μ k g) := hμ k g
  letI : IsFiniteMeasure (π k g) := hπ k g
  have hNpos : 0 < N k := hNp k
  have hKp : 0 < K k := zero_lt_one.trans_le (hK.1 k)
  have hPp : 0 < P k := zero_lt_one.trans_le (hP.1 k)
  have hHfp : 0 < Hf k := zero_lt_one.trans_le (hHf.1 k)
  have hcapF (q : Fin 3 → ℤ) (c : ℤ) :
      μ k g (F k g ∩ {z | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z) = q ∧
        (⌊a z.1 1 / N k ^ (-r)⌋ : ℤ) = c}) ≤
        ENNReal.ofReal (K k * N k ^ (-((2 + d) * r))) * π k g (scalarVelocityBin (N k ^ (-r)) c) :=
    (measure_mono (Set.inter_subset_inter_left _ (hF k g).2)).trans (hk g r hr hr' q c)
  have hcount := coefficient_cell_list_bound (μ k g) (θ k g) (π k g) a ha (F k g) (hF k g).1
    (N k ^ (-r)) (K k) (N k ^ (-r) / P k) (N k ^ (-((1 + d) * r)) / Hf k)
    (K k * N k ^ (-((2 + d) * r))) (Real.rpow_pos_of_pos (hNp k) _) (by positivity) (by positivity)
    (by positivity)
    (fun z hz => ((hE k g).2 z ((hF k g).2 hz)).2)
    (fun z hz => hprior k g r hrΞ z ((hF k g).2 hz))
    (fun q b => (hentry k g r hrΞ q b).imp id (fun hh => hh.le)) hcapF q c
  have hpowers : N k ^ (-r) * N k ^ (-((1 + d) * r)) = N k ^ (-((2 + d) * r)) := by
    rw [← Real.rpow_add (hNp k)]
    congr 1
    ring
  have hratio :
      (K k * N k ^ (-((2 + d) * r))) /
        ((N k ^ (-r) / P k) * (N k ^ (-((1 + d) * r)) / Hf k)) = H k := by
    rw [div_mul_div_comm,hpowers]
    dsimp only [H]
    field_simp [hPp.ne',hHfp.ne',(Real.rpow_pos_of_pos (hNp k) (-((2 + d) * r))).ne']
    <;> ring
  rw [hratio] at hcount
  have hmphys : Measurable (fun z : X × ℝ => physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z)) := by
    apply Measurable.of_eval
    intro e
    dsimp only [physicalScalarGridTag]
    have hh := measurable_scalarPacketPosition ha
    fun_prop
  have hmcoeff : Measurable (fun z : X × ℝ =>
      scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1)) :=
    (measurable_scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r))).comp
      (ha.comp measurable_fst)
  have hmvel : Measurable (fun z : X × ℝ => (⌊a z.1 1 / N k ^ (-r)⌋ : ℤ)) := by fun_prop
  have hcell (b : Fin 5 → ℤ) : MeasurableSet {z : X × ℝ |
      physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z) = q ∧
      (⌊a z.1 1 / N k ^ (-r)⌋ : ℤ) = c ∧
      scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1) = b} :=
    (measurableSet_eq_fun hmphys measurable_const).inter
      ((measurableSet_eq_fun hmvel measurable_const).inter (measurableSet_eq_fun hmcoeff measurable_const))
  simpa only [Measure.restrict_apply (hcell _),Set.inter_comm] using hcount

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
