import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.FrameData
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.OriginalSupport

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Data.ListFrame

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {r v m ε : ℝ}
    (f : ListFrame cfg k r v m ε)

/-- The time map from normalized block time to original time. -/
def frameMap : α × ℝ → α × ℝ := fun p => (p.1, f.t₀ + f.q * p.2)

theorem measurable_frameMap : Measurable f.frameMap :=
  measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))

/-- The original reference factor of the frame. -/
def weight : ℝ≥0∞ := ENNReal.ofReal f.q * cfg.ν k (cfg.A k r f.parent)

theorem map_le (hρμ : cfg.ρ k ≤ cfg.μ k) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤) :
    f.law.map f.frameMap ≤ f.weight⁻¹ • cfg.μ k := by
  rw [Measure.le_iff']
  intro s
  have hd := Measure.le_iff'.mp (f.original_domination.trans hρμ) s
  rw [Measure.smul_apply, smul_eq_mul] at hd ⊢
  calc (f.law.map f.frameMap) s = f.weight⁻¹ * (f.weight * (f.law.map f.frameMap) s) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ ≤ f.weight⁻¹ * cfg.μ k s := by
        gcongr
        exact hd

/-- Almost-sure facts about original incidences hold on the frame. -/
theorem ae_of_original (hρμ : cfg.ρ k ≤ cfg.μ k) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤)
    {P : α × ℝ → Prop} (hP : ∀ᵐ p ∂cfg.μ k, P p) :
    ∀ᵐ p ∂f.law, P (p.1, f.t₀ + f.q * p.2) := by
  have hac : f.law.map f.frameMap ≪ cfg.μ k :=
    Measure.absolutelyContinuous_of_le_smul (f.map_le hρμ h0 ht)
  exact ae_of_ae_map f.measurable_frameMap.aemeasurable (hac.ae_le hP)

/-- Original measures of measurable events bound their frame pullbacks. -/
theorem law_preimage_le (hρμ : cfg.ρ k ≤ cfg.μ k) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    f.law (f.frameMap ⁻¹' E) ≤ f.weight⁻¹ * cfg.μ k E := by
  rw [← Measure.map_apply f.measurable_frameMap hE]
  have h := Measure.le_iff'.mp (f.map_le hρμ h0 ht) E
  rwa [Measure.smul_apply, smul_eq_mul] at h

theorem law_univ_le : f.law univ ≤ ENNReal.ofReal (cfg.N k ^ ε) := by
  calc f.law univ ≤ f.law ((univ : Set α) ×ˢ Icc (0 : ℝ) 1) +
        f.law ((univ : Set α) ×ˢ Icc (0 : ℝ) 1)ᶜ := measure_univ_le_add_compl _
    _ = f.law ((univ : Set α) ×ˢ Icc (0 : ℝ) 1) := by rw [f.time_support, add_zero]
    _ ≤ (ENNReal.ofReal (cfg.N k ^ ε) • (f.prior.prod volume))
          ((univ : Set α) ×ˢ Icc (0 : ℝ) 1) := f.law_domination _
    _ = ENNReal.ofReal (cfg.N k ^ ε) := by
        have := f.prior_probability
        rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, measure_univ,
          Real.volume_Icc, sub_zero, ENNReal.ofReal_one, one_mul, mul_one]

theorem isFiniteMeasure_law : IsFiniteMeasure f.law :=
  ⟨lt_of_le_of_lt f.law_univ_le ENNReal.ofReal_lt_top⟩

/-- Countably many normalized times carry no frame mass. -/
theorem law_time_countable_null {Z : Set ℝ} (hZ : Z.Countable) :
    f.law {p | p.2 ∈ Z} = 0 := by
  apply le_antisymm _ zero_le
  have hset : {p : α × ℝ | p.2 ∈ Z} = (univ : Set α) ×ˢ Z := by
    ext p; simp
  calc f.law {p | p.2 ∈ Z} ≤ (ENNReal.ofReal (cfg.N k ^ ε) • (f.prior.prod volume))
        {p | p.2 ∈ Z} := f.law_domination _
    _ = 0 := by
        rw [hset, Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
          hZ.measure_zero, mul_zero, mul_zero]

end Data.ListFrame

/-- Floors of nearby values at the same mesh differ by at most one. -/
theorem floor_div_near {x y σ : ℝ} (hσ : 0 < σ) (hxy : |x - y| ≤ σ) :
    ⌊y / σ⌋ - 1 ≤ ⌊x / σ⌋ ∧ ⌊x / σ⌋ ≤ ⌊y / σ⌋ + 1 := by
  have h1 : x / σ ≤ y / σ + 1 := by
    rw [div_add_one hσ.ne', div_le_div_iff_of_pos_right hσ]
    linarith [(abs_le.mp hxy).2]
  have h2 : y / σ ≤ x / σ + 1 := by
    rw [div_add_one hσ.ne', div_le_div_iff_of_pos_right hσ]
    linarith [(abs_le.mp hxy).1]
  constructor
  · have := Int.floor_mono h2
    rw [Int.floor_add_one] at this
    linarith
  · have := Int.floor_mono h1
    rwa [Int.floor_add_one] at this

/-- The output states within one step of a given one in each coordinate. -/
def stateBox (o : (Fin 2 → ℤ) × ℤ) : Finset ((Fin 2 → ℤ) × ℤ) :=
  (Fintype.piFinset fun e => Finset.Icc (o.1 e - 1) (o.1 e + 1)) ×ˢ
    Finset.Icc (o.2 - 1) (o.2 + 1)

theorem card_stateBox (o : (Fin 2 → ℤ) × ℤ) : (stateBox o).card = 27 := by
  simp only [stateBox, Finset.card_product, Fintype.card_piFinset, Int.card_Icc,
    Fin.prod_univ_two]
  have h : ∀ z : ℤ, (z + 1 + 1 - (z - 1)).toNat = 3 := by intro z; omega
  rw [h, h, h]
  norm_num

theorem mem_stateBox {o o' : (Fin 2 → ℤ) × ℤ}
    (h1 : ∀ e, o.1 e - 1 ≤ o'.1 e ∧ o'.1 e ≤ o.1 e + 1)
    (h2 : o.2 - 1 ≤ o'.2 ∧ o'.2 ≤ o.2 + 1) : o' ∈ stateBox o := by
  simp only [stateBox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc]
  exact ⟨h1, h2⟩

/-- Half-open dyadic pieces of one level are disjoint. -/
theorem dyadic_Ico_disjoint {T a b : ℕ} (hab : a ≠ b) :
    Disjoint (Ico ((a : ℝ) / 2 ^ T) (((a : ℝ) + 1) / 2 ^ T))
      (Ico ((b : ℝ) / 2 ^ T) (((b : ℝ) + 1) / 2 ^ T)) := by
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · have h' : ((a : ℝ) + 1) / 2 ^ T ≤ (b : ℝ) / 2 ^ T := by
      apply div_le_div_of_nonneg_right _ hT.le
      exact_mod_cast h
    exact Set.disjoint_left.mpr fun t ht ht' => absurd (ht.2.trans_le h') (not_lt.mpr ht'.1)
  · have h' : ((b : ℝ) + 1) / 2 ^ T ≤ (a : ℝ) / 2 ^ T := by
      apply div_le_div_of_nonneg_right _ hT.le
      exact_mod_cast h
    exact Set.disjoint_left.mpr fun t ht ht' => absurd (ht'.2.trans_le h') (not_lt.mpr ht.1)

/-- A deep half-open piece inside the dyadic interval `b` of a coarser level,
met at a time strictly before the end of the parent interval `p`, forces `b = p`
whenever the trajectory classes of `b` and `p` meet. -/
theorem dyadic_parent_eq {T T' a b p : ℕ} {t t₀ q : ℝ}
    (hpar : Icc ((p : ℝ) / 2 ^ T) (((p : ℝ) + 1) / 2 ^ T) = Icc t₀ (t₀ + q)) (hq : 0 < q)
    (ht0 : t₀ ≤ t) (ht1 : t < t₀ + q)
    (hta : t ∈ Ico ((a : ℝ) / 2 ^ T') (((a : ℝ) + 1) / 2 ^ T'))
    (hsub : Icc ((a : ℝ) / 2 ^ T') (((a : ℝ) + 1) / 2 ^ T') ⊆
      Icc ((b : ℝ) / 2 ^ T) (((b : ℝ) + 1) / 2 ^ T)) : b = p := by
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  have hT' : (0 : ℝ) < 2 ^ T' := by positivity
  have haa : (a : ℝ) / 2 ^ T' ≤ ((a : ℝ) + 1) / 2 ^ T' :=
    div_le_div_of_nonneg_right (by linarith) hT'.le
  have hl := hsub ⟨le_rfl, haa⟩
  have hr := hsub ⟨haa, le_rfl⟩
  have hpq : t₀ ≤ t₀ + q := by linarith
  have hp1 : (p : ℝ) / 2 ^ T ∈ Icc t₀ (t₀ + q) := by
    rw [← hpar]; exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hT.le⟩
  have hp2 : ((p : ℝ) + 1) / 2 ^ T ∈ Icc t₀ (t₀ + q) := by
    rw [← hpar]; exact ⟨div_le_div_of_nonneg_right (by linarith) hT.le, le_rfl⟩
  have hq1 : t₀ ∈ Icc ((p : ℝ) / 2 ^ T) (((p : ℝ) + 1) / 2 ^ T) := by
    rw [hpar]; exact ⟨le_rfl, hpq⟩
  have hq2 : t₀ + q ∈ Icc ((p : ℝ) / 2 ^ T) (((p : ℝ) + 1) / 2 ^ T) := by
    rw [hpar]; exact ⟨hpq, le_rfl⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h' : ((b : ℝ) + 1) / 2 ^ T ≤ (p : ℝ) / 2 ^ T := by
      apply div_le_div_of_nonneg_right _ hT.le
      exact_mod_cast h
    have := hta.2
    linarith [hr.2, hq1.1]
  · have h' : ((p : ℝ) + 1) / 2 ^ T ≤ (b : ℝ) / 2 ^ T := by
      apply div_le_div_of_nonneg_right _ hT.le
      exact_mod_cast h
    have := hta.1
    linarith [hl.1, hq2.2]

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
