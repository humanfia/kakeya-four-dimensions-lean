import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Sliced

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit: collision mass

Steps of "Fitting one row component" (paper Proposition 5.4) before the planar input:
the starting time `u₀`, the pair weights at a time and in a `(u, v, v')` cell.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

/-- Cauchy–Schwarz: `(∫ g)² ≤ μ(univ) ∫ g²`. -/
theorem sq_lintegral_le_mul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {g : X → ENNReal} (hg : AEMeasurable g μ) : (∫⁻ x, g x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, g x ^ 2 ∂μ := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have h3 : (∫⁻ x, g x ∂μ) ^ (2:ℝ) ≤
      ((∫⁻ x, g x ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) * μ univ ^ (1 / (2:ℝ))) ^ (2:ℝ) :=
    ENNReal.rpow_le_rpow h (by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h3
  norm_num at h3
  have e : ∀ y : ENNReal, y ^ (2:ℝ) = y ^ (2:ℕ) := fun y => by
    rw [← ENNReal.rpow_natCast]; norm_num
  rw [mul_comm]
  simpa [e] using h3

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Choice of the starting time `u₀`: the labeled mass of trajectories labeled at `u₀` is at
least `1/K³`. -/
theorem exists_start_time {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hK : 1 ≤ K) :
    ∃ u₀ ∈ Icc (0:ℝ) 1, ENNReal.ofReal (1 / K ^ 3) ≤
      (D.ν.prod volume) (D.E ∩ {q | (q.1, u₀) ∈ D.E}) := by
  have := H.finite
  have hE := H.measE
  set g : Ω → ENNReal := fun l => volume (Prod.mk l ⁻¹' D.E) with hgdef
  have hg : Measurable g := measurable_measure_prodMk_left hE
  set f : ℝ → ENNReal := fun u₀ => (D.ν.prod volume) (D.E ∩ {q | (q.1, u₀) ∈ D.E}) with hfdef
  have hEu : ∀ u₀ : ℝ, MeasurableSet {q : Ω × ℝ | (q.1, u₀) ∈ D.E} :=
    fun u₀ => (measurable_fst.prodMk measurable_const) hE
  have hf_eq : ∀ u₀, f u₀ = ∫⁻ l, D.E.indicator (fun _ => (1:ENNReal)) (l, u₀) * g l ∂D.ν := by
    intro u₀
    simp only [hfdef]
    rw [Measure.prod_apply (hE.inter (hEu u₀))]
    apply lintegral_congr; intro l
    by_cases hl : (l, u₀) ∈ D.E
    · have : Prod.mk l ⁻¹' (D.E ∩ {q | (q.1, u₀) ∈ D.E}) = Prod.mk l ⁻¹' D.E := by
        ext u; simp [hl]
      rw [this, indicator_of_mem hl, one_mul]
    · have : Prod.mk l ⁻¹' (D.E ∩ {q | (q.1, u₀) ∈ D.E}) = ∅ := by
        ext u; simp [hl]
      rw [this, measure_empty, indicator_of_notMem hl, zero_mul]
  have hjoint : Measurable (fun x : ℝ × Ω => D.E.indicator (fun _ => (1:ENNReal)) (x.2, x.1) * g x.2) :=
    ((measurable_const.indicator hE).comp (measurable_snd.prodMk measurable_fst)).mul
      (hg.comp measurable_snd)
  set μ01 : Measure ℝ := volume.restrict (Icc (0:ℝ) 1) with hμ01
  have hprob : IsProbabilityMeasure μ01 := ⟨by simp [hμ01]⟩
  have havg : ∫⁻ u₀, f u₀ ∂μ01 = ∫⁻ l, g l ^ 2 ∂D.ν := by
    simp_rw [hf_eq]
    rw [lintegral_lintegral_swap (hjoint.aemeasurable)]
    apply lintegral_congr; intro l
    have hmeas : Measurable (fun u₀ => D.E.indicator (fun _ => (1:ENNReal)) (l, u₀)) :=
      (measurable_const.indicator hE).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_mul_const _ hmeas]
    have hind : (fun u₀ => D.E.indicator (fun _ => (1:ENNReal)) (l, u₀)) =
        (Prod.mk l ⁻¹' D.E).indicator (fun _ => 1) := by
      ext u₀; by_cases h : (l, u₀) ∈ D.E
      · rw [indicator_of_mem h, indicator_of_mem (show u₀ ∈ Prod.mk l ⁻¹' D.E from h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (show u₀ ∉ Prod.mk l ⁻¹' D.E from h)]
    rw [hind, lintegral_indicator (measurable_prodMk_left hE), setLIntegral_const, one_mul,
      Measure.restrict_apply (measurable_prodMk_left hE)]
    have : Prod.mk l ⁻¹' D.E ∩ Icc (0:ℝ) 1 = Prod.mk l ⁻¹' D.E := by
      ext u; simp only [mem_inter_iff, mem_preimage, and_iff_left_iff_imp]
      exact fun h => H.E01 _ h
    rw [this, sq]
  have hmass : ENNReal.ofReal (1 / K) ≤ ∫⁻ l, g l ∂D.ν := by
    have := H.mass; rwa [Measure.prod_apply hE] at this
  have hCS := sq_lintegral_le_mul D.ν hg.aemeasurable
  have hlow : ENNReal.ofReal (1 / K ^ 3) ≤ ∫⁻ l, g l ^ 2 ∂D.ν := by
    have hK0 : 0 < K := by linarith
    have h1 : ENNReal.ofReal (1 / K) ^ 2 ≤ ENNReal.ofReal K * ∫⁻ l, g l ^ 2 ∂D.ν :=
      (pow_le_pow_left₀ bot_le hmass 2).trans (hCS.trans (by gcongr; exact H.mass_le))
    rw [← ENNReal.ofReal_pow (by positivity)] at h1
    have h2 : ENNReal.ofReal ((1 / K) ^ 2) = ENNReal.ofReal K * ENNReal.ofReal (1 / K ^ 3) := by
      rw [← ENNReal.ofReal_mul hK0.le]; congr 1; field_simp
    rw [h2] at h1
    exact (ENNReal.mul_le_mul_iff_right (by simp [hK0]) ENNReal.ofReal_ne_top).1 h1
  have hfin : ∫⁻ u₀, f u₀ ∂μ01 ≠ ⊤ := by
    rw [havg]
    refine ne_top_of_le_ne_top (b := ∫⁻ _l, (1:ENNReal) ^ 2 ∂D.ν) (by simp [measure_ne_top]) ?_
    apply lintegral_mono; intro l
    have : g l ≤ 1 := by
      calc g l = volume (Prod.mk l ⁻¹' D.E) := rfl
        _ ≤ volume (Icc (0:ℝ) 1) := measure_mono (fun u hu => H.E01 _ hu)
        _ = 1 := by simp
    show g l ^ 2 ≤ 1 ^ 2
    gcongr
  have hpos := measure_lintegral_le_pos (μ := μ01) hfin
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ ∈ Icc (0:ℝ) 1 ∧ ∫⁻ u, f u ∂μ01 ≤ f u₀ := by
    by_contra hcon
    push Not at hcon
    have : μ01 {x | ∫⁻ a, f a ∂μ01 ≤ f x} = 0 := by
      rw [hμ01, Measure.restrict_apply' measurableSet_Icc]
      convert measure_empty (μ := volume)
      ext x; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; exact absurd h1 (not_le.2 (hcon x h2))
    rw [this] at hpos; exact lt_irrefl _ hpos
  exact ⟨u₀, hu₀.1, hlow.trans (havg ▸ hu₀.2)⟩

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
