-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/JetFit/Chart.lean.
-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/JetFit/SlicedMass.lean.
-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/JetFit/BlockFit.lean.
-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/JetFit/RowFitNumerics.lean.
import Mathlib

namespace Submission.Obl.k4_fixed_prior_chart_regularization.JetFit
open MeasureTheory Set Filter
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

theorem floor_window {a x q : ℝ} {n : ℕ} (hq : 0 < q) (h1 : a ≤ x) (h2 : x ≤ a + n * q) :
    ⌊x / q⌋ ∈ Finset.Icc ⌊a / q⌋ (⌊a / q⌋ + n) := by
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right h1 hq.le)
  · have : x / q ≤ a / q + n := by
      rw [div_add' _ _ _ hq.ne', div_le_div_iff_of_pos_right hq]; linarith
    calc ⌊x / q⌋ ≤ ⌊a / q + n⌋ := Int.floor_le_floor this
      _ = ⌊a / q⌋ + n := by exact_mod_cast Int.floor_add_natCast (a / q) n

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

theorem exists_heavy_time (ν : Measure Ω) [IsFiniteMeasure ν] {S : Set (Ω × ℝ)}
    (hS : MeasurableSet S) {a b : ℝ} (hab : a < b) (hSab : ∀ q ∈ S, q.2 ∈ Icc a b) :
    ∃ t₀ ∈ Icc a b, ((ν.prod volume) S) ^ 2 ≤
      ENNReal.ofReal (b - a) * ν univ * (ν.prod volume) (S ∩ {q | (q.1, t₀) ∈ S}) := by
  set g : Ω → ENNReal := fun l => volume (Prod.mk l ⁻¹' S) with hgdef
  have hg : Measurable g := measurable_measure_prodMk_left hS
  set f : ℝ → ENNReal := fun t₀ => (ν.prod volume) (S ∩ {q | (q.1, t₀) ∈ S}) with hfdef
  have hEu : ∀ t₀ : ℝ, MeasurableSet {q : Ω × ℝ | (q.1, t₀) ∈ S} :=
    fun t₀ => (measurable_fst.prodMk measurable_const) hS
  have hf_eq : ∀ t₀, f t₀ = ∫⁻ l, S.indicator (fun _ => (1:ENNReal)) (l, t₀) * g l ∂ν := by
    intro t₀
    simp only [hfdef]
    rw [Measure.prod_apply (hS.inter (hEu t₀))]
    apply lintegral_congr; intro l
    by_cases hl : (l, t₀) ∈ S
    · have : Prod.mk l ⁻¹' (S ∩ {q | (q.1, t₀) ∈ S}) = Prod.mk l ⁻¹' S := by
        ext u; simp [hl]
      rw [this, indicator_of_mem hl, one_mul]
    · have : Prod.mk l ⁻¹' (S ∩ {q | (q.1, t₀) ∈ S}) = ∅ := by
        ext u; simp [hl]
      rw [this, measure_empty, indicator_of_notMem hl, zero_mul]
  have hjoint : Measurable (fun x : ℝ × Ω => S.indicator (fun _ => (1:ENNReal)) (x.2, x.1) * g x.2) :=
    ((measurable_const.indicator hS).comp (measurable_snd.prodMk measurable_fst)).mul
      (hg.comp measurable_snd)
  set μab : Measure ℝ := volume.restrict (Icc a b) with hμab
  have hint : ∫⁻ t₀, f t₀ ∂μab = ∫⁻ l, g l ^ 2 ∂ν := by
    simp_rw [hf_eq]
    rw [lintegral_lintegral_swap (hjoint.aemeasurable)]
    apply lintegral_congr; intro l
    have hmeas : Measurable (fun t₀ => S.indicator (fun _ => (1:ENNReal)) (l, t₀)) :=
      (measurable_const.indicator hS).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_mul_const _ hmeas]
    have hind : (fun t₀ => S.indicator (fun _ => (1:ENNReal)) (l, t₀)) =
        (Prod.mk l ⁻¹' S).indicator (fun _ => 1) := by
      ext t₀; by_cases h : (l, t₀) ∈ S
      · rw [indicator_of_mem h, indicator_of_mem (show t₀ ∈ Prod.mk l ⁻¹' S from h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (show t₀ ∉ Prod.mk l ⁻¹' S from h)]
    rw [hind, lintegral_indicator (measurable_prodMk_left hS), setLIntegral_const, one_mul,
      Measure.restrict_apply (measurable_prodMk_left hS)]
    have : Prod.mk l ⁻¹' S ∩ Icc a b = Prod.mk l ⁻¹' S := by
      ext u; simp only [mem_inter_iff, mem_preimage, and_iff_left_iff_imp]
      exact fun h => hSab _ h
    rw [this, sq]
  have hmass : (ν.prod volume) S = ∫⁻ l, g l ∂ν := Measure.prod_apply hS
  have hCS := sq_lintegral_le_mul ν hg.aemeasurable
  -- normalized averaging on `[a,b]`
  set μn : Measure ℝ := ENNReal.ofReal (1 / (b - a)) • μab with hμn
  have hba : 0 < b - a := by linarith
  have hprob : IsProbabilityMeasure μn := by
    constructor
    rw [hμn, Measure.smul_apply, hμab, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
    rw [show 1 / (b - a) * (b - a) = 1 by field_simp]; simp
  have hfin : ∫⁻ t₀, f t₀ ∂μn ≠ ⊤ := by
    rw [hμn, lintegral_smul_measure, hint]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    refine ne_top_of_le_ne_top (b := ∫⁻ _l, (ENNReal.ofReal (b - a)) ^ 2 ∂ν) (by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)) ?_
    apply lintegral_mono; intro l
    show g l ^ 2 ≤ (ENNReal.ofReal (b - a)) ^ 2
    have : g l ≤ ENNReal.ofReal (b - a) := by
      calc g l = volume (Prod.mk l ⁻¹' S) := rfl
        _ ≤ volume (Icc a b) := measure_mono (fun u hu => hSab _ hu)
        _ = ENNReal.ofReal (b - a) := Real.volume_Icc
    gcongr
  have hpos := measure_lintegral_le_pos (μ := μn) hfin
  obtain ⟨t₀, ht₀, hle⟩ : ∃ t₀, t₀ ∈ Icc a b ∧ ∫⁻ u, f u ∂μn ≤ f t₀ := by
    by_contra hcon
    push Not at hcon
    have : μn {x | ∫⁻ a, f a ∂μn ≤ f x} = 0 := by
      rw [hμn, Measure.smul_apply, hμab, Measure.restrict_apply' measurableSet_Icc]
      have : {x | ∫⁻ a, f a ∂μn ≤ f x} ∩ Icc a b = ∅ := by
        ext x; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro h1 h2; exact absurd h1 (not_le.2 (hcon x h2))
      rw [this, measure_empty, smul_zero]
    rw [this] at hpos; exact lt_irrefl _ hpos
  refine ⟨t₀, ht₀, ?_⟩
  -- assemble
  have hav : ∫⁻ u, f u ∂μn = ENNReal.ofReal (1 / (b - a)) * ∫⁻ l, g l ^ 2 ∂ν := by
    rw [hμn, lintegral_smul_measure, hint, smul_eq_mul]
  rw [hav] at hle
  calc ((ν.prod volume) S) ^ 2 = (∫⁻ l, g l ∂ν) ^ 2 := by rw [hmass]
    _ ≤ ν univ * ∫⁻ l, g l ^ 2 ∂ν := hCS
    _ = ENNReal.ofReal (b - a) * ν univ * (ENNReal.ofReal (1 / (b - a)) * ∫⁻ l, g l ^ 2 ∂ν) := by
        rw [mul_comm (ENNReal.ofReal (b - a)) (ν univ), mul_assoc, ← mul_assoc (ENNReal.ofReal (b - a)),
          ← ENNReal.ofReal_mul hba.le, show (b - a) * (1 / (b - a)) = 1 by field_simp,
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (b - a) * ν univ * f t₀ := by gcongr


theorem eventually_mul_rpow_le (C : ℝ) {x y : ℝ} (hxy : x < y) :
    ∀ᶠ N : ℝ in atTop, C * N ^ x ≤ N ^ y := by
  have h := tendsto_rpow_atTop (sub_pos.2 hxy)
  filter_upwards [h.eventually_ge_atTop C, eventually_gt_atTop 0] with N hN hN0
  calc C * N ^ x ≤ N ^ (y - x) * N ^ x :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = N ^ y := by rw [← Real.rpow_add hN0]; ring_nf

theorem rpow_mul_nat {N : ℝ} (hN : 0 < N) (a : ℝ) (n : ℕ) : (N ^ a) ^ n = N ^ (n * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; ring_nf


end
end Submission.Obl.k4_fixed_prior_chart_regularization.JetFit
