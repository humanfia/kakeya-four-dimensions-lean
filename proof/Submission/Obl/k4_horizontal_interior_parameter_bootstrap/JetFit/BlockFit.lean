import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Block

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# Fitting one row component on a block

* `prod_time_rescale`, `exists_heavy_time`: time rescaling in `ν ⊗ dt` and the averaging choice
  of a common time (paper: "Averaging and Cauchy–Schwarz provide `u_*`");
* `data_mass_eq`, `exists_heavy_group`: the groups of lines labeled at `tS` (an `H`-bin of `B` by
  the support count at `tS`, a `p`-slice of `y₁`) are at most `224K⁵/(H^d p)` in number, so one
  has normalized labeled mass `≥ m/(224K⁵)` ("deletion of light groups");
* `block_fit`: the block model satisfies the sliced hypotheses, `sliced_fit` applies, and in
  original time `F₀` is within `H(12Ks+2)p + Kζ` of an affine function on active times of measure
  `≥ H p^ε/(5C₀K₁)` (paper: "In the original variables this is an affine component fit to `F`
  with error `KH^{5/4}` on `T_I`").
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Rescaling time in a product with Lebesgue measure. -/
theorem prod_time_rescale (ν : Measure Ω) [SFinite ν] {S : Set (Ω × ℝ)} (hS : MeasurableSet S)
    (tI H : ℝ) (hH : 0 < H) :
    (ν.prod volume) {q : Ω × ℝ | (q.1, tI + H * q.2) ∈ S} =
      ENNReal.ofReal (1 / H) * (ν.prod volume) S := by
  have hS' : MeasurableSet {q : Ω × ℝ | (q.1, tI + H * q.2) ∈ S} :=
    (measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))) hS
  rw [Measure.prod_apply hS', Measure.prod_apply hS, ← lintegral_const_mul _
    (measurable_measure_prodMk_left hS)]
  apply lintegral_congr
  intro l
  have : Prod.mk l ⁻¹' {q : Ω × ℝ | (q.1, tI + H * q.2) ∈ S} =
      (fun u => H * u) ⁻¹' ((fun u => tI + u) ⁻¹' (Prod.mk l ⁻¹' S)) := by
    ext u; simp
  rw [this, Real.volume_preimage_mul_left hH.ne', measure_preimage_add, abs_inv,
    abs_of_pos hH, one_div]

/-- Cauchy–Schwarz: `(∫ g)² ≤ μ(univ) ∫ g²`. -/
theorem sq_lintegral_le_mul' {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {g : X → ENNReal} (hg : AEMeasurable g μ) : (∫⁻ x, g x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, g x ^ 2 ∂μ :=
  sq_lintegral_le_mul μ hg

/-- **A heavy common time**: some time `t₀ ∈ [a,b]` has
`(ν⊗dt)(S)² ≤ (b-a) ν(Ω) (ν⊗dt)(S ∩ {lines labeled at t₀})`. -/
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


/-- The normalized mass of a block group. -/
theorem data_mass_eq {D : JetData Ω} {E : Set (Ω × ℝ)} {tI H p tS : ℝ} {b c : ℤ} {K d ζ : ℝ}
    (hD : JetHyp D ζ K d) (hEm : MeasurableSet E) :
    ((Block.data D E tI H p tS b c K d).ν.prod volume) (Block.data D E tI H p tS b c K d).E =
      ENNReal.ofReal (1 / (H ^ d * p)) * (D.ν.prod volume)
        {q : Ω × ℝ | q.1 ∈ Block.grp D E tI H p tS b c ∧ (q.1, tI + H * q.2) ∈ E ∧
          q.2 ∈ Icc (0:ℝ) 1} := by
  have := hD.prob
  have hgm := Block.measurableSet_grp (tI := tI) (H := H) (p := p) (tS := tS) (b := b) (c := c) hD hEm
  show (((1 / (H ^ d * p)).toNNReal • D.ν.restrict (Block.grp D E tI H p tS b c)).prod volume)
    {q : Ω × ℝ | q.1 ∈ Block.grp D E tI H p tS b c ∧ (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1} = _
  rw [Measure.prod_smul_left, Measure.smul_apply]
  rw [show (D.ν.restrict (Block.grp D E tI H p tS b c)).prod volume =
    (D.ν.restrict (Block.grp D E tI H p tS b c)).prod (volume.restrict univ) by rw [Measure.restrict_univ],
    Measure.prod_restrict, Measure.restrict_apply' (hgm.prod MeasurableSet.univ)]
  have : {q : Ω × ℝ | q.1 ∈ Block.grp D E tI H p tS b c ∧ (q.1, tI + H * q.2) ∈ E ∧
      q.2 ∈ Icc (0:ℝ) 1} ∩ Block.grp D E tI H p tS b c ×ˢ univ =
      {q : Ω × ℝ | q.1 ∈ Block.grp D E tI H p tS b c ∧ (q.1, tI + H * q.2) ∈ E ∧
        q.2 ∈ Icc (0:ℝ) 1} := by
    ext q; simp only [mem_inter_iff, mem_prod, mem_univ, and_true, and_iff_left_iff_imp]
    exact fun h => h.1
  rw [this, ENNReal.smul_def, smul_eq_mul]
  rfl

/-- The normal scalars are bounded by `4K²` at labeled times. -/
theorem abs_S_le {D : JetData Ω} {ζ K d : ℝ} (hD : JetHyp D ζ K d) (hK : 1 ≤ K) {l : Ω} {t : ℝ}
    (h : (l, t) ∈ D.E) : |D.S l t| ≤ 4 * K ^ 2 := by
  have ht := hD.E01 _ h
  simp only at ht
  have hx := hD.bound_x l
  have hy0 := hD.bound_y l 0
  have hy1 := hD.bound_y l 1
  have hF0 := hD.bound_F t 0
  have hF1 := hD.bound_F t 1
  have ht1 : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  simp only [JetData.S, JetData.xb, JetData.Fy]
  have a1 : |t * D.x1 l| ≤ |D.x1 l| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht1
  have a2 : |D.F t 0 * D.y l 0| ≤ K * K := by
    rw [abs_mul]; exact mul_le_mul hF0 hy0 (abs_nonneg _) (by linarith)
  have a3 : |D.F t 1 * D.y l 1| ≤ K * K := by
    rw [abs_mul]; exact mul_le_mul hF1 hy1 (abs_nonneg _) (by linarith)
  have t1 := abs_add_le (D.x0 l) (t * D.x1 l)
  have t2 := abs_add_le (D.F t 0 * D.y l 0) (D.F t 1 * D.y l 1)
  have t3 := abs_sub (D.x0 l + t * D.x1 l) (D.F t 0 * D.y l 0 + D.F t 1 * D.y l 1)
  nlinarith

/-- **A heavy group**: among the groups of lines labeled at `tS`, one carries normalized labeled
mass at least `m/(224 K⁵)`, where `m` is the labeled block mass (normalized time) of all lines
labeled at `tS`. -/
theorem exists_heavy_group {D : JetData Ω} {E : Set (Ω × ℝ)} {tI H p tS : ℝ} {K d ζ : ℝ}
    (hD : JetHyp D ζ K d) (hK : 1 ≤ K) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hEsub : E ⊆ D.E)
    (hEm : MeasurableSet E) (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1) (hζH : ζ ≤ H)
    (htS : tS ∈ Icc tI (tI + H)) (m : ℝ)
    (hm : ENNReal.ofReal m ≤ (D.ν.prod volume)
      {q : Ω × ℝ | (q.1, tS) ∈ E ∧ (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1}) :
    ∃ b c : ℤ, ENNReal.ofReal (m / (224 * K ^ 5)) ≤
      ((Block.data D E tI H p tS b c K d).ν.prod volume) (Block.data D E tI H p tS b c K d).E := by
  classical
  have hK0 : 0 < K := by linarith
  have := hD.prob
  -- the occupied bins of the normal scalar at `tS`
  obtain ⟨m₀, cc, hcov, hm₀⟩ := hD.supp tS (-(4 * K ^ 2)) (8 * K ^ 2) H hζH (by nlinarith)
  set n : ℕ := ⌈2 * K + 2⌉₊ with hn
  set Bset : Finset ℤ := Finset.univ.biUnion (fun j : Fin m₀ =>
    Finset.Icc ⌊(cc j - (K + 1) * H) / H⌋ (⌊(cc j - (K + 1) * H) / H⌋ + n))
  set Cset : Finset ℤ := vBins K p
  set Eall : Set (Ω × ℝ) := {q : Ω × ℝ | (q.1, tS) ∈ E ∧ (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1}
  set E' : ℤ × ℤ → Set (Ω × ℝ) := fun bc => {q : Ω × ℝ | q.1 ∈ Block.grp D E tI H p tS bc.1 bc.2 ∧
    (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1}
  have hcover : Eall ⊆ ⋃ bc ∈ Bset ×ˢ Cset, E' bc := by
    rintro ⟨l, u⟩ ⟨hl, hlu, hu⟩
    have hlD := hEsub hl
    have hS := abs_S_le hD hK hlD
    have hmem : D.S l tS ∈ {s | ∃ l, (l, tS) ∈ D.E ∧ s = D.S l tS} ∩
        Icc (-(4 * K ^ 2)) (-(4 * K ^ 2) + 8 * K ^ 2) :=
      ⟨⟨l, hlD, rfl⟩, by rw [mem_Icc]; constructor <;> linarith [(abs_le.1 hS).1, (abs_le.1 hS).2]⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov hmem)
    rw [Metric.mem_closedBall, Real.dist_eq] at hj
    have hB := Block.S_at_tS D tI tS l
    have hx1 : |D.x1 l| ≤ K := le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hD.bound_x l)
    have hxt : |(tS - tI) * D.x1 l| ≤ H * K := by
      rw [abs_mul]; exact mul_le_mul (by rw [abs_le]; constructor <;> linarith [htS.1, htS.2]) hx1
        (abs_nonneg _) hH.le
    have hbwin : ⌊Block.Bv D tI tS l / H⌋ ∈
        Finset.Icc ⌊(cc j - (K + 1) * H) / H⌋ (⌊(cc j - (K + 1) * H) / H⌋ + n) := by
      apply floor_window hH
      · linarith [(abs_le.1 hj).1, (abs_le.1 hxt).2]
      · have : 2 * K + 2 ≤ (n : ℝ) := Nat.le_ceil _
        nlinarith [(abs_le.1 hj).2, (abs_le.1 hxt).1]
    refine mem_iUnion₂.2 ⟨(⌊Block.Bv D tI tS l / H⌋, ⌊D.y l 1 / p⌋), Finset.mem_product.2
      ⟨Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hbwin⟩, mem_vBins hp (hD.bound_y l 1)⟩, ?_⟩
    exact ⟨⟨hl, rfl, rfl⟩, hlu, hu⟩
  have hsum : (D.ν.prod volume) Eall ≤ ∑ bc ∈ Bset ×ˢ Cset, (D.ν.prod volume) (E' bc) :=
    (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
  -- the number of groups
  have hcardB : (Bset.card : ℝ) ≤ m₀ * (2 * K + 4) := by
    have h1 : Bset.card ≤ ∑ j : Fin m₀, (Finset.Icc ⌊(cc j - (K + 1) * H) / H⌋
        (⌊(cc j - (K + 1) * H) / H⌋ + n)).card := Finset.card_biUnion_le
    have h2 : ∀ j : Fin m₀, (Finset.Icc ⌊(cc j - (K + 1) * H) / H⌋
        (⌊(cc j - (K + 1) * H) / H⌋ + n)).card = n + 1 := by
      intro j; rw [Int.card_Icc]; omega
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h3 : ((m₀ * (n + 1) : ℕ) : ℝ) ≤ m₀ * (2 * K + 4) := by
      push_cast
      have : (n : ℝ) + 1 ≤ 2 * K + 4 := by
        have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * K + 2 by linarith); linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    exact (Nat.cast_le.2 h1).trans h3
  have hcardC : (Cset.card : ℝ) ≤ 2 * K / p + 2 := card_vBins hp hK0.le
  have hgroups : ((Bset ×ˢ Cset).card : ℝ) * (H ^ d * p) ≤ 224 * K ^ 5 := by
    rw [Finset.card_product]; push_cast
    have hHd : 0 < H ^ d := Real.rpow_pos_of_pos hH d
    have hm0 : (m₀ : ℝ) * H ^ d ≤ 8 * K ^ 3 := by
      have h8 : (8 * K ^ 2 / H) ^ d = (8 * K ^ 2) ^ d / H ^ d := Real.div_rpow (by positivity) hH.le d
      have h8' : (8 * K ^ 2) ^ d ≤ 8 * K ^ 2 := by
        calc (8 * K ^ 2) ^ d ≤ (8 * K ^ 2) ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by nlinarith) hd1
          _ = 8 * K ^ 2 := Real.rpow_one _
      have : (m₀ : ℝ) ≤ K * ((8 * K ^ 2) / H ^ d) := by
        calc (m₀ : ℝ) ≤ K * (8 * K ^ 2 / H) ^ d := hm₀
          _ = K * ((8 * K ^ 2) ^ d / H ^ d) := by rw [h8]
          _ ≤ K * ((8 * K ^ 2) / H ^ d) := by gcongr
      calc (m₀ : ℝ) * H ^ d ≤ K * ((8 * K ^ 2) / H ^ d) * H ^ d :=
            mul_le_mul_of_nonneg_right this hHd.le
        _ = 8 * K ^ 3 := by field_simp
    have hCp : (Cset.card : ℝ) * p ≤ 4 * K := by
      calc (Cset.card : ℝ) * p ≤ (2 * K / p + 2) * p := mul_le_mul_of_nonneg_right hcardC hp.le
        _ = 2 * K + 2 * p := by field_simp
        _ ≤ 4 * K := by linarith
    calc (Bset.card : ℝ) * Cset.card * (H ^ d * p) = (Bset.card : ℝ) * H ^ d * (Cset.card * p) := by
          ring
      _ ≤ (m₀ * (2 * K + 4)) * H ^ d * (4 * K) := by
          apply mul_le_mul _ hCp (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hcardB hHd.le
      _ = (m₀ * H ^ d) * (2 * K + 4) * (4 * K) := by ring
      _ ≤ (8 * K ^ 3) * (6 * K) * (4 * K) := by
          apply mul_le_mul (mul_le_mul hm0 (by linarith) (by positivity) (by positivity)) le_rfl
            (by positivity) (by positivity)
      _ ≤ 224 * K ^ 5 := by nlinarith [pow_pos hK0 5]
  -- pigeonhole
  by_cases hnonempty : (Bset ×ˢ Cset).Nonempty
  swap
  · -- no groups: the labeled mass vanishes
    rw [Finset.not_nonempty_iff_eq_empty] at hnonempty
    rw [hnonempty, Finset.sum_empty] at hsum
    refine ⟨0, 0, ?_⟩
    have : ENNReal.ofReal m = 0 := le_antisymm (hm.trans hsum) bot_le
    rw [ENNReal.ofReal_eq_zero] at this
    rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg this (by positivity))]
    exact bot_le
  obtain ⟨bc, hbc, hmax⟩ := (Bset ×ˢ Cset).exists_max_image (fun bc => (D.ν.prod volume) (E' bc))
    hnonempty
  refine ⟨bc.1, bc.2, ?_⟩
  rw [data_mass_eq hD hEm]
  have hmax' : ENNReal.ofReal m ≤ (Bset ×ˢ Cset).card * (D.ν.prod volume) (E' bc) := by
    calc ENNReal.ofReal m ≤ (D.ν.prod volume) Eall := hm
      _ ≤ ∑ bc ∈ Bset ×ˢ Cset, (D.ν.prod volume) (E' bc) := hsum
      _ ≤ ∑ _bc' ∈ Bset ×ˢ Cset, (D.ν.prod volume) (E' bc) := Finset.sum_le_sum hmax
      _ = (Bset ×ˢ Cset).card * (D.ν.prod volume) (E' bc) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- divide
  rcases le_or_gt m 0 with hm0 | hm0
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hm0 (by positivity))]; exact bot_le
  have hcard0 : 0 < ((Bset ×ˢ Cset).card : ℝ) := by exact_mod_cast hnonempty.card_pos
  have hfin : (D.ν.prod volume) (E' bc) ≠ ⊤ := by
    have : (D.ν.prod volume) (E' bc) ≤ (D.ν.prod volume) (univ ×ˢ Icc (0:ℝ) 1) :=
      measure_mono (fun q hq => ⟨trivial, hq.2.2⟩)
    refine ne_top_of_le_ne_top ?_ this
    rw [Measure.prod_prod]; exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)
  set X := (D.ν.prod volume) (E' bc) with hX
  have hXr : ENNReal.ofReal (m / (Bset ×ˢ Cset).card) ≤ X := by
    rw [← ENNReal.ofReal_toReal hfin] at hmax' ⊢
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hmax'
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmax'
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hcard0]; linarith
  calc ENNReal.ofReal (m / (224 * K ^ 5))
      ≤ ENNReal.ofReal (1 / (H ^ d * p)) * ENNReal.ofReal (m / (Bset ×ˢ Cset).card) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hHd : 0 < H ^ d * p := mul_pos (Real.rpow_pos_of_pos hH d) hp
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ ≤ ENNReal.ofReal (1 / (H ^ d * p)) * X := by gcongr

/-- `C₀` of the sliced fit. -/
def C0 (K : ℝ) : ℝ := (4 * (2 * K) + 5) * (8 * (2 * K) + 9)

set_option maxHeartbeats 4000000 in
/-- **Fitting one row component on a block** (paper Proposition 5.4, "Fitting one row component",
in original time): on a block `[tI, tI+H]` carrying labeled mass `τH`, the first row component
is within `H(12Ks+2)p + Kζ` of an affine function of slope at most `6Ks+1` on a set of active
times of measure at least `H p^ε/(5 C₀ K₁)`. -/
theorem block_fit {ε d : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) (hd1 : d < 1) (hεd : ε + d < 1) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ (p Ks : ℝ), 0 < p → p ≤ 1 → 1 ≤ Ks → p / (8 * Ks) ≤ δ₀ →
      5 * (8 * Ks + 5) ≤ (p / (8 * Ks)) ^ (-η) →
      3 * (4 * Ks) ^ 2 * (4 * Ks + 2) < (p / (8 * Ks)) ^ (-η * (1 - ε - d)) →
      27 * 179712 * Ks ^ 16 * p ^ 3 * (p / (8 * Ks)) ^ (η - 3) ≤ 1 →
      10 * ((4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9)) * (p / (8 * Ks)) ≤ (p / (8 * Ks)) ^ ε →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (D : JetData Ω) (ζ K τ H tI : ℝ) (E : Set (Ω × ℝ)),
      JetHyp D ζ K d → 1 ≤ K → 0 < τ → τ ≤ 1 → 224 * K ^ 5 / τ ^ 2 ≤ Ks → E ⊆ D.E →
      MeasurableSet E → 0 < H → H ≤ 1 → H ≤ p → 0 < ζ → ζ ≤ H * p →
      ENNReal.ofReal (τ * H) ≤ (D.ν.prod volume) (E ∩ {q | q.2 ∈ Icc tI (tI + H)}) →
      ∃ σ c : ℝ, |σ| ≤ 6 * Ks + 1 ∧ ∃ T : Set ℝ, MeasurableSet T ∧ T ⊆ Icc tI (tI + H) ∧
        (∀ t ∈ T, 0 < D.ν {l | (l, t) ∈ E}) ∧
        ENNReal.ofReal (H * (p ^ ε / (5 * C0 Ks * (36864 * Ks ^ 16)))) ≤ volume T ∧
        ∀ t ∈ T, |D.F t 0 - (c + σ * t)| ≤ H * ((12 * Ks + 2) * p) + K * ζ := by
  obtain ⟨η, δ₀, hη, hδ₀, hSF⟩ := sliced_fit hε hd hd1 hεd
  refine ⟨η, δ₀, hη, hδ₀, ?_⟩
  intro p Ks hp hp1 hKs1 hδ hA hB hDc hC Ω _ D ζ K τ H tI E hD hK hτ hτ1 hKs hEsub hEm hH hH1 hHp
    hζ0 hζ hmassB
  have hprob := hD.prob
  have hK0 : 0 < K := by linarith
  have hζH : ζ ≤ H := hζ.trans (by nlinarith)
  -- a heavy common time
  set Sb : Set (Ω × ℝ) := E ∩ {q | q.2 ∈ Icc tI (tI + H)} with hSb
  have hSbm : MeasurableSet Sb := hEm.inter (measurable_snd measurableSet_Icc)
  obtain ⟨tS, htS, hheavy⟩ := exists_heavy_time D.ν hSbm (show tI < tI + H by linarith)
    (fun q hq => hq.2)
  rw [measure_univ, mul_one, add_sub_cancel_left] at hheavy
  set X := (D.ν.prod volume) (Sb ∩ {q | (q.1, tS) ∈ Sb}) with hX
  have hXlow : ENNReal.ofReal (τ ^ 2 * H) ≤ X := by
    have h1 : ENNReal.ofReal (τ * H) ^ 2 ≤ ENNReal.ofReal H * X :=
      (pow_le_pow_left₀ bot_le hmassB 2).trans hheavy
    rw [← ENNReal.ofReal_pow (by positivity)] at h1
    have h2 : (τ * H) ^ 2 = H * (τ ^ 2 * H) := by ring
    rw [h2, ENNReal.ofReal_mul hH.le] at h1
    exact (ENNReal.mul_le_mul_iff_right (by simp [hH]) ENNReal.ofReal_ne_top).1 h1
  -- in normalized time
  have hnorm : ENNReal.ofReal (τ ^ 2) ≤ (D.ν.prod volume)
      {q : Ω × ℝ | (q.1, tS) ∈ E ∧ (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1} := by
    have hset : {q : Ω × ℝ | (q.1, tS) ∈ E ∧ (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1} =
        {q : Ω × ℝ | (q.1, tI + H * q.2) ∈ Sb ∩ {q | (q.1, tS) ∈ Sb}} := by
      ext ⟨l, u⟩
      simp only [hSb, mem_ofPred_eq, mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨h2, by nlinarith, by nlinarith⟩, h1, htS.1, htS.2⟩
      · rintro ⟨⟨h2, h3, h4⟩, h1, -⟩
        refine ⟨h1, h2, ?_, ?_⟩
        · by_contra hc; push Not at hc; nlinarith
        · by_contra hc; push Not at hc; nlinarith
    have hSm2 : MeasurableSet (Sb ∩ {q : Ω × ℝ | (q.1, tS) ∈ Sb}) :=
      hSbm.inter ((measurable_fst.prodMk measurable_const) hSbm)
    rw [hset, prod_time_rescale (S := Sb ∩ {q : Ω × ℝ | (q.1, tS) ∈ Sb}) D.ν hSm2 tI H hH]
    calc ENNReal.ofReal (τ ^ 2) = ENNReal.ofReal (1 / H) * ENNReal.ofReal (τ ^ 2 * H) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
      _ ≤ ENNReal.ofReal (1 / H) * X := by gcongr
  -- a heavy group
  obtain ⟨b, c, hgrpmass⟩ := exists_heavy_group hD hK hd hd1.le hEsub hEm hH hH1 hp hp1 hζH
    (tI := tI) (tS := tS) (by rw [mem_Icc] at htS ⊢; exact htS) (τ ^ 2) hnorm
  have hmassKs : ENNReal.ofReal (1 / Ks) ≤
      ((Block.data D E tI H p tS b c K d).ν.prod volume) (Block.data D E tI H p tS b c K d).E := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hgrpmass
    have h1 : 224 * K ^ 5 ≤ Ks * τ ^ 2 := by rwa [div_le_iff₀ (by positivity)] at hKs
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    linarith
  -- nonemptiness of the group and of its labeled times
  have hpos : 0 < ((Block.data D E tI H p tS b c K d).ν.prod volume)
      (Block.data D E tI H p tS b c K d).E :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hmassKs
  obtain ⟨⟨l₀, u₀⟩, hq₀⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hgrp : (Block.grp D E tI H p tS b c).Nonempty := ⟨l₀, hq₀.1⟩
  have hlam : (Block.lamS D E tI H p tS b c).Nonempty := ⟨u₀, hq₀.2.2, l₀, hq₀.1, hq₀.2.1⟩
  have h200 : 200 * K ^ 3 ≤ Ks := by
    refine le_trans ?_ hKs
    rw [le_div_iff₀ (by positivity)]
    have h1 : τ ^ 2 ≤ 1 := by nlinarith
    have h2 : 200 * K ^ 3 * τ ^ 2 ≤ 200 * K ^ 3 := by nlinarith [pow_pos hK0 3]
    have h3 : K ^ 3 ≤ K ^ 5 := pow_le_pow_right₀ hK (by norm_num)
    have h4 : 0 ≤ K ^ 5 := by positivity
    linarith
  have hSH := Block.data_hyp hD hK hd hEsub hEm hH hH1 hHp hp1 hζ0 hζ
    (by rw [mem_Icc] at htS ⊢; exact htS) hgrp hlam Ks h200 hmassKs
  -- the sliced fit
  obtain ⟨σ, c', hσ, T, hTm, hTact, hTvol, hTfit⟩ :=
    hSF p Ks hp hp1 hKs1 hδ hA hB hDc hC (Block.data D E tI H p tS b c K d) hSH
  -- back to original time
  set T' : Set ℝ := (fun t => (t - tI) / H) ⁻¹' T with hT'
  have hmeasT' : MeasurableSet T' :=
    ((measurable_id.sub measurable_const).div_const H) hTm
  refine ⟨σ, D.F tS 0 + H * c' - σ * tI, hσ, T', hmeasT', ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hu := actSet_sub hSH (hTact ht)
    rw [mem_Icc] at hu ⊢
    constructor
    · have := hu.1; rw [le_div_iff₀ hH] at this; linarith
    · have := hu.2; rw [div_le_iff₀ hH] at this; linarith
  · intro t ht
    have hact := hTact ht
    have hpos' : 0 < (Block.data D E tI H p tS b c K d).ν
        {l | (l, (t - tI) / H) ∈ (Block.data D E tI H p tS b c K d).E} := hact
    obtain ⟨l, hl⟩ := nonempty_of_measure_ne_zero hpos'.ne'
    have hlt : (l, t) ∈ E := by
      have := hl.2.1
      have e : tI + H * ((t - tI) / H) = t := by field_simp; ring
      rwa [e] at this
    apply lt_of_lt_of_le _ (measure_mono (show {l' | l' ∈ Block.grp D E tI H p tS b c ∧
        (l', tI + H * ((t - tI) / H)) ∈ E ∧ (t - tI) / H ∈ Icc (0:ℝ) 1} ⊆ {l | (l, t) ∈ E} by
      intro l' hl'
      have e : tI + H * ((t - tI) / H) = t := by field_simp; ring
      have := hl'.2.1; rw [e] at this; exact this))
    have : 0 < D.ν ({l' | l' ∈ Block.grp D E tI H p tS b c ∧ (l', tI + H * ((t - tI) / H)) ∈ E ∧
        (t - tI) / H ∈ Icc (0:ℝ) 1} ∩ Block.grp D E tI H p tS b c) := by
      have h := hpos'
      simp only [Block.data, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
      rw [Measure.restrict_apply' (Block.measurableSet_grp hD hEm)] at h
      exact pos_of_mul_pos_right h bot_le |> fun h' => by
        rcases (ENNReal.mul_pos_iff.1 h) with ⟨-, h2⟩; exact h2
    exact this.trans_le (measure_mono inter_subset_left)
  · -- the measure
    have hvol : volume T' = ENNReal.ofReal H * volume T := by
      have e : T' = (fun t => -tI + t) ⁻¹' ((fun u => H⁻¹ * u) ⁻¹' T) := by
        ext t; simp only [hT', mem_preimage]; rw [div_eq_inv_mul]; ring_nf
      rw [e, measure_preimage_add, Real.volume_preimage_mul_left (inv_ne_zero hH.ne'), inv_inv,
        abs_of_pos hH]
    rw [hvol, ENNReal.ofReal_mul hH.le]
    gcongr
    simpa [C0] using hTvol
  · -- the affine fit
    intro t ht
    have hfit := hTfit _ ht
    have hu := hTact ht
    have hpos' : 0 < (Block.data D E tI H p tS b c K d).ν
        {l | (l, (t - tI) / H) ∈ (Block.data D E tI H p tS b c K d).E} := hu
    obtain ⟨l, hl⟩ := nonempty_of_measure_ne_zero hpos'.ne'
    have huΛ : (t - tI) / H ∈ Block.lamS D E tI H p tS b c := ⟨hl.2.2, l, hl.1, hl.2.1⟩
    -- envelope versus raw row
    have hfφ : ∀ a ∈ Block.lamS D E tI H p tS b c, -(2 * K) ≤ Block.phiR D tI H tS 0 a :=
      fun a ha => (abs_le.1 (Block.abs_phiR_le hD hEsub hH hζH (by rw [mem_Icc] at htS ⊢; exact htS)
        hK0.le ha 0)).1
    have hnear := lipEnv_near (g := id) (L := K) (e := ζ / H) hK0.le hfφ
      (fun a ha b hb => Block.phiR_slack hD hEsub hH ha hb 0) huΛ
    simp only [id] at hnear
    have hφdef : (Block.data D E tI H p tS b c K d).φ ((t - tI) / H) =
        lipEnv (Block.lamS D E tI H p tS b c) (Block.phiR D tI H tS 0) id K ((t - tI) / H) := rfl
    rw [hφdef] at hfit
    have hraw : D.F t 0 = D.F tS 0 + H * Block.phiR D tI H tS 0 ((t - tI) / H) := by
      simp only [Block.phiR]
      have e : tI + H * ((t - tI) / H) = t := by field_simp; ring
      rw [e]; field_simp; ring
    rw [hraw]
    have key : D.F tS 0 + H * Block.phiR D tI H tS 0 ((t - tI) / H) -
        (D.F tS 0 + H * c' - σ * tI + σ * t) =
        H * (Block.phiR D tI H tS 0 ((t - tI) / H) -
          lipEnv (Block.lamS D E tI H p tS b c) (Block.phiR D tI H tS 0) id K ((t - tI) / H)) +
        H * (lipEnv (Block.lamS D E tI H p tS b c) (Block.phiR D tI H tS 0) id K ((t - tI) / H) -
          (c' + σ * ((t - tI) / H))) := by
      field_simp; ring
    rw [key]
    calc _ ≤ |H * (Block.phiR D tI H tS 0 ((t - tI) / H) -
          lipEnv (Block.lamS D E tI H p tS b c) (Block.phiR D tI H tS 0) id K ((t - tI) / H))| +
        |H * (lipEnv (Block.lamS D E tI H p tS b c) (Block.phiR D tI H tS 0) id K ((t - tI) / H) -
          (c' + σ * ((t - tI) / H)))| := abs_add_le _ _
      _ ≤ H * (K * (ζ / H)) + H * ((12 * Ks + 2) * p) := by
          rw [abs_mul, abs_mul, abs_of_pos hH, abs_sub_comm]
          exact add_le_add (mul_le_mul_of_nonneg_left hnear hH.le)
            (mul_le_mul_of_nonneg_left hfit hH.le)
      _ = H * ((12 * Ks + 2) * p) + K * ζ := by field_simp; ring

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
