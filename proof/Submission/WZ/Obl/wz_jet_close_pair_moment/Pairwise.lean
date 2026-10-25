-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.Pairwise.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.Geometry
import Submission.WZ.Obl.wz_jet_close_pair_moment.Sublevel
import Submission.WZ.Obl.wz_jet_close_pair_moment.Measure

namespace WangZahlLot.Obl.wz_jet_close_pair_moment

open MeasureTheory Set Metric

private theorem local_interval_mem {z w : ℝ} :
    z ∈ Icc (max (-1) (w-1/10000)) (min 1 (w+1/10000)) ↔
      z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 := by
  simp only [mem_Icc, max_le_iff, le_min_iff, abs_le]
  constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;> constructor <;> constructor <;> linarith

/-- Uniform local sublevel control in each of the three jet alternatives. -/
theorem JetControlled.local_sublevel_volume {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (i j : Fin n) {δ w : ℝ} (hδ : 0 < δ) (hd : 0 < dist (q i) (q j))
    (hw : w ∈ Icc (-1 : ℝ) 1) :
    volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 ∧
      |g i z-g j z| ≤ 2*δ} ≤
      ENNReal.ofReal (4000 * Real.sqrt (δ / dist (q i) (q j))) := by
  let d := dist (q i) (q j)
  have hd' : 0 < d := hd
  have ht : 0 ≤ δ/d := div_nonneg hδ.le hd.le
  have hs : 0 ≤ Real.sqrt (δ/d) := Real.sqrt_nonneg _
  by_cases hlarge : d ≤ 1000*δ
  · have hratio : (1/1000 : ℝ) ≤ δ/d := (le_div_iff₀ hd').mpr (by linarith)
    have hroot : (1/1000 : ℝ) ≤ Real.sqrt (δ/d) :=
      (Real.le_sqrt (by norm_num) ht).mpr (by nlinarith)
    calc
      volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 ∧ |g i z-g j z| ≤ 2*δ}
          ≤ volume (Icc (-1 : ℝ) 1) := measure_mono (fun _ hz => hz.1)
      _ = ENNReal.ofReal 2 := by rw [Real.volume_Icc]; norm_num
      _ ≤ ENNReal.ofReal (4000 * Real.sqrt (δ/d)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
  have hsmall : 1000*δ < d := lt_of_not_ge hlarge
  have ht1 : δ/d ≤ 1 := (div_le_one hd').mpr (by linarith)
  have hroot : δ/d ≤ Real.sqrt (δ/d) :=
    (Real.le_sqrt ht ht).mpr (by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)])
  let a := max (-1 : ℝ) (w-1/10000)
  let b := min (1 : ℝ) (w+1/10000)
  have hab : ∀ z ∈ Icc a b, z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 :=
    fun _ hz => local_interval_mem.mp hz
  have heq : {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 ∧ |g i z-g j z| ≤ 2*δ} =
      {z | z ∈ Icc a b ∧ |(g i-g j) z| ≤ 2*δ} := by
    ext z
    simp only [mem_ofPred_eq, Pi.sub_apply, a, b, local_interval_mem]
    tauto
  rw [heq]
  rcases hjet.local_alternative hg i j hw with hvalue | hslope | hcurv
  · have hempty : {z | z ∈ Icc a b ∧ |(g i-g j) z| ≤ 2*δ} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have h := hvalue z (hab z hz.1).1 (hab z hz.1).2
      have hz' : |g i z-g j z| ≤ 2*δ := hz.2
      change d / 480 ≤ _ at h
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · have hbound := volume_sublevel_le_of_deriv
      (((hg i).sub (hg j)).differentiable (by norm_num))
      (by positivity : 0 < d/480) (a := a) (b := b) (A := 2*δ) (by
        intro z hz
        change d / 480 ≤ |deriv (g i - g j) z|
        rw [deriv_sub_of_contDiff_two (hg i) (hg j)]
        exact hslope z (hab z hz).1 (hab z hz).2)
    apply hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : 2*(2*δ)/(d/480) = 1920*(δ/d) := by field_simp; ring
    rw [he]
    nlinarith
  · have hbound := volume_sublevel_le_of_deriv2 ((hg i).sub (hg j))
      (by positivity : 0 ≤ 2*δ) (by positivity : 0 < d/60) (a := a) (b := b) (by
        intro z hz
        change d / 60 ≤ |deriv (deriv (g i - g j)) z|
        rw [deriv2_sub_of_contDiff_two (hg i) (hg j)]
        exact hcurv z (hab z hz).1 (hab z hz).2)
    apply hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (2*δ)/(d/60) = 120*(δ/d) := by field_simp; ring
    rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 120)]
    have h120 : Real.sqrt 120 ≤ 1000 :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    nlinarith

/-- A fixed finite cover turns the local jet alternative into a uniform
pairwise sublevel bound on the entire time interval. -/
theorem exists_pairwise_sublevel_constant : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ i j : Fin n, ∀ δ : ℝ, 0 < δ → 0 < dist (q i) (q j) →
      volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z-g j z| ≤ 2*δ} ≤
        ENNReal.ofReal (C * Real.sqrt (δ / dist (q i) (q j))) := by
  classical
  obtain ⟨centers, hcover⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).elim_finite_subcover
    (fun w : Icc (-1 : ℝ) 1 => ball (w : ℝ) (1/10000)) (fun _ => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (by norm_num)⟩)
  refine ⟨4000*((centers.card : ℝ)+1), by positivity, ?_⟩
  intro n q g hjet hg i j δ hδ hd
  let S := {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z-g j z| ≤ 2*δ}
  let T := fun w : Icc (-1 : ℝ) 1 =>
    {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z-(w : ℝ)| ≤ 1/10000 ∧ |g i z-g j z| ≤ 2*δ}
  have hsub : S ⊆ ⋃ w ∈ centers, T w := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hcover hz.1)
    refine mem_iUnion₂.mpr ⟨w, hw, hz.1, ?_, hz.2⟩
    exact le_of_lt (by simpa only [mem_ball, Real.dist_eq] using hzw)
  calc
    volume S ≤ volume (⋃ w ∈ centers, T w) := measure_mono hsub
    _ ≤ ∑ w ∈ centers, volume (T w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ centers, ENNReal.ofReal (4000*Real.sqrt (δ/dist (q i) (q j))) := by
      apply Finset.sum_le_sum
      intro w hw
      exact hjet.local_sublevel_volume hg i j hδ hd w.property
    _ = ENNReal.ofReal ((centers.card : ℝ)*(4000*Real.sqrt (δ/dist (q i) (q j)))) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg centers.card)]
    _ ≤ ENNReal.ofReal (4000*((centers.card : ℝ)+1)*Real.sqrt (δ/dist (q i) (q j))) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [Real.sqrt_nonneg (δ/dist (q i) (q j))]

/-- Fubini bounds the overlap of two strips by their common-time sublevel set. -/
theorem volume_strip_inter_le_sublevel {f g : ℝ → ℝ} {δ : ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    volume (strip δ f ∩ strip δ g) ≤ ENNReal.ofReal (2*δ) *
      volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |f z-g z| ≤ 2*δ} := by
  let E := {z | z ∈ Icc (-1 : ℝ) 1 ∧ |f z-g z| ≤ 2*δ}
  have hE : MeasurableSet E := measurableSet_Icc.inter
    (isClosed_le (hf.sub hg).abs continuous_const).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm
    ((measurableSet_strip hf).inter (measurableSet_strip hg))]
  have hbound : ∀ z : ℝ,
      volume ((fun x : ℝ => (x,z)) ⁻¹' (strip δ f ∩ strip δ g)) ≤
        E.indicator (fun _ => ENNReal.ofReal (2*δ)) z := by
    intro z
    by_cases hz : z ∈ E
    · rw [indicator_of_mem hz]
      have hsub : ((fun x : ℝ => (x,z)) ⁻¹' (strip δ f ∩ strip δ g)) ⊆
          (fun x : ℝ => (x,z)) ⁻¹' strip δ f :=
        preimage_mono inter_subset_left
      have h := measure_mono (μ := (volume : Measure ℝ)) hsub
      rw [strip_fiber hz.1, Real.volume_Icc] at h
      convert h using 2
      ring
    · rw [indicator_of_notMem hz]
      have he : ((fun x : ℝ => (x,z)) ⁻¹' (strip δ f ∩ strip δ g)) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hfx : z ∈ Icc (-1 : ℝ) 1 ∧ |x-f z| ≤ δ := hx.1
        have hgx : z ∈ Icc (-1 : ℝ) 1 ∧ |x-g z| ≤ δ := hx.2
        apply hz
        refine ⟨hfx.1, ?_⟩
        have h := abs_sub_le (f z) x (g z)
        rw [abs_sub_comm (f z) x] at h
        linarith [hfx.2, hgx.2]
      rw [he, measure_empty]
  apply (lintegral_mono hbound).trans
  rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ]

/-- The uniform pairwise overlap estimate following from the frozen jet
hypotheses. No nonconcentration or global coefficient bound is used. -/
theorem exists_pairwise_overlap_constant : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ i j : Fin n, ∀ δ : ℝ, 0 < δ → 0 < dist (q i) (q j) →
      volume (strip δ (g i) ∩ strip δ (g j)) ≤
        ENNReal.ofReal (C * δ * Real.sqrt (δ / dist (q i) (q j))) := by
  obtain ⟨C, hC, hbound⟩ := exists_pairwise_sublevel_constant
  refine ⟨2*C, by positivity, ?_⟩
  intro n q g hjet hg i j δ hδ hd
  calc
    volume (strip δ (g i) ∩ strip δ (g j)) ≤ ENNReal.ofReal (2*δ) *
        volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z-g j z| ≤ 2*δ} :=
      volume_strip_inter_le_sublevel (hg i).continuous (hg j).continuous
    _ ≤ ENNReal.ofReal (2*δ) * ENNReal.ofReal (C * Real.sqrt (δ/dist (q i) (q j))) :=
      by
        gcongr
        exact hbound hjet hg i j δ hδ hd
    _ = ENNReal.ofReal ((2*C)*δ*Real.sqrt (δ/dist (q i) (q j))) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ)]
      congr 1
      ring

end WangZahlLot.Obl.wz_jet_close_pair_moment
