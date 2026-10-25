-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_transverse_pair_moment.Transverse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.Geometry
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.Measure
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.MonotoneSublevel

namespace WangZahlLot.Obl.wz_jet_transverse_pair_moment

open MeasureTheory Set Metric

/-- The portion of a strip intersection with a quantitative slope separation. -/
def transverseIntersection (δ κ : ℝ) (q r : EuclideanSpace ℝ (Fin 3))
    (f g : ℝ → ℝ) : Set (ℝ × ℝ) :=
  strip δ f ∩ strip δ g ∩
    {p | κ * dist q r ≤ |deriv f p.2 - deriv g p.2|}

theorem measurableSet_transverseIntersection {δ κ : ℝ}
    {q r : EuclideanSpace ℝ (Fin 3)} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    MeasurableSet (transverseIntersection δ κ q r f g) := by
  apply ((measurableSet_strip hf.continuous).inter
    (measurableSet_strip hg.continuous)).inter
  exact (isClosed_le continuous_const
    (((hf.deriv' (n := 1)).continuous.comp continuous_snd).sub
      ((hg.deriv' (n := 1)).continuous.comp continuous_snd)).abs).measurableSet

/-- Fubini converts transverse common-time control to strip-overlap control. -/
theorem volume_transverseIntersection_le_sublevel {δ κ : ℝ}
    {q r : EuclideanSpace ℝ (Fin 3)} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    volume (transverseIntersection δ κ q r f g) ≤ ENNReal.ofReal (2*δ) *
      volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |f z-g z| ≤ 2*δ ∧
        κ * dist q r ≤ |deriv f z-deriv g z|} := by
  let E := {z | z ∈ Icc (-1 : ℝ) 1 ∧ |f z-g z| ≤ 2*δ ∧
    κ * dist q r ≤ |deriv f z-deriv g z|}
  have hE : MeasurableSet E := measurableSet_Icc.inter
    (((isClosed_le (hf.continuous.sub hg.continuous).abs continuous_const).measurableSet).inter
      ((isClosed_le continuous_const
        (((hf.deriv' (n := 1)).continuous).sub
          ((hg.deriv' (n := 1)).continuous)).abs).measurableSet))
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm
    (measurableSet_transverseIntersection hf hg)]
  have hbound : ∀ z : ℝ,
      volume ((fun x : ℝ => (x,z)) ⁻¹' (transverseIntersection δ κ q r f g)) ≤
        E.indicator (fun _ => ENNReal.ofReal (2*δ)) z := by
    intro z
    by_cases hz : z ∈ E
    · rw [indicator_of_mem hz]
      have hsub : ((fun x : ℝ => (x,z)) ⁻¹' (transverseIntersection δ κ q r f g)) ⊆
          (fun x : ℝ => (x,z)) ⁻¹' strip δ f := fun _ hx => hx.1.1
      have h := measure_mono (μ := (volume : Measure ℝ)) hsub
      rw [strip_fiber hz.1, Real.volume_Icc] at h
      convert h using 2
      ring
    · rw [indicator_of_notMem hz]
      have he : ((fun x : ℝ => (x,z)) ⁻¹' (transverseIntersection δ κ q r f g)) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hz
        refine ⟨hx.1.1.1, ?_, hx.2⟩
        have h := abs_sub_le (f z) x (g z)
        rw [abs_sub_comm (f z) x] at h
        linarith [hx.1.1.2, hx.1.2.2]
      rw [he, measure_empty]
  apply (lintegral_mono hbound).trans
  rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ]

/-- The local transverse estimate has precisely the inverse first power of
its slope threshold. Monotonicity in the curvature alternative is crucial. -/
theorem JetControlled.local_transverse_sublevel_volume {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (i j : Fin n) {δ κ w : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hd : 0 < dist (q i) (q j)) (hw : w ∈ Icc (-1 : ℝ) 1) :
    volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 ∧
      |g i z-g j z| ≤ 2*δ ∧
      κ*dist (q i) (q j) ≤ |deriv (g i) z-deriv (g j) z|} ≤
      ENNReal.ofReal (4000*δ/(κ*dist (q i) (q j))) := by
  let d := dist (q i) (q j)
  have hd' : 0 < d := hd
  by_cases hlarge : d ≤ 1000*δ
  · calc
      volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 ∧
        |g i z-g j z| ≤ 2*δ ∧
        κ*dist (q i) (q j) ≤ |deriv (g i) z-deriv (g j) z|} ≤
          volume (Icc (-1 : ℝ) 1) := measure_mono (fun _ hz => hz.1)
      _ = ENNReal.ofReal 2 := by rw [Real.volume_Icc]; norm_num
      _ ≤ ENNReal.ofReal (4000*δ/(κ*d)) := by
        apply ENNReal.ofReal_le_ofReal
        apply (le_div_iff₀ (mul_pos hκ hd')).mpr
        have hkd : κ*d ≤ d := by nlinarith
        linarith
  have hsmall : 1000*δ < d := lt_of_not_ge hlarge
  let a := max (-1 : ℝ) (w-1/10000)
  let b := min (1 : ℝ) (w+1/10000)
  have hab : ∀ z ∈ Icc a b, z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 := by
    intro z hz
    have hl := max_le_iff.mp hz.1
    have hr := le_min_iff.mp hz.2
    exact ⟨⟨hl.1, hr.1⟩, abs_le.mpr ⟨by linarith [hl.2], by linarith [hr.2]⟩⟩
  have heq : {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 ∧
      |g i z-g j z| ≤ 2*δ ∧ κ*d ≤ |deriv (g i) z-deriv (g j) z|} =
      {z | z ∈ Icc a b ∧ |(g i-g j) z| ≤ 2*δ ∧ κ*d ≤ |deriv (g i-g j) z|} := by
    ext z
    rw [deriv_sub_of_contDiff_two (hg i) (hg j)]
    have hi : z ∈ Icc a b ↔ z ∈ Icc (-1 : ℝ) 1 ∧ |z-w| ≤ 1/10000 := by
      simp only [a, b, mem_Icc, max_le_iff, le_min_iff, abs_le]
      constructor
      · intro h
        exact ⟨⟨h.1.1, h.2.1⟩, ⟨by linarith [h.1.2], by linarith [h.2.2]⟩⟩
      · intro h
        exact ⟨⟨h.1.1, by linarith [h.2.1]⟩, ⟨h.1.2, by linarith [h.2.2]⟩⟩
    simp only [mem_ofPred_eq, Pi.sub_apply, hi]
    tauto
  rw [heq]
  rcases hjet.local_alternative hg i j hw with hv | hs | hc
  · have hempty : {z | z ∈ Icc a b ∧ |(g i-g j) z| ≤ 2*δ ∧
        κ*d ≤ |deriv (g i-g j) z|} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have h := hv z (hab z hz.1).1 (hab z hz.1).2
      have hz' : |g i z-g j z| ≤ 2*δ := hz.2.1
      change d/480 ≤ _ at h
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · have hbound := volume_sublevel_le_of_deriv
      (((hg i).sub (hg j)).differentiable (by norm_num))
      (by positivity : 0 < d/480) (a := a) (b := b) (A := 2*δ) (by
        intro z hz
        change d / 480 ≤ |deriv (g i-g j) z|
        rw [deriv_sub_of_contDiff_two (hg i) (hg j)]
        exact hs z (hab z hz).1 (hab z hz).2)
    have hsub : {z | z ∈ Icc a b ∧ |(g i-g j) z| ≤ 2*δ ∧ κ*d ≤ |deriv (g i-g j) z|} ⊆
        {z | z ∈ Icc a b ∧ |(g i-g j) z| ≤ 2*δ} := fun _ hz => ⟨hz.1, hz.2.1⟩
    apply (measure_mono hsub).trans (hbound.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have he : 2*(2*δ)/(d/480) = 1920*δ/d := by field_simp; ring
    rw [he]
    apply (div_le_div_iff₀ hd' (mul_pos hκ hd')).mpr
    have hprod := mul_le_mul_of_nonneg_left hκ1 (by positivity : 0 ≤ 1920*δ*d)
    nlinarith
  · have hmono := monotone_deriv_of_deriv2_ne_zero ((hg i).sub (hg j)) (a := a) (b := b) (by
      intro z hz he
      have h := hc z (hab z hz).1 (hab z hz).2
      change deriv (deriv (g i-g j)) z = 0 at he
      rw [deriv2_sub_of_contDiff_two (hg i) (hg j)] at he
      change deriv (deriv (g i)) z-deriv (deriv (g j)) z = 0 at he
      rw [he, abs_zero] at h
      linarith)
    apply (volume_sublevel_transverse_of_monotone_deriv
      (((hg i).sub (hg j)).differentiable (by norm_num))
      (by positivity : 0 ≤ 2*δ) (mul_pos hκ hd') hmono).trans
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (mul_pos hκ hd').le
    linarith

/-- A uniform constant controls transverse sublevels for all thresholds in
(0,1]. The only threshold loss is one inverse power. -/
theorem exists_uniform_transverse_sublevel_constant : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ i j : Fin n, ∀ δ κ : ℝ, 0 < δ → 0 < κ → κ ≤ 1 → 0 < dist (q i) (q j) →
      volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z-g j z| ≤ 2*δ ∧
        κ*dist (q i) (q j) ≤ |deriv (g i) z-deriv (g j) z|} ≤
        ENNReal.ofReal (C*δ/(κ*dist (q i) (q j))) := by
  classical
  obtain ⟨centers, hcover⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).elim_finite_subcover
    (fun w : Icc (-1 : ℝ) 1 => ball (w : ℝ) (1/10000)) (fun _ => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (by norm_num)⟩)
  refine ⟨4000*((centers.card : ℝ)+1), by positivity, ?_⟩
  intro n q g hjet hg i j δ κ hδ hκ hκ1 hd
  let S := {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z-g j z| ≤ 2*δ ∧
    κ*dist (q i) (q j) ≤ |deriv (g i) z-deriv (g j) z|}
  let T := fun w : Icc (-1 : ℝ) 1 =>
    {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z-(w : ℝ)| ≤ 1/10000 ∧
      |g i z-g j z| ≤ 2*δ ∧ κ*dist (q i) (q j) ≤ |deriv (g i) z-deriv (g j) z|}
  have hsub : S ⊆ ⋃ w ∈ centers, T w := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hcover hz.1)
    refine mem_iUnion₂.mpr ⟨w, hw, hz.1, ?_, hz.2⟩
    exact le_of_lt (by simpa only [mem_ball, Real.dist_eq] using hzw)
  calc
    volume S ≤ volume (⋃ w ∈ centers, T w) := measure_mono hsub
    _ ≤ ∑ w ∈ centers, volume (T w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ centers, ENNReal.ofReal (4000*δ/(κ*dist (q i) (q j))) := by
      apply Finset.sum_le_sum
      intro w hw
      exact hjet.local_transverse_sublevel_volume hg i j hδ hκ hκ1 hd w.property
    _ = ENNReal.ofReal ((centers.card : ℝ)*(4000*δ/(κ*dist (q i) (q j)))) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg centers.card)]
    _ ≤ ENNReal.ofReal ((4000*((centers.card : ℝ)+1))*δ/(κ*dist (q i) (q j))) := by
      apply ENNReal.ofReal_le_ofReal
      have hnonneg : 0 ≤ 4000*δ/(κ*dist (q i) (q j)) := by positivity
      calc
        (centers.card : ℝ)*(4000*δ/(κ*dist (q i) (q j))) ≤
            ((centers.card : ℝ)+1)*(4000*δ/(κ*dist (q i) (q j))) := by nlinarith
        _ = _ := by ring

/-- The uniform transverse overlap estimate, with its sharp threshold loss. -/
theorem exists_uniform_transverse_overlap_constant : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ i j : Fin n, ∀ δ κ : ℝ, 0 < δ → 0 < κ → κ ≤ 1 → 0 < dist (q i) (q j) →
      volume (transverseIntersection δ κ (q i) (q j) (g i) (g j)) ≤
        ENNReal.ofReal (C*δ^2/(κ*dist (q i) (q j))) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_transverse_sublevel_constant
  refine ⟨2*C, by positivity, ?_⟩
  intro n q g hjet hg i j δ κ hδ hκ hκ1 hd
  calc
    volume (transverseIntersection δ κ (q i) (q j) (g i) (g j)) ≤
        ENNReal.ofReal (2*δ) *
          volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z-g j z| ≤ 2*δ ∧
            κ*dist (q i) (q j) ≤ |deriv (g i) z-deriv (g j) z|} :=
      volume_transverseIntersection_le_sublevel (hg i) (hg j)
    _ ≤ ENNReal.ofReal (2*δ) * ENNReal.ofReal (C*δ/(κ*dist (q i) (q j))) := by
      gcongr
      exact hbound hjet hg i j δ κ hδ hκ hκ1 hd
    _ = ENNReal.ofReal ((2*C)*δ^2/(κ*dist (q i) (q j))) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ)]
      congr 1
      ring

end WangZahlLot.Obl.wz_jet_transverse_pair_moment
