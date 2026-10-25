-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.NearPairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.Pairwise

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- At coefficient distances much larger than the strip width, a small slope
window has small time measure. -/
theorem local_near_pair_time {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (i j : Fin n) {δ κ w : ℝ} (hδ : 0 < δ) (_hκ : 0 ≤ κ)
    (hκsmall : κ < 1 / 480) (hfar : 1000 * δ < dist (q i) (q j))
    (hw : w ∈ Icc (-1 : ℝ) 1) :
    volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z - w| ≤ 1 / 10000 ∧
      |g i z - g j z| ≤ 2 * δ ∧
      |deriv (g i) z - deriv (g j) z| ≤ κ * dist (q i) (q j)} ≤
      ENNReal.ofReal (120 * κ) := by
  let d := dist (q i) (q j)
  have hd : 0 < d := by dsimp [d]; linarith
  let a := max (-1 : ℝ) (w - 1 / 10000)
  let b := min (1 : ℝ) (w + 1 / 10000)
  have hI (z : ℝ) : z ∈ Icc a b ↔
      z ∈ Icc (-1 : ℝ) 1 ∧ |z - w| ≤ 1 / 10000 := by
    simp only [a, b, mem_Icc, max_le_iff, le_min_iff, abs_le]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
      exact ⟨⟨h₁, h₃⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
      exact ⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩
  let S := {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z - w| ≤ 1 / 10000 ∧
    |g i z - g j z| ≤ 2 * δ ∧ |deriv (g i) z - deriv (g j) z| ≤ κ * d}
  change volume S ≤ _
  rcases hjet.local_alternative hg i j hw with hv | hs | hc
  · have hempty : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have h := hv z hz.1 hz.2.1
      have hf := hz.2.2.1
      change d / 480 ≤ _ at h
      change 1000 * δ < d at hfar
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · have hempty : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have h := hs z hz.1 hz.2.1
      have hf := hz.2.2.2
      change d / 480 ≤ _ at h
      have hkd := mul_lt_mul_of_pos_right hκsmall hd
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · have hdf : Differentiable ℝ (deriv (g i - g j)) :=
      (((hg i).sub (hg j)).deriv' (n := 1)).differentiable (by norm_num)
    have hbound := volume_sublevel_le_of_deriv hdf
      (a := a) (b := b) (A := κ * d) (c := d / 60) (by positivity) (by
        intro z hz
        rw [deriv2_sub_of_contDiff_two (hg i) (hg j)]
        exact hc z ((hI z).mp hz).1 ((hI z).mp hz).2)
    have hsub : S ⊆ {z | z ∈ Icc a b ∧ |deriv (g i - g j) z| ≤ κ * d} := by
      intro z hz
      refine ⟨(hI z).mpr ⟨hz.1, hz.2.1⟩, ?_⟩
      rw [deriv_sub_of_contDiff_two (hg i) (hg j)]
      exact hz.2.2.2
    apply (measure_mono hsub).trans (hbound.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have heq : 2 * (κ * d) / (d / 60) = 120 * κ := by field_simp; ring
    exact heq.le

/-- The small-slope time estimate is uniform in the curves and their
coefficient distance. -/
theorem exists_near_pair_time_constant : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ i j : Fin n, ∀ δ κ : ℝ, 0 < δ → 0 ≤ κ → 1000 * δ < dist (q i) (q j) →
      volume {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z - g j z| ≤ 2 * δ ∧
        |deriv (g i) z - deriv (g j) z| ≤ κ * dist (q i) (q j)} ≤
        ENNReal.ofReal (C * κ) := by
  classical
  obtain ⟨centers, hcover⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).elim_finite_subcover
    (fun w : Icc (-1 : ℝ) 1 => ball (w : ℝ) (1 / 10000)) (fun _ => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (by norm_num)⟩)
  refine ⟨960 + 120 * (centers.card : ℝ), by positivity, ?_⟩
  intro n q g hjet hg i j δ κ hδ hκ hfar
  by_cases hκsmall : κ < 1 / 480
  · let T := fun w : Icc (-1 : ℝ) 1 =>
      {z | z ∈ Icc (-1 : ℝ) 1 ∧ |z - (w : ℝ)| ≤ 1 / 10000 ∧
        |g i z - g j z| ≤ 2 * δ ∧
        |deriv (g i) z - deriv (g j) z| ≤ κ * dist (q i) (q j)}
    have hsub : {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z - g j z| ≤ 2 * δ ∧
        |deriv (g i) z - deriv (g j) z| ≤ κ * dist (q i) (q j)} ⊆
        ⋃ w ∈ centers, T w := by
      intro z hz
      obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hcover hz.1)
      refine mem_iUnion₂.mpr ⟨w, hw, hz.1, ?_, hz.2⟩
      exact le_of_lt (by simpa only [mem_ball, Real.dist_eq] using hzw)
    calc
      _ ≤ volume (⋃ w ∈ centers, T w) := measure_mono hsub
      _ ≤ ∑ w ∈ centers, volume (T w) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ centers, ENNReal.ofReal (120 * κ) :=
        Finset.sum_le_sum fun w _ => local_near_pair_time hjet hg i j hδ hκ hκsmall hfar w.property
      _ = ENNReal.ofReal ((centers.card : ℝ) * (120 * κ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg centers.card)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith)
  · have hlarge : 1 / 480 ≤ κ := le_of_not_gt hκsmall
    calc
      _ ≤ volume (Icc (-1 : ℝ) 1) := measure_mono fun _ hz => hz.1
      _ = ENNReal.ofReal 2 := by rw [Real.volume_Icc]; norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        nlinarith [mul_nonneg (Nat.cast_nonneg centers.card) hκ])

/-- Restricting the time coordinate in a graph strip costs at most its
horizontal width times the measure of the allowed times. -/
theorem volume_subset_strip_time {δ : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    {T : Set ℝ} (hT : MeasurableSet T) {E : Set (ℝ × ℝ)}
    (hE : E ⊆ strip δ g ∩ Prod.snd ⁻¹' T) :
    volume E ≤ ENNReal.ofReal (2 * δ) * volume T := by
  apply (measure_mono hE).trans
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm
    ((measurableSet_strip hg).inter (hT.preimage measurable_snd))]
  calc
    _ ≤ ∫⁻ z, T.indicator (fun _ => ENNReal.ofReal (2 * δ)) z := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ T
      · rw [indicator_of_mem hz]
        have hsub : ((fun x : ℝ => (x, z)) ⁻¹' (strip δ g ∩ Prod.snd ⁻¹' T)) ⊆
            (fun x : ℝ => (x, z)) ⁻¹' strip δ g := preimage_mono inter_subset_left
        apply (measure_mono hsub).trans
        by_cases hzI : z ∈ Icc (-1 : ℝ) 1
        · rw [strip_fiber hzI, Real.volume_Icc]
          apply ENNReal.ofReal_le_ofReal
          linarith
        · rw [strip_fiber_of_not_mem hzI, measure_empty]
          exact zero_le
      · rw [indicator_of_notMem hz]
        have he : (fun x : ℝ => (x, z)) ⁻¹' (strip δ g ∩ Prod.snd ⁻¹' T) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hz hx.2
        change volume ((fun x : ℝ => (x, z)) ⁻¹' (strip δ g ∩ Prod.snd ⁻¹' T)) ≤ 0
        rw [he, measure_empty]
    _ = _ := by rw [lintegral_indicator hT, lintegral_const, Measure.restrict_apply_univ]

/-- The complementary, strictly narrow, intersection of two strips. -/
def narrowIntersection (δ κ : ℝ) (q r : EuclideanSpace ℝ (Fin 3))
    (f g : ℝ → ℝ) : Set (ℝ × ℝ) :=
  strip δ f ∩ strip δ g ∩ {p | |deriv f p.2 - deriv g p.2| < κ * dist q r}

theorem measurableSet_narrowIntersection {δ κ : ℝ} {q r : EuclideanSpace ℝ (Fin 3)}
    {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    MeasurableSet (narrowIntersection δ κ q r f g) := by
  apply ((measurableSet_strip hf.continuous).inter
    (measurableSet_strip hg.continuous)).inter
  exact (isOpen_lt
    (((hf.deriv' (n := 1)).continuous.comp continuous_snd).sub
      ((hg.deriv' (n := 1)).continuous.comp continuous_snd)).abs continuous_const).measurableSet

/-- For a far pair, restricting to small relative slope gives a factor `κ`
in the overlap area, independently of the coefficient scale. -/
theorem exists_narrow_overlap_constant : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ i j : Fin n, ∀ δ κ : ℝ, 0 < δ → 0 ≤ κ → 1000 * δ < dist (q i) (q j) →
      volume (narrowIntersection δ κ (q i) (q j) (g i) (g j)) ≤
        ENNReal.ofReal (C * δ * κ) := by
  obtain ⟨C, hC, hbound⟩ := exists_near_pair_time_constant
  refine ⟨2 * C, by positivity, ?_⟩
  intro n q g hjet hg i j δ κ hδ hκ hfar
  let T := {z | z ∈ Icc (-1 : ℝ) 1 ∧ |g i z - g j z| ≤ 2 * δ ∧
    |deriv (g i) z - deriv (g j) z| ≤ κ * dist (q i) (q j)}
  have hT : MeasurableSet T := measurableSet_Icc.inter
    (((isClosed_le ((hg i).continuous.sub (hg j).continuous).abs continuous_const).measurableSet).inter
      ((isClosed_le (((hg i).deriv' (n := 1)).continuous.sub
        ((hg j).deriv' (n := 1)).continuous).abs continuous_const).measurableSet))
  have hsub : narrowIntersection δ κ (q i) (q j) (g i) (g j) ⊆
      strip δ (g i) ∩ Prod.snd ⁻¹' T := by
    intro p hp
    refine ⟨hp.1.1, hp.1.1.1, ?_, hp.2.le⟩
    have hv := abs_sub_le (g i p.2) p.1 (g j p.2)
    rw [abs_sub_comm (g i p.2) p.1] at hv
    linarith [hp.1.1.2, hp.1.2.2]
  calc
    _ ≤ ENNReal.ofReal (2 * δ) * volume T := volume_subset_strip_time (hg i).continuous hT hsub
    _ ≤ ENNReal.ofReal (2 * δ) * ENNReal.ofReal (C * κ) := by
      gcongr
      exact hbound hjet hg i j δ κ hδ hκ hfar
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * δ)]
      congr 1
      ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
