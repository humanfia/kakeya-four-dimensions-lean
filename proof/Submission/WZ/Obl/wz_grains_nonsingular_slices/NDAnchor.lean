-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.NDAnchor.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.ShearFubini

/-!
# Nondegeneracy, step 2: a common anchoring plane

If every point of the shadings lies on a grain whose fibre has length at least `lam`, then for
some plane `{q 1 = y0}` a fixed fraction of the shading mass is anchored: the grain through the
point meets `E` at `y0`, at a locally full point of the fibre.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- A set of length at least `lam` in `[-1, 1]` has length at least `lam / 2` in its locally full
points (scale `ℓ`, density `lam / 20`): partition `[-1, 1]` into intervals of length `ℓ / 2`; a
point of an interval carrying length `≥ lam ℓ / 20` is locally full, and the other intervals carry
at most `(4 / ℓ + 2) lam ℓ / 20 ≤ 3 lam / 10` in total. -/
lemma nda_locFull_volume {F : Set ℝ} (hF : F ⊆ Icc (-1) 1) {lam ℓ : ℝ} (hlam : 0 < lam)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hvol : ENNReal.ofReal lam ≤ volume F) :
    ENNReal.ofReal (lam / 2) ≤ volume {y | y ∈ F ∧ LocFull F ℓ (lam / 20) y} := by
  classical
  set N : ℕ := ⌈4 / ℓ⌉₊ + 1 with hN
  set I : ℕ → Set ℝ := fun k => Ico (-1 + k * (ℓ / 2)) (-1 + (k + 1) * (ℓ / 2)) with hI
  set bad : Finset ℕ := (Finset.range N).filter
    (fun k => volume (F ∩ I k) < ENNReal.ofReal (lam / 20 * ℓ)) with hbad
  have hℓ2 : 0 < ℓ / 2 := by positivity
  have hcover : F ⊆ {y | y ∈ F ∧ LocFull F ℓ (lam / 20) y} ∪ ⋃ k ∈ bad, (F ∩ I k) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hF hy
    set k := ⌊(y + 1) / (ℓ / 2)⌋₊ with hk
    have h1 : (k : ℝ) ≤ (y + 1) / (ℓ / 2) := Nat.floor_le (div_nonneg (by linarith) hℓ2.le)
    have h2 : (y + 1) / (ℓ / 2) < k + 1 := Nat.lt_floor_add_one _
    have h1' : -1 + k * (ℓ / 2) ≤ y := by
      have := (le_div_iff₀ hℓ2).mp h1; linarith
    have h2' : y < -1 + (k + 1) * (ℓ / 2) := by
      have := (div_lt_iff₀ hℓ2).mp h2; linarith
    have hyI : y ∈ I k := ⟨h1', h2'⟩
    have hkN : k < N := by
      have h3 : (y + 1) / (ℓ / 2) ≤ 4 / ℓ := by
        rw [div_le_div_iff₀ hℓ2 hℓ]; nlinarith
      have h4 : (k : ℝ) ≤ ⌈4 / ℓ⌉₊ := h1.trans (h3.trans (Nat.le_ceil _))
      have h5 : k ≤ ⌈4 / ℓ⌉₊ := by exact_mod_cast h4
      omega
    by_cases hgood : ENNReal.ofReal (lam / 20 * ℓ) ≤ volume (F ∩ I k)
    · left
      refine ⟨hy, hgood.trans (measure_mono ?_)⟩
      rintro t ⟨htF, ht1, ht2⟩
      exact ⟨htF, by linarith, by linarith⟩
    · right
      simp only [mem_iUnion]
      refine ⟨k, ?_, hy, hyI⟩
      simp only [hbad, Finset.mem_filter, Finset.mem_range]
      exact ⟨hkN, not_le.mp hgood⟩
  have hbadvol : volume (⋃ k ∈ bad, (F ∩ I k)) ≤ ENNReal.ofReal (3 * lam / 10) := by
    calc volume (⋃ k ∈ bad, (F ∩ I k)) ≤ ∑ k ∈ bad, volume (F ∩ I k) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ bad, ENNReal.ofReal (lam / 20 * ℓ) :=
          Finset.sum_le_sum (fun k hk => (Finset.mem_filter.mp hk).2.le)
      _ ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal (lam / 20 * ℓ) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ENNReal.ofReal (N * (lam / 20 * ℓ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (3 * lam / 10) := by
        apply ENNReal.ofReal_le_ofReal
        have hN1 : (N : ℝ) < 4 / ℓ + 2 := by
          simp only [hN, Nat.cast_add, Nat.cast_one]
          have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 / ℓ by positivity)
          linarith
        have h6 : (N : ℝ) * ℓ ≤ 6 := by
          have := mul_lt_mul_of_pos_right hN1 hℓ
          rw [add_mul, div_mul_cancel₀ _ hℓ.ne'] at this
          linarith
        nlinarith
  have htot := hvol.trans ((measure_mono hcover).trans (measure_union_le _ _))
  have h7 : ENNReal.ofReal lam ≤ volume {y | y ∈ F ∧ LocFull F ℓ (lam / 20) y} +
      ENNReal.ofReal (3 * lam / 10) := htot.trans (add_le_add le_rfl hbadvol)
  calc ENNReal.ofReal (lam / 2) ≤ ENNReal.ofReal (lam - 3 * lam / 10) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal lam - ENNReal.ofReal (3 * lam / 10) := ENNReal.ofReal_sub _ (by positivity)
    _ ≤ _ := tsub_le_iff_right.mpr h7

/-- The set of pairs `(q, y)` such that `q ∈ Z` and `y` is a locally full point of the fibre of
the grain through `q` is measurable in `Space × ℝ`. -/
lemma nda_measurableSet {f : ℝ → ℝ} (hf : Continuous f) {E : Set Space}
    (hE : MeasurableSet E) {Z : Set Space} (hZ : MeasurableSet Z) (ℓ κ : ℝ) :
    MeasurableSet {p : Space × ℝ | p.1 ∈ Z ∧ p.2 ∈ grainFib f E (twist f p.1) (p.1 2) ∧
      LocFull (grainFib f E (twist f p.1) (p.1 2)) ℓ κ p.2} := by
  have ht := continuous_twist hf
  have hΦ : Continuous (fun p : Space × ℝ => ofTwist f (twist f p.1) p.2 (p.1 2)) :=
    (continuous_ofTwist hf).comp (f := fun p : Space × ℝ => (twist f p.1, p.2, p.1 2))
      (by fun_prop)
  set T : Set ((Space × ℝ) × ℝ) := {x | ofTwist f (twist f x.1.1) x.2 (x.1.1 2) ∈ E ∧
    x.1.2 - ℓ / 2 ≤ x.2 ∧ x.2 ≤ x.1.2 + ℓ / 2} with hT
  have hTm : MeasurableSet T := by
    have h1 : MeasurableSet {x : (Space × ℝ) × ℝ | ofTwist f (twist f x.1.1) x.2 (x.1.1 2) ∈ E} :=
      hE.preimage (hΦ.comp (f := fun x : (Space × ℝ) × ℝ => (x.1.1, x.2))
        (by fun_prop)).measurable
    have h2 : MeasurableSet {x : (Space × ℝ) × ℝ | x.1.2 - ℓ / 2 ≤ x.2} :=
      measurableSet_le (f := fun x : (Space × ℝ) × ℝ => x.1.2 - ℓ / 2) (g := fun x => x.2)
        (by fun_prop) (by fun_prop)
    have h3 : MeasurableSet {x : (Space × ℝ) × ℝ | x.2 ≤ x.1.2 + ℓ / 2} :=
      measurableSet_le (f := fun x : (Space × ℝ) × ℝ => x.2) (g := fun x => x.1.2 + ℓ / 2)
        (by fun_prop) (by fun_prop)
    exact h1.inter (h2.inter h3)
  -- the sections of `T` are the pieces `grainFib ∩ Icc (y - ℓ / 2) (y + ℓ / 2)` in `LocFull`
  have hg : Measurable fun p : Space × ℝ => volume (Prod.mk p ⁻¹' T) :=
    measurable_measure_prodMk_left hTm
  have hLoc : MeasurableSet
      {p : Space × ℝ | LocFull (grainFib f E (twist f p.1) (p.1 2)) ℓ κ p.2} :=
    measurableSet_le (f := fun _ => ENNReal.ofReal (κ * ℓ))
      (g := fun p : Space × ℝ => volume (Prod.mk p ⁻¹' T)) measurable_const hg
  exact (measurable_fst hZ).inter ((hE.preimage hΦ.measurable).inter hLoc)

/-- Grain fibres of a subset of the unit ball lie in `[-1, 1]`. -/
lemma nda_grainFib_subset {f : ℝ → ℝ} {E : Set Space} (hEb : E ⊆ ball 0 1) (u z : ℝ) :
    grainFib f E u z ⊆ Icc (-1) 1 := by
  intro y hy
  have h1 : ‖ofTwist f u y z‖ < 1 := mem_ball_zero_iff.mp (hEb hy)
  have h2 := PiLp.norm_apply_le (ofTwist f u y z) 1
  have h3 : |y| ≤ 1 := by
    have : ‖(ofTwist f u y z) 1‖ = |y| := by simp
    rw [this] at h2
    linarith
  exact abs_le.mp h3

theorem nd_anchor {f : ℝ → ℝ} (hf : Continuous f) {E : Set Space} (hE : MeasurableSet E)
    (hEb : E ⊆ ball 0 1) {lam ℓ : ℝ} (hlam : 0 < lam) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    {ι : Type*} (G : Finset ι) (Z : ι → Set Space) (hZm : ∀ i ∈ G, MeasurableSet (Z i))
    (hZb : ∀ i ∈ G, Z i ⊆ ball 0 1) (hZfull : ∀ i ∈ G, Z i ⊆ FullPart f E lam) :
    ∃ y0 ∈ Icc (-1 : ℝ) 1, ENNReal.ofReal (lam / 8) * ∑ i ∈ G, volume (Z i) ≤
      ∑ i ∈ G, volume {q | q ∈ Z i ∧ y0 ∈ grainFib f E (twist f q) (q 2) ∧
        LocFull (grainFib f E (twist f q) (q 2)) ℓ (lam / 20) y0} := by
  classical
  -- `S i` is the set of pairs `(q, y)` with `q ∈ Z i` and `y` a locally full point of `F_q`
  set S : ι → Set (Space × ℝ) := fun i => {p : Space × ℝ | p.1 ∈ Z i ∧
    p.2 ∈ grainFib f E (twist f p.1) (p.1 2) ∧
    LocFull (grainFib f E (twist f p.1) (p.1 2)) ℓ (lam / 20) p.2} with hS
  have hSm : ∀ i ∈ G, MeasurableSet (S i) := fun i hi =>
    nda_measurableSet hf hE (hZm i hi) ℓ (lam / 20)
  -- each `q ∈ Z i` contributes a section of length at least `lam / 2`
  have hlow : ∀ i ∈ G, ENNReal.ofReal (lam / 2) * volume (Z i) ≤
      ((volume : Measure Space).prod (volume : Measure ℝ)) (S i) := by
    intro i hi
    rw [Measure.prod_apply (hSm i hi), ← lintegral_indicator_const (hZm i hi)]
    refine lintegral_mono fun q => ?_
    by_cases hq : q ∈ Z i
    · rw [indicator_of_mem hq]
      refine (nda_locFull_volume (nda_grainFib_subset hEb _ _) hlam hℓ hℓ1
        (hZfull i hi hq)).trans (measure_mono ?_)
      intro y hy
      exact ⟨hq, hy⟩
    · rw [indicator_of_notMem hq]
      exact zero_le
  -- if every plane `y0 ∈ [-1, 1]` failed, integrating over `y0` would give too little mass
  by_contra hcon
  push Not at hcon
  set c := ENNReal.ofReal (lam / 8) * ∑ i ∈ G, volume (Z i) with hc
  have hup : ∀ y : ℝ, ∑ i ∈ G, volume ((fun q => (q, y)) ⁻¹' S i) ≤
      (Icc (-1 : ℝ) 1).indicator (fun _ => c) y := by
    intro y
    by_cases hy : y ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hy]
      exact (hcon y hy).le
    · rw [indicator_of_notMem hy]
      refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
      have hempty : (fun q => (q, y)) ⁻¹' S i = ∅ := by
        ext q
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨_, hyq, _⟩
        exact hy (nda_grainFib_subset hEb _ _ hyq)
      rw [hempty, measure_empty]
  have hfin : ∑ i ∈ G, volume (Z i) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact ((measure_mono (hZb i hi)).trans_lt measure_ball_lt_top).ne
  have hpos : ∑ i ∈ G, volume (Z i) ≠ 0 := by
    intro h0
    have h := hcon 0 ⟨by norm_num, by norm_num⟩
    rw [hc, h0, mul_zero] at h
    exact not_lt_zero h
  have key : ENNReal.ofReal (lam / 2) * ∑ i ∈ G, volume (Z i) ≤
      ENNReal.ofReal (lam / 4) * ∑ i ∈ G, volume (Z i) := by
    calc ENNReal.ofReal (lam / 2) * ∑ i ∈ G, volume (Z i)
        = ∑ i ∈ G, ENNReal.ofReal (lam / 2) * volume (Z i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ G, ((volume : Measure Space).prod (volume : Measure ℝ)) (S i) :=
          Finset.sum_le_sum hlow
      _ = ∑ i ∈ G, ∫⁻ y, volume ((fun q => (q, y)) ⁻¹' S i) :=
          Finset.sum_congr rfl (fun i hi => Measure.prod_apply_symm (hSm i hi))
      _ = ∫⁻ y, ∑ i ∈ G, volume ((fun q => (q, y)) ⁻¹' S i) :=
          (lintegral_finsetSum G (fun i hi => measurable_measure_prodMk_right (hSm i hi))).symm
      _ ≤ ∫⁻ y, (Icc (-1 : ℝ) 1).indicator (fun _ => c) y := lintegral_mono hup
      _ = c * volume (Icc (-1 : ℝ) 1) := lintegral_indicator_const measurableSet_Icc c
      _ = ENNReal.ofReal (lam / 4) * ∑ i ∈ G, volume (Z i) := by
        rw [Real.volume_Icc, hc, mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
  rw [ENNReal.mul_le_mul_iff_left hpos hfin, ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  linarith

end WangZahlLot.Obl.wz_grains_nonsingular_slices
