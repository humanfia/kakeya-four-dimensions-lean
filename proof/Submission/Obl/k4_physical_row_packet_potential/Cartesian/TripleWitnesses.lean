-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/TripleWitnesses.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Spanning witness triples for `cartesian_whole_state_row`.

From a finite family of states with
* a small unqualified fraction in every state,
* per-state strip breadth of the planar velocities,
* per-state domination of the velocity law by one palette `πv`,
choose ONE triple `J` of planar velocities (centers of fine bins) with lifted
determinant at least `(wv/2)²`, and a subfamily `Ωst` of states carrying at
least the fraction `((1 - ηq)³ - 2 ps) / Kr³` of the family mass, such that
every state of `Ωst` has a qualified witness in each of the three bins.
-/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.TripleSpanning

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- The bin of a planar velocity at width `pv`. -/
def velBinOf (pv : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℤ := fun k => ⌊x k / pv⌋

/-- The center of a velocity bin. -/
def binCenter (pv : ℝ) (b : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun k => pv * ((b k : ℝ) + 1 / 2))

theorem measurable_velBinOf (pv : ℝ) : Measurable (velBinOf pv) := by
  apply measurable_pi_iff.mpr
  intro k
  have hk : Measurable fun x : Fin 2 → ℝ => x k / pv := by fun_prop
  exact Int.measurable_floor.comp hk

theorem binCenter_dist {pv : ℝ} (hpv : 0 < pv) (x : Fin 2 → ℝ) (k : Fin 2) :
    |x k - binCenter pv (velBinOf pv x) k| ≤ pv / 2 := by
  have hlo := Int.floor_le (x k / pv)
  have hhi := Int.lt_floor_add_one (x k / pv)
  have h1 : pv * (⌊x k / pv⌋ : ℝ) ≤ x k := by
    have := mul_le_mul_of_nonneg_left hlo hpv.le
    rwa [mul_div_cancel₀ _ hpv.ne'] at this
  have h2 : x k < pv * ((⌊x k / pv⌋ : ℝ) + 1) := by
    have := mul_lt_mul_of_pos_left hhi hpv
    rwa [mul_div_cancel₀ _ hpv.ne'] at this
  change |x k - pv * ((⌊x k / pv⌋ : ℝ) + 1 / 2)| ≤ pv / 2
  rw [abs_le]
  constructor <;> nlinarith

theorem binCenter_norm_dist {pv : ℝ} (hpv : 0 < pv) (x : Fin 2 → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 2)) - binCenter pv (velBinOf pv x)‖ ≤ pv := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left hpv.le, Fin.sum_univ_two]
  have h0 := binCenter_dist hpv x 0
  have h1 := binCenter_dist hpv x 1
  simp only [PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  have e0 : (x 0 - binCenter pv (velBinOf pv x) 0) ^ 2 ≤ (pv / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : (x 1 - binCenter pv (velBinOf pv x) 1) ^ 2 ≤ (pv / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

open Classical in
/-- **One spanning triple of qualified witnesses**, from domination of the
qualified velocity BINS by one bin palette `π`. -/
theorem exists_spanning_witness_triple_of_bins {Λ σ : Type*} [MeasurableSpace Λ] [MeasurableSpace σ]
    [MeasurableSingletonClass σ]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ] (st : Λ × ℝ → σ) (hst : Measurable st)
    (v : Λ → Fin 2 → ℝ) (hv : Measurable v)
    (Fam : Finset σ) (Q : Set (Λ × ℝ)) (hQ : MeasurableSet Q)
    {ηq ps : ℝ} (hηq : 0 ≤ ηq) (hps : 0 ≤ ps)
    (hqual : ∀ D ∈ Fam, μ (st ⁻¹' {D} \ Q) ≤ ENNReal.ofReal ηq * μ (st ⁻¹' {D}))
    {wv pv : ℝ} (hwv : 0 < wv) (hpv : 0 < pv) (hpvw : pv ≤ wv / 2)
    (hstrip : ∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      μ (st ⁻¹' {D} ∩ {x | |⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤ wv}) ≤
        ENNReal.ofReal ps * μ (st ⁻¹' {D}))
    (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π] {Kr : ℝ}
    (hdomBin : ∀ D ∈ Fam, ∀ b : Fin 2 → ℤ,
      μ ({x | velBinOf pv (v x.1) = b} ∩ (st ⁻¹' {D} ∩ Q)) ≤
        ENNReal.ofReal Kr * μ (st ⁻¹' {D}) * π {b}) :
    ∃ (J : Fin 3 → Fin 2 → ℝ) (Ωst : Finset σ), Ωst ⊆ Fam ∧
      (Ωst.Nonempty → (wv / 2) ^ 2 ≤ |(liftMatrix J).det|) ∧
      (∀ D ∈ Ωst, ∀ axis : Fin 3, ∃ w ∈ Q, st w = D ∧ ∀ k, |v w.1 k - J axis k| ≤ pv / 2) ∧
      ENNReal.ofReal ((1 - ηq) ^ 3 - 2 * ps) * ∑ D ∈ Fam, μ (st ⁻¹' {D}) ≤
        ENNReal.ofReal Kr ^ 3 * ∑ D ∈ Ωst, μ (st ⁻¹' {D}) := by
  set bin : Λ × ℝ → (Fin 2 → ℤ) := fun x => velBinOf pv (v x.1) with hbin_def
  have hbin : Measurable bin := (measurable_velBinOf pv).comp (hv.comp measurable_fst)
  let ρ : σ → Measure (Fin 2 → ℤ) := fun D => (μ.restrict (st ⁻¹' {D} ∩ Q)).map bin
  have hDQ (D : σ) : MeasurableSet (st ⁻¹' {D} ∩ Q) := (hst (measurableSet_singleton D)).inter hQ
  have hρ (D : σ) (A : Set (Fin 2 → ℤ)) : ρ D A = μ (bin ⁻¹' A ∩ (st ⁻¹' {D} ∩ Q)) := by
    simp only [ρ]
    rw [Measure.map_apply hbin ((Set.to_countable A).measurableSet),
      Measure.restrict_apply (hbin ((Set.to_countable A).measurableSet))]
  haveI (D : σ) : IsFiniteMeasure (ρ D) := by simp only [ρ]; infer_instance
  let m : σ → ℝ≥0∞ := fun D => μ (st ⁻¹' {D})
  have hm : ∀ D ∈ Fam, m D ≠ ⊤ := fun D _ => measure_ne_top _ _
  -- palette domination of the bin laws
  have hdom : ∀ D ∈ Fam, ∀ b, ρ D {b} ≤ ENNReal.ofReal Kr * m D * π {b} := by
    intro D hD b
    rw [hρ]
    exact hdomBin D hD b
  -- strip breadth of the bin centers
  have hstripρ : ∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      ρ D {b | |⟪n, binCenter pv b⟫ - s| ≤ wv / 2} ≤ ENNReal.ofReal ps * m D := by
    intro D hD n hn s
    rw [hρ]
    refine (measure_mono ?_).trans (hstrip D hD n hn s)
    rintro x ⟨hx1, hx2, -⟩
    refine ⟨hx2, ?_⟩
    simp only [mem_preimage, mem_setOf_eq] at hx1 ⊢
    have hd := binCenter_norm_dist hpv (v x.1)
    have hcs : |⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2)) -
        binCenter pv (velBinOf pv (v x.1))⟫| ≤ pv := by
      calc _ ≤ ‖n‖ * ‖(WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2)) -
            binCenter pv (velBinOf pv (v x.1))‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * pv := by rw [hn]; gcongr
        _ = pv := one_mul _
    rw [inner_sub_right] at hcs
    have := abs_sub_abs_le_abs_sub (⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s)
      (⟪n, binCenter pv (velBinOf pv (v x.1))⟫ - s)
    rw [abs_le] at hcs hx1 ⊢
    constructor <;> linarith [hcs.1, hcs.2, hx1.1, hx1.2]
  -- per-state spanning mass
  set G : Set ((Fin 2 → ℤ) × (Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
    {t | (wv / 2) ^ 2 ≤ |(liftMatrix (tripleVel (binCenter pv) t)).det|} with hG
  have hspan : ∀ D ∈ Fam, ENNReal.ofReal ((1 - ηq) ^ 3 - 2 * ps) * m D ^ 3 ≤
      ((ρ D).prod ((ρ D).prod (ρ D))) G := by
    intro D hD
    have hbad := prod3_small_det_le (ρ D) (binCenter pv) (by linarith : (0 : ℝ) < wv / 2)
      (ENNReal.ofReal ps) (m D)
      (by rw [hρ]; exact measure_mono (fun x hx => hx.2.1)) (hstripρ D hD)
    have hcompl : Gᶜ = {t | |(liftMatrix (tripleVel (binCenter pv) t)).det| < (wv / 2) ^ 2} := by
      ext t; simp [G, not_le]
    have huniv : ((ρ D).prod ((ρ D).prod (ρ D))) univ = (ρ D univ) ^ 3 := by
      rw [← univ_prod_univ, Measure.prod_prod, ← univ_prod_univ, Measure.prod_prod]
      ring
    have hρuniv : ENNReal.ofReal (1 - ηq) * m D ≤ ρ D univ := by
      rw [hρ, preimage_univ, univ_inter]
      have hsplit : m D ≤ μ (st ⁻¹' {D} ∩ Q) + μ (st ⁻¹' {D} \ Q) := by
        simp only [m]
        rw [measure_inter_add_diff _ hQ]
      by_cases hη1 : ηq ≤ 1
      · rw [ENNReal.ofReal_sub _ hηq, ENNReal.ofReal_one, ENNReal.sub_mul (fun _ _ => hm D hD),
          one_mul]
        exact tsub_le_iff_right.mpr (hsplit.trans (add_le_add le_rfl (hqual D hD)))
      · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]
        exact zero_le
    by_cases hc : (1 - ηq) ^ 3 - 2 * ps ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hc, zero_mul]
      exact zero_le
    · push_neg at hc
      have hη1 : 0 ≤ 1 - ηq := by
        by_contra h
        push_neg at h
        have : (1 - ηq) ^ 3 < 0 := Odd.pow_neg (by decide) h
        linarith
      have hmain : ENNReal.ofReal ((1 - ηq) ^ 3) * m D ^ 3 ≤
          ((ρ D).prod ((ρ D).prod (ρ D))) G + 2 * ENNReal.ofReal ps * m D ^ 3 := by
        calc ENNReal.ofReal ((1 - ηq) ^ 3) * m D ^ 3 = (ENNReal.ofReal (1 - ηq) * m D) ^ 3 := by
              rw [ENNReal.ofReal_pow hη1]; ring
          _ ≤ (ρ D univ) ^ 3 := by gcongr
          _ = ((ρ D).prod ((ρ D).prod (ρ D))) univ := huniv.symm
          _ ≤ ((ρ D).prod ((ρ D).prod (ρ D))) G + ((ρ D).prod ((ρ D).prod (ρ D))) Gᶜ := by
              rw [← union_compl_self G]; exact measure_union_le _ _
          _ ≤ _ := by rw [hcompl]; gcongr
      have hsub : ENNReal.ofReal ((1 - ηq) ^ 3 - 2 * ps) =
          ENNReal.ofReal ((1 - ηq) ^ 3) - 2 * ENNReal.ofReal ps := by
        rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]
      rw [hsub, ENNReal.sub_mul (fun _ _ => ENNReal.pow_ne_top (hm D hD))]
      exact tsub_le_iff_right.mpr (by rw [mul_assoc] at hmain ⊢; exact hmain)
  -- the common triple
  obtain ⟨t, ht⟩ := exists_common_bin_triple Fam m hm ρ π (ENNReal.ofReal Kr) ENNReal.ofReal_ne_top
    hdom G _ hspan
  let Ωst := Fam.filter (fun D => t ∈ G ∧ ρ D {t.1} ≠ 0 ∧ ρ D {t.2.1} ≠ 0 ∧ ρ D {t.2.2} ≠ 0)
  refine ⟨tripleVel (binCenter pv) t, Ωst, Finset.filter_subset _ _, ?_, ?_, ht⟩
  · rintro ⟨D, hD⟩
    exact (Finset.mem_filter.mp hD).2.1
  · intro D hD axis
    have hpos := (Finset.mem_filter.mp hD).2.2
    have hwit (b : Fin 2 → ℤ) (hb : ρ D {b} ≠ 0) :
        ∃ w ∈ Q, st w = D ∧ ∀ k, |v w.1 k - binCenter pv b k| ≤ pv / 2 := by
      rw [hρ] at hb
      obtain ⟨w, hw1, hw2, hw3⟩ := nonempty_of_measure_ne_zero hb
      refine ⟨w, hw3, hw2, fun k => ?_⟩
      have hbw : velBinOf pv (v w.1) = b := hw1
      rw [← hbw]
      exact binCenter_dist hpv (v w.1) k
    fin_cases axis
    · exact hwit t.1 hpos.1
    · exact hwit t.2.1 hpos.2.1
    · exact hwit t.2.2 hpos.2.2

open Classical in
/-- **One spanning triple of qualified witnesses on a substantial state family.** -/
theorem exists_spanning_witness_triple {Λ σ : Type*} [MeasurableSpace Λ] [MeasurableSpace σ]
    [MeasurableSingletonClass σ]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ] (st : Λ × ℝ → σ) (hst : Measurable st)
    (v : Λ → Fin 2 → ℝ) (hv : Measurable v)
    (Fam : Finset σ) (Q : Set (Λ × ℝ)) (hQ : MeasurableSet Q)
    {ηq ps : ℝ} (hηq : 0 ≤ ηq) (hps : 0 ≤ ps)
    (hqual : ∀ D ∈ Fam, μ (st ⁻¹' {D} \ Q) ≤ ENNReal.ofReal ηq * μ (st ⁻¹' {D}))
    {wv pv : ℝ} (hwv : 0 < wv) (hpv : 0 < pv) (hpvw : pv ≤ wv / 2)
    (hstrip : ∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      μ (st ⁻¹' {D} ∩ {x | |⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤ wv}) ≤
        ENNReal.ofReal ps * μ (st ⁻¹' {D}))
    (πv : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure πv] {Kr : ℝ}
    (hpal : ∀ D ∈ Fam, ∀ B : Set (Fin 2 → ℝ), MeasurableSet B →
      μ (st ⁻¹' {D} ∩ {x | v x.1 ∈ B}) ≤ ENNReal.ofReal Kr * μ (st ⁻¹' {D}) * πv B) :
    ∃ (J : Fin 3 → Fin 2 → ℝ) (Ωst : Finset σ), Ωst ⊆ Fam ∧
      (Ωst.Nonempty → (wv / 2) ^ 2 ≤ |(liftMatrix J).det|) ∧
      (∀ D ∈ Ωst, ∀ axis : Fin 3, ∃ w ∈ Q, st w = D ∧ ∀ k, |v w.1 k - J axis k| ≤ pv / 2) ∧
      ENNReal.ofReal ((1 - ηq) ^ 3 - 2 * ps) * ∑ D ∈ Fam, μ (st ⁻¹' {D}) ≤
        ENNReal.ofReal Kr ^ 3 * ∑ D ∈ Ωst, μ (st ⁻¹' {D}) := by
  refine exists_spanning_witness_triple_of_bins μ st hst v hv Fam Q hQ hηq hps hqual hwv hpv hpvw
    hstrip (πv.map (velBinOf pv)) (fun D hD b => ?_)
  rw [Measure.map_apply (measurable_velBinOf pv) (measurableSet_singleton b)]
  refine (measure_mono ?_).trans (hpal D hD _ ((measurable_velBinOf pv) (measurableSet_singleton b)))
  rintro x ⟨hx1, hx2, -⟩
  exact ⟨hx2, hx1⟩

/-- Entries of a `3 × 3` adjugate are bounded by twice the squared entry bound. -/
theorem adjugate_fin_three_bound (A : Matrix (Fin 3) (Fin 3) ℝ) {V : ℝ}
    (hA : ∀ i k, |A i k| ≤ V) (i k : Fin 3) : |A.adjugate i k| ≤ 2 * V ^ 2 := by
  have hV : 0 ≤ V := (abs_nonneg _).trans (hA 0 0)
  have h2 (a b c d : ℝ) (ha : |a| ≤ V) (hb : |b| ≤ V) (hc : |c| ≤ V) (hd : |d| ≤ V) :
      |a * b - c * d| ≤ 2 * V ^ 2 := by
    calc |a * b - c * d| ≤ |a * b| + |c * d| := abs_sub _ _
      _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]
      _ ≤ V * V + V * V := by gcongr
      _ = 2 * V ^ 2 := by ring
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases k <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | exact h2 _ _ _ _ (hA _ _) (hA _ _) (hA _ _) (hA _ _)
    | (rw [show ∀ a b c d : ℝ, -(a * b) + c * d = c * d - a * b from fun a b c d => by ring]
       exact h2 _ _ _ _ (hA _ _) (hA _ _) (hA _ _) (hA _ _))

/-- A lifted triple with determinant at least `d₀` has a bounded inverse frame. -/
theorem liftMatrix_inverse_bound (J : Fin 3 → Fin 2 → ℝ) {V d₀ : ℝ} (hV1 : 1 ≤ V)
    (hJ : ∀ i k, |J i k| ≤ V) (hd0 : 0 < d₀) (hdet : d₀ ≤ |(liftMatrix J).det|) :
    liftMatrix J * (liftMatrix J)⁻¹ = 1 ∧ ∀ i k, |(liftMatrix J)⁻¹ i k| ≤ 2 * V ^ 2 / d₀ := by
  have hdet0 : (liftMatrix J).det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdet; linarith
  refine ⟨Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0), fun i k => ?_⟩
  have hA : ∀ r c, |liftMatrix J r c| ≤ V := by
    intro r c
    rw [liftMatrix_apply]
    fin_cases r
    · simp [lift]; exact hV1
    · simpa [lift] using hJ c 0
    · simpa [lift] using hJ c 1
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', abs_mul, abs_inv,
    inv_mul_le_iff₀ (abs_pos.mpr hdet0)]
  calc |(liftMatrix J).adjugate i k| ≤ 2 * V ^ 2 := adjugate_fin_three_bound _ hA i k
    _ ≤ |(liftMatrix J).det| * (2 * V ^ 2 / d₀) := by
      rw [mul_div_assoc', le_div_iff₀ hd0]
      have : 0 ≤ 2 * V ^ 2 := by positivity
      nlinarith

/-- The finite box of velocity bins met by velocities bounded by `V`. -/
def binBox (pv V : ℝ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(⌈V / pv⌉ + 1)) (⌈V / pv⌉ + 1))

theorem velBinOf_mem_binBox {pv V : ℝ} (hpv : 0 < pv) {x : Fin 2 → ℝ}
    (hx : ∀ k, |x k| ≤ V) : velBinOf pv x ∈ binBox pv V := by
  rw [binBox, Fintype.mem_piFinset]
  intro k
  rw [Finset.mem_Icc]
  have hk := abs_le.mp (hx k)
  have h1 : -(V / pv) ≤ x k / pv := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right hk.1 hpv.le
  have h2 : x k / pv ≤ V / pv := div_le_div_of_nonneg_right hk.2 hpv.le
  constructor
  · have hfl : ⌊-(V / pv)⌋ ≤ ⌊x k / pv⌋ := Int.floor_mono h1
    have hc : -⌈V / pv⌉ ≤ ⌊-(V / pv)⌋ := by
      rw [Int.floor_neg]
    change -(⌈V / pv⌉ + 1) ≤ ⌊x k / pv⌋
    omega
  · have hfl : ⌊x k / pv⌋ ≤ ⌈V / pv⌉ := (Int.floor_le_ceil _).trans (Int.ceil_mono h2)
    change ⌊x k / pv⌋ ≤ ⌈V / pv⌉ + 1
    omega

/-- The uniform probability on the bin box. -/
def binUniform (pv V : ℝ) : Measure (Fin 2 → ℤ) :=
  ((binBox pv V).card : ℝ≥0∞)⁻¹ • Measure.count.restrict (binBox pv V : Set (Fin 2 → ℤ))

theorem binUniform_probability (pv V : ℝ) (hne : (binBox pv V).Nonempty) :
    IsProbabilityMeasure (binUniform pv V) := by
  constructor
  rw [binUniform, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.count_apply_finset, smul_eq_mul]
  have hc : ((binBox pv V).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  exact ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _)

theorem binUniform_singleton {pv V : ℝ} {b : Fin 2 → ℤ} (hb : b ∈ binBox pv V) :
    binUniform pv V {b} = ((binBox pv V).card : ℝ≥0∞)⁻¹ := by
  rw [binUniform, Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton b),
    smul_eq_mul]
  have : ({b} : Set (Fin 2 → ℤ)) ∩ (binBox pv V : Set (Fin 2 → ℤ)) = {b} :=
    inter_eq_left.mpr (by simpa using hb)
  rw [this, Measure.count_singleton, mul_one]

/-- **Coarse-bin witness triple.** Bounded velocities on the qualified
events dominate their bin laws by the uniform law on the bin box, with
`Kr` the number of bins; no velocity palette is needed. -/
theorem exists_spanning_witness_triple_uniform {Λ σ : Type*} [MeasurableSpace Λ]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ] (st : Λ × ℝ → σ) (hst : Measurable st)
    (v : Λ → Fin 2 → ℝ) (hv : Measurable v)
    (Fam : Finset σ) (Q : Set (Λ × ℝ)) (hQ : MeasurableSet Q)
    {ηq ps : ℝ} (hηq : 0 ≤ ηq) (hps : 0 ≤ ps)
    (hqual : ∀ D ∈ Fam, μ (st ⁻¹' {D} \ Q) ≤ ENNReal.ofReal ηq * μ (st ⁻¹' {D}))
    {wv pv : ℝ} (hwv : 0 < wv) (hpv : 0 < pv) (hpvw : pv ≤ wv / 2)
    (hstrip : ∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      μ (st ⁻¹' {D} ∩ {x | |⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤ wv}) ≤
        ENNReal.ofReal ps * μ (st ⁻¹' {D}))
    {Vmax : ℝ} (hVmax : 0 ≤ Vmax) (hvb : ∀ x ∈ Q, ∀ k, |v x.1 k| ≤ Vmax) :
    ∃ (J : Fin 3 → Fin 2 → ℝ) (Ωst : Finset σ), Ωst ⊆ Fam ∧
      (Ωst.Nonempty → (wv / 2) ^ 2 ≤ |(liftMatrix J).det|) ∧
      (∀ D ∈ Ωst, ∀ axis : Fin 3, ∃ w ∈ Q, st w = D ∧ ∀ k, |v w.1 k - J axis k| ≤ pv / 2) ∧
      ENNReal.ofReal ((1 - ηq) ^ 3 - 2 * ps) * ∑ D ∈ Fam, μ (st ⁻¹' {D}) ≤
        ENNReal.ofReal ((binBox pv Vmax).card : ℝ) ^ 3 * ∑ D ∈ Ωst, μ (st ⁻¹' {D}) := by
  have hne : (binBox pv Vmax).Nonempty :=
    ⟨velBinOf pv 0, velBinOf_mem_binBox hpv (fun k => by simpa using hVmax)⟩
  haveI := binUniform_probability pv Vmax hne
  refine exists_spanning_witness_triple_of_bins μ st hst v hv Fam Q hQ hηq hps hqual hwv hpv hpvw
    hstrip (binUniform pv Vmax) (fun D hD b => ?_)
  by_cases hb : b ∈ binBox pv Vmax
  · rw [binUniform_singleton hb, ENNReal.ofReal_natCast]
    have hc : ((binBox pv Vmax).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hne).ne'
    calc μ ({x | velBinOf pv (v x.1) = b} ∩ (st ⁻¹' {D} ∩ Q)) ≤ μ (st ⁻¹' {D}) :=
          measure_mono (fun x hx => hx.2.1)
      _ = ((binBox pv Vmax).card : ℝ≥0∞) * μ (st ⁻¹' {D}) *
          ((binBox pv Vmax).card : ℝ≥0∞)⁻¹ := by
        rw [mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _), one_mul]
  · have hempty : {x | velBinOf pv (v x.1) = b} ∩ (st ⁻¹' {D} ∩ Q) = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx _ hxQ
      exact hb (hx ▸ velBinOf_mem_binBox hpv (hvb x hxQ))
    rw [hempty, measure_empty]
    exact zero_le

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
