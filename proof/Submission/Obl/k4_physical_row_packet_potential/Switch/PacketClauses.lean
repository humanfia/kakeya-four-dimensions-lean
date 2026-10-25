-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/PacketClauses.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The six-switch curl bound of one old packet from its own
clauses, in the form of the frozen `PhysicalPotentialPacket`:

* states: the frozen `physicalCode` of `(packetBase, P/a)` at mesh `εs`;
* controls: planar velocity bins of width `pv`, with per-state palette
  domination `Kr π`;
* thin pencils: the frozen per-state strip breadth;
* base cap: the frozen base density ceiling;
* support: the frozen census of `(packetBase, P/a)` at meshes `(pc, wc)`;
* the field: degree `D`, coefficients `≤ AT`, fitting the parent rate on `S`.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.PacketInputs

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4PolynomialNorming
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Obl.k4_physical_row_packet_potential.PotentialFits
open scoped ENNReal

noncomputable section

namespace PacketSwitching

/-- The frozen state of an event: `physicalCode` of `(packetBase, P/a)`. -/
def packetState (T j : ℕ) (c u : P2) (P : Po) (a εs : ℝ) (z : Ev) : (Fin 3 → ℤ) × ℤ :=
  physicalCode (packetBase T j c u) (fun z => packetSignal P z / a) εs z

theorem continuous_packetBase (T j : ℕ) (c u : P2) : Continuous (packetBase T j c u) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [xp, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
      Matrix.tail_cons] <;>
    fun_prop

theorem continuous_packetSignal (P : Po) : Continuous (packetSignal P) := by
  unfold packetSignal
  apply (MvPolynomial.continuous_eval P).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [xp, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

theorem measurable_packetState (T j : ℕ) (c u : P2) (P : Po) (a εs : ℝ) :
    Measurable (packetState T j c u P a εs) := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro i
    exact Int.measurable_floor.comp
      (((PiLp.continuous_apply 2 _ i).comp (continuous_packetBase T j c u)).measurable.div_const _)
  · exact Int.measurable_floor.comp
      (((continuous_packetSignal P).div_const a).measurable.div_const _)

/-- **Curl bound of one old packet from its clauses.** -/
theorem packet_curl_from_clauses (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ (T j : ℕ) (c u : P2) (P : Po) (hP : P.totalDegree ≤ 2)
      (ν₀ : Measure Ln) [IsFiniteMeasure ν₀]
      (S : Set Ev) (hS : MeasurableSet S) (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1)
      (htime : ∀ z ∈ S, z.2 ∈ Icc (start T j) (start T j + clock T))
      (hpos : 0 < (ν₀.prod volume) S)
      (a K : ℝ) (ha : 0 < a) (hK : 1 ≤ K)
      (hbaseK : ∀ z ∈ S, ‖packetBase T j c u z‖ ≤ K)
      (hvK : ∀ z ∈ S, ‖v z.1‖ ≤ K)
      (hPK : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp z.1 t) P| ≤ K)
      (εs : ℝ) (hεs : 0 < εs)
      {σ : Type*} [MeasurableSpace σ] [MeasurableSingletonClass σ] [Countable σ]
      [StandardBorelSpace σ] (st : Ev → σ) (hstm : Measurable st)
      (hrefine : ∀ z z', st z = st z' →
        packetState T j c u P a εs z = packetState T j c u P a εs z')
      (pv : ℝ) (hpv : 0 < pv) (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π] (Kr : ENNReal)
      (hrect : ∀ k (A : Set (Fin 2 → ℤ)), MeasurableSet A →
        (ν₀.prod volume) ({z | st z = k ∧ velBin pv z.1 ∈ A} ∩ S) ≤
          Kr * (ν₀.prod volume) (st ⁻¹' {k} ∩ S) * π A)
      (wstrip : ℝ) (ps : ENNReal)
      (hstrip : ∀ k (n : P2) (t : ℝ), ‖n‖ = 1 →
        ((ν₀.prod volume).restrict S)
            {z | st z = k ∧ |inner ℝ n (v z.1) - t| ≤ wstrip} ≤
          ps * ((ν₀.prod volume).restrict S) {z | st z = k})
      (r : ℝ) (hr : 0 < r) (hrw : 2 * (K + 1) * (r + pv) ≤ wstrip) (hr4 : r + pv ≤ 1 / 4)
      (Kc : ENNReal)
      (hceil : ∀ U : Set P3, MeasurableSet U →
        ((ν₀.prod volume).restrict S) {z | packetBase T j c u z ∈ U} ≤ Kc * volume U)
      (pc wc : ℝ) (hpc : 0 < pc) (hwc : 0 < wc)
      (hfin : (occupied S (fun z i => packetBase T j c u z i)
        (fun z => packetSignal P z / a) pc wc).Finite)
      (Tf : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (Tf i).totalDegree ≤ D)
      (AT : ℝ) (hAT : 0 ≤ AT) (hcoeffT : ∀ i m, |(Tf i).coeff m| ≤ AT)
      (εfit : ℝ) (hεfit : 0 ≤ εfit)
      (hfit : ∀ z ∈ S, |ParentSignal.rate P z.1 z.2 -
        ∑ i, direction z.1 i * MvPolynomial.eval (fun k => packetBase T j c u z k) (Tf i)| ≤
          εfit)
      (q : ℝ) (hq : 0 < q) (hqh : q ≤ clock T)
      (widths : Fin 4 → ℝ)
      (hwidth0 : a / clock T * wc / 2 ≤ widths 0 ∧
        simHeightError D (clock T / q) εfit (εs + εs * K) (pv / 2)
          (a / clock T * εs + εs * (40 * K))
          ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (εs + εs * K + pv / 2)))) ^ D * AT)
          (max 1 (K + pv))
          (3 * ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (εs + εs * K + pv / 2)))) ^ D *
            ((D : ℝ) * AT))) ≤ widths 0)
      (hwidthB : ∀ k : Fin 3, pc / 2 ≤ widths k.succ ∧
        6 * (εs + εs * K + pv / 2) ≤ widths k.succ)
      (θ Λ Λ' : ℝ) (hθ : 0 < θ) (hΛ : 2 ≤ Λ) (hΛ' : 2 ≤ Λ')
      (hbudget : (Kr * ENNReal.ofReal (clock T / q)) ^ 6 *
            switchVolumeBound D cNorm hfin.toFinset widths r (max 1 (K + pv)) θ Λ +
          6 * (((ν₀.prod volume) S)⁻¹ * (ENNReal.ofReal q * ν₀ univ) + ps) +
          ((ν₀.prod volume) S)⁻¹ * (Kc * ENNReal.ofReal (K ^ 3)) * ENNReal.ofReal Λ'⁻¹ < 1),
      ∀ i k m, |(pderiv k (Tf i) - pderiv i (Tf k)).coeff m| ≤ Λ' ^ cCurl * θ := by
  obtain ⟨cNorm, cCurl, hcurl⟩ := packet_six_switch_curl_coefficients D
  refine ⟨cNorm, cCurl, ?_⟩
  intro T j c u P hP ν₀ _ S hS hSunit htime hpos a K ha hK hbaseK hvK hPK εs hεs σ _ _ _ _ st hstm
    hrefine pv hpv π _ Kr
    hrect wstrip ps hstrip r hr hrw hr4 Kc hceil pc wc hpc hwc hfin Tf hT AT hAT hcoeffT εfit
    hεfit hfit q hq hqh widths hwidth0 hwidthB θ Λ Λ' hθ hΛ hΛ' hbudget
  have hh := clock_pos T
  have hK0 : 0 ≤ K := by linarith
  -- the block lies in unit time
  obtain ⟨z₀, hz₀⟩ : S.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, measure_empty] at hpos
    exact lt_irrefl _ hpos
  have hstart0 : 0 ≤ start T j := by unfold start; positivity
  have hstart1 : start T j ≤ 1 := (htime z₀ hz₀).1.trans (hSunit hz₀).2.2
  have hclock1 : clock T ≤ 1 := by
    unfold clock
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  -- derived bounds
  have hbaseR : ∀ z ∈ S, ‖(fun i => packetBase T j c u z i)‖ ≤ K := by
    intro z hz
    refine (pi_norm_le_iff_of_nonneg hK0).mpr (fun i => ?_)
    exact (PiLp.norm_apply_le _ i).trans (hbaseK z hz)
  have hdirR : ∀ z ∈ S, ‖direction z.1‖ ≤ K := by
    intro z hz
    refine (pi_norm_le_iff_of_nonneg hK0).mpr (fun i => ?_)
    rw [Real.norm_eq_abs]
    fin_cases i
    · simp [direction]; exact hK
    · have := (PiLp.norm_apply_le (v z.1) 0).trans (hvK z hz)
      simpa [direction, v_apply_zero] using this
    · have := (PiLp.norm_apply_le (v z.1) 1).trans (hvK z hz)
      simpa [direction, v_apply_one] using this
  have hheightR : ∀ z ∈ S, |height1 T j P z.1| + 2 * |height2 T P z.1| ≤ 40 * K := by
    intro z hz
    have hsig : ∀ t ∈ Icc (0 : ℝ) 1, |Submission.Lib.K4ProjectedGroups.sig P z.1.2 t| ≤ K :=
      fun t ht => hPK z hz t ht
    have h1 := Submission.Lib.K4ProjectedGroups.abs_sc1_le hsig
    have h2 := Submission.Lib.K4ProjectedGroups.abs_sc2_le hsig
    simp only [height1, height2]
    have e1 : |Submission.Lib.K4ProjectedGroups.sc1 P z.1.2 +
        2 * start T j * Submission.Lib.K4ProjectedGroups.sc2 P z.1.2| ≤ 8 * K + 2 * 1 * (8 * K) := by
      calc
        _ ≤ |Submission.Lib.K4ProjectedGroups.sc1 P z.1.2| +
            |2 * start T j * Submission.Lib.K4ProjectedGroups.sc2 P z.1.2| := abs_add_le _ _
        _ = |Submission.Lib.K4ProjectedGroups.sc1 P z.1.2| +
            2 * start T j * |Submission.Lib.K4ProjectedGroups.sc2 P z.1.2| := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hstart0]
        _ ≤ 8 * K + 2 * 1 * (8 * K) := by gcongr
    have e2 : |clock T * Submission.Lib.K4ProjectedGroups.sc2 P z.1.2| ≤ 1 * (8 * K) := by
      rw [abs_mul, abs_of_pos hh]
      exact mul_le_mul hclock1 h2 (abs_nonneg _) zero_le_one
    linarith
  -- the field on the switching box
  set Rf := K + K + 7 * (εs + εs * K + pv / 2) with hRf
  have hRf0 : 0 ≤ Rf := by positivity
  obtain ⟨hfield, hspace⟩ := field_bounds_of_coeff Tf D hT hAT hRf0 hcoeffT
  -- thin pencils from strip breadth
  let V' : Ev → EuclideanSpace ℝ (Fin 2) := fun z => if ‖v z.1‖ ≤ K then v z.1 else 0
  have hV' : ∀ z, ‖V' z‖ ≤ K := by
    intro z
    by_cases hz : ‖v z.1‖ ≤ K
    · simp only [V', if_pos hz]; exact hz
    · simp only [V', if_neg hz, norm_zero]; exact hK0
  have hV'S : ∀ z ∈ S, V' z = v z.1 := fun z hz => by simp only [V', if_pos (hvK z hz)]
  have hstrip' : ∀ k (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖n‖ = 1 →
      ((ν₀.prod volume).restrict S) (st ⁻¹' {k} ∩ {z | |inner ℝ n (V' z) - t| ≤ wstrip}) ≤
        ps * ((ν₀.prod volume).restrict S) (st ⁻¹' {k}) := by
    intro k n t hn
    have hset : (st ⁻¹' {k} ∩ {z | |inner ℝ n (V' z) - t| ≤ wstrip}) ∩ S =
        {z | st z = k ∧ |inner ℝ n (v z.1) - t| ≤ wstrip} ∩ S := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, by rwa [hV'S z h3] at h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, by rwa [hV'S z h3]⟩, h3⟩
    rw [Measure.restrict_apply' hS, hset, ← Measure.restrict_apply' hS]
    exact hstrip k n t hn
  have hsub := state_subspace_ratio_of_strip_ratio ((ν₀.prod volume).restrict S) st V' K wstrip
    (r + pv) ps hV' hK0 (by linarith) hrw hr4 hstrip'
  have hratio : ∀ k (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
      (ν₀.prod volume)
          ((st ⁻¹' {k} ∩ {z | Metric.infDist (binDir pv (velBin pv z.1)) (W : Set _) < r}) ∩ S) ≤
        ps * (ν₀.prod volume) (st ⁻¹' {k} ∩ S) := by
    intro k W hW
    have h := hsub k W hW
    rw [Measure.restrict_apply' hS, Measure.restrict_apply' hS] at h
    refine (measure_mono ?_).trans h
    rintro z ⟨⟨hk, hd⟩, hzS⟩
    refine ⟨⟨hk, ?_⟩, hzS⟩
    simp only [mem_setOf_eq] at hd ⊢
    rw [hV'S z hzS]
    calc
      _ ≤ Metric.infDist (binDir pv (velBin pv z.1)) (W : Set _) +
          dist (liftDir (v z.1)) (binDir pv (velBin pv z.1)) :=
        Metric.infDist_le_infDist_add_dist
      _ < r + pv := by
        rw [dist_eq_norm, norm_sub_rev]
        exact add_lt_add_of_lt_of_le hd (binDir_dist_le hpv z.1)
  -- states share base and height
  have hgeom : ∀ z ∈ S, ∀ z' ∈ S, st z = st z' →
      ‖(fun i => packetBase T j c u z i) - (fun i => packetBase T j c u z' i)‖ ≤ εs ∧
        |packetSignal P z / clock T - packetSignal P z' / clock T| ≤ a / clock T * εs := by
    intro z hz z' hz' hzz
    obtain ⟨h1, h2⟩ := physicalCode_geom (packetBase T j c u) (fun z => packetSignal P z / a)
      hεs (hrefine z z' hzz)
    refine ⟨h1, ?_⟩
    have heq : packetSignal P z / clock T - packetSignal P z' / clock T =
        a / clock T * (packetSignal P z / a - packetSignal P z' / a) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (div_pos ha hh)]
    exact mul_le_mul_of_nonneg_left h2 (div_pos ha hh).le
  -- the support cover
  have hcover := census_box_cover S (fun z i => packetBase T j c u z i)
    (fun z => packetSignal P z / a) hpc hwc (div_pos ha hh) hfin
  -- apply the packet switching
  apply hcurl T j c u P hP ν₀ S hS hSunit htime hpos st hstm
    (velBin pv) (measurable_velBin pv) (binDir pv) π Kr ps r (max 1 (K + pv)) hr
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (fun k A hA => hrect k A hA) hratio
    (fun z hz i => binDir_coord_le hpv (hvK z hz) i) Tf hT q hq hqh εfit εs
    (a / clock T * εs) (pv / 2)
    ((D + 1 : ℕ) * (max 1 (3 * Rf)) ^ D * AT)
    (3 * ((D + 1 : ℕ) * (max 1 (3 * Rf)) ^ D * ((D : ℝ) * AT))) K K (40 * K) hεfit hεs.le
    (by positivity) (by positivity) (by positivity) (by positivity) hK0 (by positivity)
    (fun z hz => by simpa only [norm_sub_rev] using (direction_binDir_le hpv z.1)) hfit
    hbaseR hdirR hheightR hfield hspace hgeom
    {y | ∃ x ∈ S, y = ((fun i => packetBase T j c u x i), a / clock T * (packetSignal P x / a))}
    (fun z hz => ⟨z, hz, by
      congr 1
      field_simp⟩)
    hfin.toFinset (censusCenter pc wc (a / clock T)) widths
    (fun y hy => by
      obtain ⟨k, hk, hbox⟩ := hcover y hy
      refine ⟨k, hk, fun i => (hbox i).trans ?_⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [censusWidth, Fin.cons_zero]
        have := hwidth0.1
        linarith
      · simp only [censusWidth, Fin.cons_succ]
        exact (hwidthB i).1)
    hwidth0.2 (fun k => (hwidthB k).2) K hK (Kc * ENNReal.ofReal (K ^ 3))
    (cap_of_ceiling _ (packetBase T j c u) (continuous_packetBase T j c u).measurable hceil
      (by linarith))
    (fun z hz i => (PiLp.norm_apply_le _ i).trans (hbaseK z hz)) θ Λ Λ' hθ hΛ hΛ' hbudget

end PacketSwitching

end

end Submission.Obl.k4_physical_row_packet_potential.Switch
