-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.MeasureCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Defs

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, MeasureCut.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V I)

lemma volume_coordinate_level (t : ℝ) : volume {p : V | p 0 = t} = 0 := by
  have hm : MeasurableSet {p : Fin 3 → ℝ | p 0 = t} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage hm.nullMeasurableSet
  change volume {p : V | p 0 = t} = volume {p : Fin 3 → ℝ | p 0 = t} at h
  rw [h]
  exact Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) 0 t

/-- Lebesgue measure on a measurable subset of the unit ball can be cut to
any prescribed smaller mass by a coordinate half-space. -/
theorem exists_subset_volume {S : Set V} (hSm : MeasurableSet S) (hSI : S ⊆ I)
    {t : ENNReal} (ht : t ≤ volume S) :
    ∃ A : Set V, MeasurableSet A ∧ A ⊆ S ∧ volume A = t := by
  let f : V → ℝ := fun p => p 0
  have hf : Measurable f := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top
    (measure_ball_lt_top (μ := (volume : Measure V)) (x := (0 : V)) (r := 1)).ne
    (measure_mono hSI)
  let ν : Measure ℝ := (volume.restrict S).map f
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSfin
  let : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure ((volume.restrict S).map f))
  let : NullSingletonClass ν := ⟨fun a => by
    change (volume.restrict S).map f {a} = 0
    rw [Measure.map_apply hf (measurableSet_singleton a),
      Measure.restrict_apply ((measurableSet_singleton a).preimage hf)]
    exact measure_mono_null inter_subset_left (volume_coordinate_level a)⟩
  have hcut (a : ℝ) : ν (Iic a) = volume (S ∩ {p | p 0 ≤ a}) := by
    rw [Measure.map_apply hf measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage hf), inter_comm]
    rfl
  have hleft : S ∩ {p : V | p 0 ≤ -1} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp, hpa⟩
    have hn : ‖p‖ < 1 := by simpa using hSI hp
    have hb := PiLp.norm_apply_le p 0
    rw [Real.norm_eq_abs] at hb
    have := neg_le_abs (p 0)
    change p 0 ≤ -1 at hpa
    linarith
  have hright : S ∩ {p : V | p 0 ≤ 1} = S := by
    apply inter_eq_left.mpr
    intro p hp
    have hn : ‖p‖ < 1 := by simpa using hSI hp
    have hb : |p 0| ≤ ‖p‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le p 0)
    exact (le_abs_self _).trans (hb.trans hn.le)
  have hcont : ContinuousOn (fun a : ℝ => (ν (Iic a)).toReal) (Icc (-1) 1) := by
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic 1) ν :=
      (integrable_const (1 : ℝ)).integrableOn
    have hc' := hc.continuousOn_Iic_primitive_Iic (a₀ := (1 : ℝ))
    simpa only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] using
      hc'.mono (show Icc (-1 : ℝ) 1 ⊆ Iic 1 from fun _ h => h.2)
  have htin : t.toReal ∈ Icc ((ν (Iic (-1))).toReal) ((ν (Iic 1)).toReal) := by
    rw [hcut, hleft, measure_empty, ENNReal.toReal_zero, hcut, hright]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hSfin ht⟩
  obtain ⟨a, _, ha⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont htin
  refine ⟨S ∩ {p | p 0 ≤ a}, hSm.inter (measurableSet_le hf measurable_const),
    inter_subset_left, ?_⟩
  change (ν (Iic a)).toReal = t.toReal at ha
  rw [hcut] at ha
  have he := congrArg ENNReal.ofReal ha
  rwa [ENNReal.ofReal_toReal (ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left)),
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top hSfin ht)] at he

/-- A bounded measurable set contains any finite number of disjoint pieces
of a prescribed mass, provided their total mass fits. -/
theorem exists_disjoint_volume_pieces (m : ℕ) {S : Set V}
    (hSm : MeasurableSet S) (hSI : S ⊆ I) {t : ENNReal}
    (ht : (m : ENNReal) * t ≤ volume S) :
    ∃ A : Fin m → Set V,
      (∀ i, MeasurableSet (A i) ∧ A i ⊆ S ∧ volume (A i) = t) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) := by
  induction m generalizing S with
  | zero => exact ⟨Fin.elim0, by simp, by simp [Pairwise]⟩
  | succ m ih =>
    have htS : t ≤ volume S := by
      calc
        t = (1 : ENNReal) * t := (one_mul _).symm
        _ ≤ (m.succ : ENNReal) * t := mul_le_mul' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)) le_rfl
        _ ≤ volume S := ht
    obtain ⟨B, hBm, hBS, hBt⟩ := exists_subset_volume hSm hSI htS
    have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top
      (measure_ball_lt_top (μ := (volume : Measure V)) (x := (0 : V)) (r := 1)).ne
      (measure_mono hSI)
    have htfin : t ≠ ⊤ := ne_top_of_le_ne_top hSfin htS
    have hremain : (m : ENNReal) * t ≤ volume (S \ B) := by
      rw [measure_sdiff hBS hBm.nullMeasurableSet (by rw [hBt]; exact htfin), hBt]
      apply ENNReal.le_sub_of_add_le_right htfin
      simpa only [Nat.cast_succ, add_mul, one_mul] using ht
    obtain ⟨A, hA, hdisj⟩ := ih (hSm.diff hBm) (sdiff_subset.trans hSI) hremain
    refine ⟨Fin.cons B A, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hBm, hBS, hBt⟩
      · exact ⟨(hA j).1, (hA j).2.1.trans sdiff_subset, (hA j).2.2⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          exact disjoint_sdiff_right.mono_right (hA j').2.1
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _
          exact disjoint_sdiff_left.mono_left (hA i').2.1
        · intro hij
          exact hdisj (fun h => hij (congrArg Fin.succ h))

/-- Equal-volume pieces of a bounded measurable set. Coverage up to a null
set suffices for the incidence bookkeeping. -/
theorem exists_equal_volume_pieces (m : ℕ) (hm : 0 < m) {S : Set V}
    (hSm : MeasurableSet S) (hSI : S ⊆ I) :
    ∃ A : Fin m → Set V,
      (∀ i, MeasurableSet (A i) ∧ A i ⊆ S ∧ volume (A i) = (m : ENNReal)⁻¹ * volume S) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) := by
  apply exists_disjoint_volume_pieces m hSm hSI
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hm.ne') (by simp), one_mul]

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
