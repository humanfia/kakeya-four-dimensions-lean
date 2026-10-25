import Submission.Obl.k4_critical_conditional_row_preparation.HistorySetup
import Submission.Obl.k4_critical_conditional_row_preparation.NormalizedTransport

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
local instance {ι : Type*} : MeasurableSpace (Option ι) := ⊤
local instance {ι : Type*} : DiscreteMeasurableSpace (Option ι) := ⟨fun _ => trivial⟩
namespace Data
namespace HistoryData
variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s : ℝ}
    (D : cfg.HistoryData k s)

def parentCurrent (τ : Measure (α × ℝ)) (i : Fin (cfg.n k s)) : Measure (α × ℝ) :=
  τ.restrict {p | D.parentTag p = some i}

theorem parentCurrent_le_original (h : cfg.Valid) (a : cfg.AssignmentLevel k s)
    (deep : cfg.AssignmentLevel k (3 * s)) (τ : Measure (α × ℝ)) (hτ : τ ≤ cfg.ρ k)
    (i : Fin (cfg.n k s)) : D.parentCurrent τ i ≤
      (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) := by
  have hcur : D.parentCurrent τ i ≤ cfg.ρ k := Measure.restrict_le_self.trans hτ
  have hcurμ : D.parentCurrent τ i ≤ cfg.μ k := hcur.trans (h.basic k).2.2.2.2.1
  have hparent : ∀ᵐ p ∂D.parentCurrent τ i, D.parentTag p = some i :=
    ae_restrict_mem ((D.measurable_parentTag deep) (measurableSet_singleton (some i)))
  have hnest := (a.deep_parent_ae h deep D.parent D.parent_assignment D.parent_interval).filter_mono
    (MeasureTheory.ae_mono hcurμ)
  have hsupp : ∀ᵐ p ∂D.parentCurrent τ i,
      p ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i) := by
    filter_upwards [hparent, hnest] with p hp hn
    obtain ⟨j, hj, hi⟩ := (D.parentTag_some p i).mp hp
    have hd := (coverLabel_eq_some _ deep.disjoint_halfEvents p j).mp hj
    have hc := hn j hd
    rw [hi] at hc
    exact cfg.halfEvent_subset k s i hc
  calc
    _ = (D.parentCurrent τ i).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) :=
      (Measure.restrict_eq_self_of_ae_mem hsupp).symm
    _ ≤ _ := Measure.restrict_mono_measure hcur _

theorem parentCurrent_row_constraint (h : cfg.Valid) (a : cfg.AssignmentLevel k s)
    (deep : cfg.AssignmentLevel k (3 * s)) (τ : Measure (α × ℝ)) (hτ : τ ≤ cfg.ρ k)
    (i : Fin (cfg.n k s)) (η : ℝ) (hη : 0 ≤ η)
    (hb : 32 * cfg.K k ^ 5 ≤ cfg.N k ^ η)
    (he : 2 * cfg.K k * cfg.N k ^ (-(3 * s)) / cfg.timeLength k (3 * s) +
      24 * cfg.K k ^ 5 * cfg.timeLength k (3 * s) +
      8 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) ≤ cfg.N k ^ (-s)) :
    ∀ᵐ p ∂D.parentCurrent τ i, (∀ e, |D.row p e| ≤ cfg.N k ^ η) ∧
      |D.row p 0 + cfg.b k p.1 3 * D.row p 1 - cfg.b k p.1 5| ≤ cfg.N k ^ η * cfg.N k ^ (-s) := by
  have hcur := D.parentCurrent_le_original h a deep τ hτ i
  have hcurμ : D.parentCurrent τ i ≤ cfg.μ k :=
    (hcur.trans Measure.restrict_le_self).trans (h.basic k).2.2.2.2.1
  have hparent : ∀ᵐ p ∂D.parentCurrent τ i, D.parentTag p = some i :=
    ae_restrict_mem ((D.measurable_parentTag deep) (measurableSet_singleton (some i)))
  have hdef := (a.horizontal_equation i).filter_mono (MeasureTheory.ae_mono hcurμ)
  filter_upwards [hparent, hdef, a.ae_goodArms h i (D.parentCurrent τ i) hcur] with p hp hd hv
  obtain ⟨j, hj, _⟩ := (D.parentTag_some p i).mp hp
  have hdeep := cfg.halfEvent_subset k (3 * s) j
    ((coverLabel_eq_some _ deep.disjoint_halfEvents p j).mp hj)
  have hrow : D.row p = cfg.frozenRow k (3 * s) j (D.entry j) := by
    simp only [row, rowValue, hj, Option.elim_some]
  rw [hrow]
  constructor
  · intro e
    exact (deep.frozenRow_bound h j (D.entry j) (D.entry_bound j) e).trans hb
  · apply (deep.frozenRow_error h j (D.entry j) (D.entry_bound j) (D.entry_fit j)
      p.1 hdeep.1 p.2 hdeep.2 hv.2 hd).trans
    exact he.trans (le_mul_of_one_le_left (Real.rpow_nonneg (by linarith [h.scale k]) _)
      (Real.one_le_rpow (by linarith [h.scale k]) hη))

/-- The history's physical pair code is exactly the chosen original parent's
normalized fine position, coordinate by coordinate. -/
theorem qcode_pair_of_parent (p : α × ℝ) (i : Fin (cfg.n k s))
    (hi : D.parentTag p = some i) :
    D.qcode (cfg.N k ^ (-(200 * s))) p =
      (cfg.physicalPosition k s i p 0, cfg.physicalPosition k s i p 1) := by
  rw [D.qcode_of_parentTag _ p i hi]
  simp only [basePair, physicalPosition, Matrix.cons_val_zero, Matrix.cons_val_one, div_div]

/-- Forgetting the deep label is exactly the parent/position/row-bin state. -/
theorem forget_state_iff (p : α × ℝ) (i : Fin (cfg.n k s)) (q r : Fin 2 → ℤ) :
    D.forget (cfg.N k ^ (-s)) (D.state (cfg.N k ^ (-(200 * s))) p) =
        (some i, ((q 0, q 1), r)) ↔
      D.parentTag p = some i ∧ cfg.physicalPosition k s i p = q ∧
        (fun e => ⌊D.row p e / cfg.N k ^ (-s)⌋) = r := by
  change (D.parentTag p, (D.qcode (cfg.N k ^ (-(200 * s))) p,
      (fun e => ⌊D.row p e / cfg.N k ^ (-s)⌋))) = (some i, ((q 0, q 1), r)) ↔ _
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hi, hq, hr⟩
    rw [D.qcode_pair_of_parent p i hi] at hq
    refine ⟨hi, ?_, hr⟩
    funext e
    fin_cases e
    · exact congrArg Prod.fst hq
    · exact congrArg Prod.snd hq
  · rintro ⟨hi, hq, hr⟩
    refine ⟨hi, ?_, hr⟩
    rw [D.qcode_pair_of_parent p i hi, hq]

/-- A cap on forgotten history states restricts to the actual parent current
with the original physical Row position and original palette. -/
theorem parentCurrent_conditional_cap (h : cfg.Valid) (deep : cfg.AssignmentLevel k (3 * s))
    (τ : Measure (α × ℝ)) (C : ENNReal)
    (hcap : ∀ u (v : ℤ), τ {p | D.forget (cfg.N k ^ (-s))
        (D.state (cfg.N k ^ (-(200 * s))) p) = u ∧
        ⌊cfg.b k p.1 3 / cfg.N k ^ (-(200 * s))⌋ = v} ≤
      C * cfg.π k (Ico ((v : ℝ) * cfg.N k ^ (-(200 * s)))
        (((v : ℝ) + 1) * cfg.N k ^ (-(200 * s)))) *
      τ {p | D.forget (cfg.N k ^ (-s)) (D.state (cfg.N k ^ (-(200 * s))) p) = u}) :
    ∀ (i : Fin (cfg.n k s)) (q r : Fin 2 → ℤ) (v : ℤ),
      (D.parentCurrent τ i) {p | cfg.physicalPosition k s i p = q ∧
        (fun e => ⌊D.row p e / cfg.N k ^ (-s)⌋) = r ∧
        ⌊cfg.b k p.1 3 / cfg.N k ^ (-(200 * s))⌋ = v} ≤
      C * cfg.π k (Ico ((v : ℝ) * cfg.N k ^ (-(200 * s)))
        (((v : ℝ) + 1) * cfg.N k ^ (-(200 * s)))) *
      (D.parentCurrent τ i) {p | cfg.physicalPosition k s i p = q ∧
        (fun e => ⌊D.row p e / cfg.N k ^ (-s)⌋) = r} := by
  intro i q r v
  have hb := (h.basic k).1
  have hpos : Measurable (cfg.physicalPosition k s i) := by
    apply Measurable.of_eval
    intro e
    apply Int.measurable_floor.comp
    fin_cases e <;> dsimp [physicalPosition] <;> fun_prop
  have hrow := measurable_floor_vector D.row (D.measurable_row deep) (cfg.N k ^ (-s))
  have hstate : MeasurableSet {p | cfg.physicalPosition k s i p = q ∧
      (fun e => ⌊D.row p e / cfg.N k ^ (-s)⌋) = r} :=
    (hpos (measurableSet_singleton q)).inter (hrow (measurableSet_singleton r))
  have hvel : MeasurableSet {p : α × ℝ | ⌊cfg.b k p.1 3 / cfg.N k ^ (-(200 * s))⌋ = v} :=
    (Int.measurable_floor.comp ((((measurable_pi_apply 3).comp hb).comp measurable_fst).div_const _))
      (measurableSet_singleton v)
  have hjoint : MeasurableSet {p | cfg.physicalPosition k s i p = q ∧
      (fun e => ⌊D.row p e / cfg.N k ^ (-s)⌋) = r ∧
      ⌊cfg.b k p.1 3 / cfg.N k ^ (-(200 * s))⌋ = v} := by
    convert hstate.inter hvel using 1
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, and_assoc]
  have hkey := D.forget_state_iff
  have hs : {p | cfg.physicalPosition k s i p = q ∧
        (fun e => ⌊D.row p e / cfg.N k ^ (-s)⌋) = r} ∩ {p | D.parentTag p = some i} =
      {p | D.forget (cfg.N k ^ (-s)) (D.state (cfg.N k ^ (-(200 * s))) p) =
        (some i, ((q 0, q 1), r))} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, hkey, and_assoc, and_comm, and_left_comm]
  have hsj : {p | cfg.physicalPosition k s i p = q ∧
        (fun e => ⌊D.row p e / cfg.N k ^ (-s)⌋) = r ∧
        ⌊cfg.b k p.1 3 / cfg.N k ^ (-(200 * s))⌋ = v} ∩ {p | D.parentTag p = some i} =
      {p | D.forget (cfg.N k ^ (-s)) (D.state (cfg.N k ^ (-(200 * s))) p) =
        (some i, ((q 0, q 1), r)) ∧ ⌊cfg.b k p.1 3 / cfg.N k ^ (-(200 * s))⌋ = v} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, hkey, and_assoc, and_comm, and_left_comm]
  simp only [parentCurrent, Measure.restrict_apply hjoint, Measure.restrict_apply hstate, hs, hsj]
  exact hcap _ v


/-- Parent restriction partitions the whole retained continuous law. -/
theorem parentCurrent_mass_sum (h : cfg.Valid) (deep : cfg.AssignmentLevel k (3 * s))
    (τ : Measure (α × ℝ)) (hτ : τ ≤ cfg.μ k) :
    ∑ i, (D.parentCurrent τ i) univ = τ univ := by
  have hcovered : ∀ᵐ p ∂τ, ∃ i, D.parentTag p = some i := by
    filter_upwards [(deep.half_covers h).filter_mono (MeasureTheory.ae_mono hτ)] with p hp
    obtain ⟨j, hj⟩ := hp
    have heq : D.tag p = some j := (coverLabel_eq_some _ deep.disjoint_halfEvents p j).mpr hj
    exact ⟨D.parent j, by simp only [parentTag, heq, Option.map_some]⟩
  let C : Fin (cfg.n k s) → Set (α × ℝ) := fun i => {p | D.parentTag p = some i}
  have hC : ∀ i, MeasurableSet (C i) := fun i =>
    (D.measurable_parentTag deep) (measurableSet_singleton (some i))
  have hd : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hne
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact hne (Option.some.inj (hi.symm.trans hj))
  have hfull : τ (⋃ i, C i) = τ univ := by
    apply measure_congr
    filter_upwards [hcovered] with p hp
    apply propext
    simp only [mem_univ, iff_true, mem_iUnion]
    exact hp
  simp only [parentCurrent, Measure.restrict_apply_univ]
  exact ((measure_iUnion hd hC).trans (by rw [tsum_fintype])).symm.trans hfull

/-- Positive mass relative to the total original assignment budget selects
one label with the same original-reference floor. -/
theorem exists_parentCurrent_heavy (h : cfg.Valid) (a : cfg.AssignmentLevel k s)
    (deep : cfg.AssignmentLevel k (3 * s)) (τ : Measure (α × ℝ)) (hτ : τ ≤ cfg.μ k)
    (θ : ℝ) (hθ : 0 ≤ θ) (hmass : ENNReal.ofReal θ < τ univ) :
    ∃ i, ENNReal.ofReal (cfg.parentWeight k s i * θ) ≤ (D.parentCurrent τ i) univ := by
  classical
  have hw : ∀ i, 0 ≤ cfg.parentWeight k s i := by
    intro i
    unfold parentWeight timeLength
    positivity
  have href : ∑ i, ENNReal.ofReal (cfg.parentWeight k s i * θ) ≤ ENNReal.ofReal θ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro i _; exact mul_nonneg (hw i) hθ)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (∑ i, cfg.parentWeight k s i) * θ := by rw [Finset.sum_mul]
      _ ≤ 1 * θ := mul_le_mul_of_nonneg_right (a.parent_weight_budget h) hθ
      _ = θ := one_mul _
  by_contra! hn
  have hs : τ univ ≤ ∑ i, ENNReal.ofReal (cfg.parentWeight k s i * θ) := by
    rw [← D.parentCurrent_mass_sum h deep τ hτ]
    exact Finset.sum_le_sum (fun i _ => (hn i).le)
  exact (not_lt_of_ge (hs.trans href)) hmass

end HistoryData
end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
