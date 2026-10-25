import Submission.Obl.k4_critical_conditional_row_preparation.HistoryCaps

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators

local instance {ι : Type*} : MeasurableSpace (Option ι) := ⊤
local instance {ι : Type*} : DiscreteMeasurableSpace (Option ι) := ⟨fun _ => trivial⟩

namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

structure HistoryData (cfg : Data α) (k : ℕ) (s : ℝ) where
  parent : Fin (cfg.n k (3 * s)) → Fin (cfg.n k s)
  parent_assignment : ∀ j, cfg.A k (3 * s) j ⊆ cfg.A k s (parent j)
  parent_interval : ∀ j, I (cfg.T k (3 * s)) (cfg.j k (3 * s) j) ⊆
    I (cfg.T k s) (cfg.j k s (parent j))
  entry : Fin (cfg.n k (3 * s)) → Fin 4 → ℝ
  entry_bound : ∀ i e, |entry i (Fin.succ e)| ≤ 8 * cfg.K k ^ 4
  entry_fit : ∀ i l, l ∈ cfg.B k (3 * s) i →
    ∀ t ∈ I (cfg.T k (3 * s)) (cfg.j k (3 * s) i),
      |affineResidualIntercept (entry i) (cfg.b k l) +
        t * affineResidualSlope (entry i) (cfg.b k l)| ≤ cfg.K k * cfg.N k ^ (-(3 * s))

namespace HistoryData
variable {k : ℕ} {s : ℝ} (D : cfg.HistoryData k s)

def tag (D : cfg.HistoryData k s) : α × ℝ → Option (Fin (cfg.n k (3 * s))) := coverLabel (cfg.halfEvent k (3 * s))

def rowValue (i : Option (Fin (cfg.n k (3 * s)))) : Fin 2 → ℝ :=
  i.elim 0 (fun h => cfg.frozenRow k (3 * s) h (D.entry h))

def row (p : α × ℝ) : Fin 2 → ℝ := D.rowValue (D.tag p)

def parentTag (p : α × ℝ) : Option (Fin (cfg.n k s)) := (D.tag p).map D.parent

def qcode (ξ : ℝ) (p : α × ℝ) : ℤ × ℤ :=
  (D.tag p).elim (0, 0) (fun i => basePair (cfg.b k) (cfg.leftTime k s (D.parent i))
    (cfg.horizontalOrigin k s (D.parent i)) (cfg.timeLength k s * ξ) p)

def state (ξ : ℝ) (p : α × ℝ) : Option (Fin (cfg.n k (3 * s))) × (ℤ × ℤ) :=
  (D.tag p, D.qcode ξ p)

def forget (a : ℝ) (u : Option (Fin (cfg.n k (3 * s))) × (ℤ × ℤ)) :
    Option (Fin (cfg.n k s)) × ((ℤ × ℤ) × (Fin 2 → ℤ)) :=
  (u.1.map D.parent, (u.2, fun e => ⌊D.rowValue u.1 e / a⌋))

def options (ξ : ℝ) (h : Fin (cfg.n k (3 * s))) : Finset (ℤ × ℤ) :=
  baseOptions (cfg.timeLength k s * ξ) (cfg.leftTime k s (D.parent h))
    (cfg.horizontalOrigin k s (D.parent h)) (cfg.leftTime k (3 * s) h)
    (cfg.horizontalOrigin k (3 * s) h) (2 * cfg.K k * cfg.timeLength k (3 * s))

def capReference (D : cfg.HistoryData k s) (ξ : ℝ) : ℝ := cfg.timeLength k (3 * s) ^ 2 *
  (cfg.N k ^ (-(3 * s))) ^ cfg.d * (cfg.timeLength k s * ξ) ^ 2

theorem measurable_tag (deep : cfg.AssignmentLevel k (3 * s)) : Measurable D.tag :=
  measurable_coverLabel _ deep.measurableSet_halfEvent deep.disjoint_halfEvents

theorem measurable_row (deep : cfg.AssignmentLevel k (3 * s)) : Measurable D.row :=
  (measurable_of_countable D.rowValue).comp (D.measurable_tag deep)

theorem measurable_parentTag (deep : cfg.AssignmentLevel k (3 * s)) : Measurable D.parentTag :=
  (measurable_of_countable (Option.map D.parent)).comp (D.measurable_tag deep)

theorem measurable_qcode (h : cfg.Valid) (deep : cfg.AssignmentLevel k (3 * s)) (ξ : ℝ) :
    Measurable (D.qcode ξ) := by
  unfold qcode
  refine measurable_select D.tag (D.measurable_tag deep)
    (fun i p => i.elim (0, 0) (fun j => basePair (cfg.b k)
      (cfg.leftTime k s (D.parent j)) (cfg.horizontalOrigin k s (D.parent j))
      (cfg.timeLength k s * ξ) p)) ?_
  intro i
  cases i with
  | none => exact measurable_const
  | some i => exact measurable_basePair _ (h.basic k).1 _ _ _

theorem measurable_state (h : cfg.Valid) (deep : cfg.AssignmentLevel k (3 * s)) (ξ : ℝ) :
    Measurable (D.state ξ) := (D.measurable_tag deep).prodMk (D.measurable_qcode h deep ξ)

theorem parentTag_some (p : α × ℝ) (i : Fin (cfg.n k s)) :
    D.parentTag p = some i ↔ ∃ j, D.tag p = some j ∧ D.parent j = i := by
  cases ht : D.tag p <;> simp [parentTag, ht]

theorem qcode_of_parentTag (ξ : ℝ) (p : α × ℝ) (i : Fin (cfg.n k s))
    (hi : D.parentTag p = some i) :
    D.qcode ξ p = basePair (cfg.b k) (cfg.leftTime k s i)
      (cfg.horizontalOrigin k s i) (cfg.timeLength k s * ξ) p := by
  obtain ⟨j, hj, hp⟩ := (D.parentTag_some p i).mp hi
  simp only [qcode, hj, Option.elim_some, hp]

theorem options_mem (h : cfg.Valid) (deep : cfg.AssignmentLevel k (3 * s))
    (ξ : ℝ) (hξ : 0 < ξ) (p : α × ℝ) (i : Fin (cfg.n k (3 * s)))
    (hi : D.tag p = some i) : D.qcode ξ p ∈ D.options ξ i := by
  have hp := (coverLabel_eq_some _ deep.disjoint_halfEvents p i).mp hi
  have hc := cfg.halfEvent_subset k (3 * s) i hp
  have hd := deep.horizontal_displacement i p.1 (deep.fitted_subset i hp.1) p.2 hc.2
  have hH : 0 < cfg.timeLength k (3 * s) := by unfold timeLength; positivity
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  simp only [qcode, hi, Option.elim_some]
  apply mem_baseOptions _ _ _ _ _ _ _ _ (by unfold timeLength; positivity)
  · exact hd.1.trans (by nlinarith only [hH, mul_le_mul_of_nonneg_right hK hH.le])
  · exact hd.2

theorem reference_budget (h : cfg.Valid) (deep : cfg.AssignmentLevel k (3 * s))
    (ξ : ℝ) (hξ : 0 < ξ) (hw : cfg.timeLength k s * ξ ≤ cfg.timeLength k (3 * s)) :
    ∑' u, historyReference (D.options ξ) (fun _ => ENNReal.ofReal (D.capReference ξ)) u ≤
      ENNReal.ofReal (36 * cfg.K k ^ 4) := by
  classical
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hHd : 0 < cfg.timeLength k (3 * s) := by unfold timeLength; positivity
  have hτ : 0 ≤ D.capReference ξ := by dsimp [capReference]; positivity
  have hentry (i : Fin (cfg.n k (3 * s))) :
      ((D.options ξ i).card : ℝ) * D.capReference ξ ≤
        36 * cfg.K k ^ 4 * cfg.parentWeight k (3 * s) i := by
    have hc := baseOptions_reference_bound (cfg.timeLength k s * ξ)
      (cfg.leftTime k s (D.parent i)) (cfg.horizontalOrigin k s (D.parent i))
      (cfg.leftTime k (3 * s) i) (cfg.horizontalOrigin k (3 * s) i)
      (cfg.timeLength k (3 * s)) (cfg.K k) ((cfg.N k ^ (-(3 * s))) ^ cfg.d)
      (by unfold timeLength; positivity) hHd (h.subpower.1 k) (by positivity) hw
    have hf := (deep.original_reference_floor h i).2
    have hp : cfg.timeLength k (3 * s) ^ 4 * (cfg.N k ^ (-(3 * s))) ^ cfg.d ≤
        cfg.parentWeight k (3 * s) i * cfg.K k ^ 2 := by
      exact (div_le_iff₀ (sq_pos_of_pos hK)).mp hf
    calc
      _ ≤ 36 * cfg.K k ^ 2 * cfg.timeLength k (3 * s) ^ 4 *
          (cfg.N k ^ (-(3 * s))) ^ cfg.d := hc
      _ ≤ 36 * cfg.K k ^ 2 * (cfg.parentWeight k (3 * s) i * cfg.K k ^ 2) := by
        nlinarith only [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 36 * cfg.K k ^ 2)]
      _ = _ := by ring
  have hsum : ∑ i, ((D.options ξ i).card : ℝ) * D.capReference ξ ≤ 36 * cfg.K k ^ 4 := by
    calc
      _ ≤ ∑ i, 36 * cfg.K k ^ 4 * cfg.parentWeight k (3 * s) i :=
        Finset.sum_le_sum (fun i _ => hentry i)
      _ = (36 * cfg.K k ^ 4) * ∑ i, cfg.parentWeight k (3 * s) i := by rw [Finset.mul_sum]
      _ ≤ _ := (mul_le_mul_of_nonneg_left (deep.parent_weight_budget h) (by positivity)).trans_eq (mul_one _)
  rw [tsum_historyReference]
  calc
    _ = ENNReal.ofReal (∑ i, ((D.options ξ i).card : ℝ) * D.capReference ξ) := by
      rw [ENNReal.ofReal_sum_of_nonneg (by intro i _; positivity)]
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsum

end HistoryData
end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
