import Submission.Obl.k4_critical_conditional_row_preparation.Histories

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set
open scoped ENNReal
local instance {ι : Type*} : MeasurableSpace (Option ι) := ⊤
local instance {ι : Type*} : DiscreteMeasurableSpace (Option ι) := ⟨fun _ => trivial⟩
namespace Data
namespace HistoryData
variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s : ℝ}
    (D : cfg.HistoryData k s)

/-- The primitive original caps give the precise atomic history numerator
needed for reference pruning, with the unchanged real velocity palette. -/
theorem original_history_bin_cap (h : cfg.Valid) (deep : cfg.AssignmentLevel k (3 * s))
    (σ : Measure (α × ℝ)) (hσ : σ ≤ cfg.μ k) (ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 < δ)
    (hcell : δ ≤ cfg.timeLength k s * ξ)
    (htrans : δ ≤ cfg.K k * cfg.timeLength k (3 * s) * cfg.N k ^ (-cfg.ℓ * (3 * s)))
    (hmesh : 3 * δ ≤ cfg.N k ^ (-(3 * s)))
    (hcap : cfg.NativeFineJointCap k (3 * s) δ ξ) :
    ∀ (u : Option (Fin (cfg.n k (3 * s))) × (ℤ × ℤ)) (v : ℤ),
      σ {p | D.state ξ p = u ∧ ⌊cfg.b k p.1 3 / ξ⌋ = v} ≤
        ENNReal.ofReal (27648 * cfg.K k ^ 11) *
          historyReference (D.options ξ) (fun _ => ENNReal.ofReal (D.capReference ξ)) u *
          ((cfg.π k).map (fun w : ℝ => ⌊w / ξ⌋)) {v} := by
  classical
  rintro ⟨tag, q⟩ v
  have hK0 : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  have hbin : ((cfg.π k).map (fun w : ℝ => ⌊w / ξ⌋)) {v} =
      cfg.π k {w | ⌊w / ξ⌋ = v} := by
    have hf : Measurable (fun w : ℝ => ⌊w / ξ⌋) :=
      Int.measurable_floor.comp (measurable_id.div_const ξ)
    rw [Measure.map_apply hf (measurableSet_singleton v)]
    congr 1 <;> ext w <;> simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  cases tag with
  | none =>
      have hcover : ∀ᵐ p ∂σ, D.tag p ≠ none := by
        filter_upwards [(deep.half_covers h).filter_mono (MeasureTheory.ae_mono hσ)] with p hp
        exact fun hn => (coverLabel_eq_none _ p).mp hn hp
      have hz : σ {p | D.tag p = none} = 0 := by
        simpa only [not_not] using ae_iff.mp hcover
      calc
        _ ≤ σ {p | D.tag p = none} := measure_mono (fun p hp => by
          change D.tag p = none
          exact congrArg Prod.fst hp.1)
        _ = 0 := hz
        _ ≤ _ := zero_le
  | some i =>
      have htag (p : α × ℝ) (hp : D.state ξ p = (some i, q)) : D.tag p = some i :=
        congrArg Prod.fst hp
      by_cases hq : q ∈ D.options ξ i
      swap
      · have hempty : {p | D.state ξ p = (some i, q) ∧ ⌊cfg.b k p.1 3 / ξ⌋ = v} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro p hp
          have hmem := D.options_mem h deep ξ hξ p i (htag p hp.1)
          have heq : D.qcode ξ p = q := congrArg Prod.snd hp.1
          exact hq (heq ▸ hmem)
        rw [hempty, measure_empty]
        exact zero_le
      rw [historyReference, Option.elim_some, ite_eq_left hq, hbin]
      have hfit : ∀ l ∈ cfg.B k (3 * s) i, ∀ t ∈ I (cfg.T k (3 * s)) (cfg.j k (3 * s) i),
          |cfg.b k l 2 + t * cfg.b k l 5 - affineBaseValue (D.entry i)
            ![t, cfg.b k l 0 + t * cfg.b k l 3, cfg.b k l 1 + t * cfg.b k l 4]| ≤
            cfg.K k * cfg.N k ^ (-(3 * s)) := by
        intro l hl t ht
        convert D.entry_fit i l hl t ht using 1
        congr 1
        simp [affineBaseValue, affineResidualIntercept, affineResidualSlope, Fin.sum_univ_succ]
        ring
      have hc := deep.physical_rectangle_joint_cap h i (D.entry i) (D.entry_bound i) hfit
        δ ξ (cfg.timeLength k s * ξ) (cfg.leftTime k s (D.parent i))
        (cfg.horizontalOrigin k s (D.parent i)) hδ hξ hcell htrans hmesh hcap ![q.1, q.2] v
      calc
        _ ≤ cfg.μ k {p | p.1 ∈ cfg.B k (3 * s) i ∧ p.2 ∈ I (cfg.T k (3 * s)) (cfg.j k (3 * s) i) ∧
            ⌊(p.2 - cfg.leftTime k s (D.parent i)) / (cfg.timeLength k s * ξ)⌋ = q.1 ∧
            ⌊(cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - cfg.horizontalOrigin k s (D.parent i)) /
              (cfg.timeLength k s * ξ)⌋ = q.2 ∧ ⌊cfg.b k p.1 3 / ξ⌋ = v} := by
          apply (hσ _).trans
          apply measure_mono
          intro p hp
          have hi := htag p hp.1
          have hm := cfg.halfEvent_subset k (3 * s) i
            ((coverLabel_eq_some _ deep.disjoint_halfEvents p i).mp hi)
          have hb : basePair (cfg.b k) (cfg.leftTime k s (D.parent i))
              (cfg.horizontalOrigin k s (D.parent i)) (cfg.timeLength k s * ξ) p = q := by
            simpa only [state, qcode, hi, Option.elim_some] using congrArg Prod.snd hp.1
          exact ⟨hm.1, hm.2, congrArg Prod.fst hb, congrArg Prod.snd hb, hp.2⟩
        _ ≤ ENNReal.ofReal (27648 * cfg.K k ^ 11 * cfg.timeLength k (3 * s) ^ 2 *
            (cfg.N k ^ (-(3 * s))) ^ cfg.d * (cfg.timeLength k s * ξ) ^ 2) *
            cfg.π k {w | ⌊w / ξ⌋ = v} := hc
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 27648 * cfg.K k ^ 11)]
          congr 2
          dsimp [capReference]
          ring

end HistoryData
end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
