import Submission.Obl.k4_critical_conditional_row_preparation.NormalizedTransport
import Submission.Obl.k4_critical_conditional_row_preparation.PaletteCaps
import Submission.Obl.k4_critical_conditional_row_preparation.Numerics

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

namespace PhysicalPreparation
variable {k : ℕ} {s η : ℝ} {source : Measure (α × ℝ)}
    (p : cfg.PhysicalPreparation k s η source)

/-- Every input of the exact frozen continuous row law is supplied by the
same original prior, original palette, and physical prepared current. -/
theorem to_conditionalAt (h : cfg.Valid) (a : cfg.AssignmentLevel k s)
    (hs : 0 ≤ s) (hη : 0 < η) (hcost : 2 * cfg.K k ≤ cfg.N k ^ η)
    (hpalette : ∀ x r : ℝ, cfg.N k ^ (-(200 * s)) ≤ r → r ≤ 1 →
      cfg.π k (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (cfg.N k ^ η * r ^ cfg.S))
    (hjoint : ∀ (q : Fin 2 → ℤ) (v : ℤ),
      (cfg.normalizedCurrent k s p.index p.current) {y |
        rowPositionCode (cfg.N k ^ (-(200 * s))) (cfg.clippedIntercept k s p.index)
          (cfg.clippedVelocity k s p.index) y = q ∧
        ⌊cfg.clippedVelocity k s p.index y.1 / cfg.N k ^ (-(200 * s))⌋ = v} ≤
      ENNReal.ofReal (cfg.N k ^ η * (cfg.N k ^ (-(200 * s))) ^ 2) *
        cfg.π k (Ico ((v : ℝ) * cfg.N k ^ (-(200 * s)))
          (((v : ℝ) + 1) * cfg.N k ^ (-(200 * s)))))
    (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ)
    (hcard : ∀ q v, ((lists q v).card : ℝ) ≤ cfg.N k ^ η)
    (hlists : ∀ᵐ y ∂source, y.1 ∈ cfg.B k s p.index →
      y.2 ∈ I (cfg.T k s) (cfg.j k s p.index) →
      ⌊cfg.b k y.1 5 / cfg.N k ^ (-s)⌋ ∈ lists (cfg.physicalPosition k s p.index y)
        ⌊cfg.b k y.1 3 / cfg.N k ^ (-(200 * s))⌋) :
    cfg.ConditionalAt k s η := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  have hH : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hW := (a.original_reference_floor h p.index).1
  have hc := a.clipped_measurable h p.index
  unfold ConditionalAt
  refine ⟨p.index, p.current, cfg.leftTime k s p.index, cfg.horizontalOrigin k s p.index,
    cfg.clippedIntercept k s p.index, cfg.clippedVelocity k s p.index,
    (fun l => cfg.b k l 5), cfg.normalizedRow k s p.index p.row, lists, ?_⟩
  change RowLaw cfg.S (200 * s) η (cfg.N k) α (cfg.truePrior k s p.index)
    (cfg.normalizedCurrent k s p.index p.current) (cfg.clippedIntercept k s p.index)
    (cfg.clippedVelocity k s p.index) (fun l => cfg.b k l 5)
    (cfg.normalizedRow k s p.index p.row) (cfg.π k) (cfg.N k ^ (-s)) lists ∧ _
  constructor
  · dsimp only [RowLaw]
    refine ⟨hc.1, hc.2, (measurable_pi_apply 5).comp (h.basic k).1,
      cfg.measurable_normalizedRow k s p.index p.row p.measurable_row,
      a.prior_probability h p.index, (h.basic k).2.2.1, ?_, ?_, ?_, ?_, ?_, ?_,
      hpalette, hjoint, p.normalized_row_constraint h a, hcard,
      p.normalized_lists h a lists hlists, p.normalized_conditional_cap h a⟩
    · exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    · exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    · intro l
      exact (a.clipped_bound h p.index l).trans hcost
    · calc
        _ ≤ ENNReal.ofReal (cfg.K k) • ((cfg.truePrior k s p.index).prod volume) :=
          a.normalized_original_domination h p.index p.current p.current_le_parent
        _ ≤ _ := by
          intro C
          simp only [Measure.smul_apply, smul_eq_mul]
          exact mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (by linarith only [hcost, hK])) (zero_le : (0 : ℝ≥0∞) ≤ ((cfg.truePrior k s p.index).prod volume) C)
    · exact cfg.normalized_block_support k s p.index p.current p.current_le_parent
    · exact original_normalized_mass_lower p.current (cfg.leftTime k s p.index)
        (cfg.timeLength k s) (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s p.index))
        (cfg.N k ^ (-η)) hW p.mass_lower
  · refine ⟨(cfg.leftTime_abs_le_one k s p.index).trans (by linarith [h.subpower.1 k]),
      (a.horizontalOrigin_bound h p.index).trans (by linarith only [hK]),
      hW, p.current_le_parent, ?_, a.retained_native_bounds h p.index p.current p.current_le_parent, ?_⟩
    · filter_upwards [a.clipped_coordinates_ae h p.index p.current p.current_le_parent] with y hy
      exact ⟨hy.1, hy.2, rfl⟩
    · have hlen := (a.length_bounds h).2
      exact hlen.trans (by gcongr; linarith only [hK])

end PhysicalPreparation
end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
