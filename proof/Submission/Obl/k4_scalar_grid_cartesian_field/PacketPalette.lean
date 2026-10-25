import Submission.Obl.k4_scalar_grid_cartesian_field.HeavyCells

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- A finite physical-cell count restores every original-prior bin cap after an arbitrary
Cartesian restriction, while keeping a fixed fraction of its full-prior mass floor. -/
theorem packet_palette_pruning {Ω Q I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (F : Finset Q) (hF : ∀ᵐ p ∂μ, code p ∈ F)
    (P : ENNReal) (hP : P ≠ ⊤)
    {a J C cell : ℝ} (ha : 0 < a) (hJ : 0 < J) (hC : 0 ≤ C) (hcell : 0 < cell)
    (hmass : ENNReal.ofReal a * P ≤ μ univ)
    (hcount : ENNReal.ofReal cell * F.card ≤ ENNReal.ofReal J * P)
    (event : I → Set Ω) (prior : I → ENNReal)
    (hcap : ∀ q i, μ (code ⁻¹' {q} ∩ event i) ≤ ENNReal.ofReal (C * cell) * prior i) :
    ∃ Keep : Set Ω, MeasurableSet Keep ∧
      ENNReal.ofReal (a / 2) * P ≤ (μ.restrict Keep) univ ∧
      ∀ q i, (μ.restrict Keep) (code ⁻¹' {q} ∩ event i) ≤
        ENNReal.ofReal (4 * C * J / a) * (μ.restrict Keep) (code ⁻¹' {q}) * prior i := by
  let θ : ENNReal := ENNReal.ofReal (cell * a / (4 * J))
  let floor : ENNReal := ENNReal.ofReal (a / 2) * P
  have hθreal : 0 < cell * a / (4 * J) := by positivity
  have hθ : θ ≠ 0 := (ENNReal.ofReal_pos.mpr hθreal).ne'
  have hθtop : θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfloor : floor + floor ≤ μ univ := by
    calc
      _ = (ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2)) * P := (add_mul _ _ _).symm
      _ = ENNReal.ofReal a * P := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ a / 2) (by positivity : 0 ≤ a / 2)]
        congr 2
        ring
      _ ≤ _ := hmass
  have hcost : θ * F.card ≤ floor := by
    calc
      _ = ENNReal.ofReal (a / (4 * J)) * (ENNReal.ofReal cell * F.card) := by
        dsimp [θ]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ a / (4 * J))]
        congr 2
        ring
      _ ≤ ENNReal.ofReal (a / (4 * J)) * (ENNReal.ofReal J * P) := mul_le_mul' le_rfl hcount
      _ = ENNReal.ofReal (a / 4) * P := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ a / (4 * J))]
        congr 2
        field_simp
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : a / 4 ≤ a / 2)) le_rfl
  obtain ⟨Keep, hKeep, hkept, hpalette⟩ := finite_cell_pruning_with_mass_floor μ code hcode F hF
    hθ hθtop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP) hfloor hcost event prior
    (ENNReal.ofReal (C * cell)) hcap
  have hratio : ENNReal.ofReal (C * cell) / θ = ENNReal.ofReal (4 * C * J / a) := by
    dsimp [θ]
    rw [← ENNReal.ofReal_div_of_pos hθreal]
    congr 1
    field_simp
  exact ⟨Keep, hKeep, hkept, by simpa only [hratio] using hpalette⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
