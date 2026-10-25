import Submission.Obl.k4_critical_conditional_row_preparation.NativeNormalization

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set
namespace Data
variable {α : Type} [MeasurableSpace α]

def physicalPosition (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (p : α × ℝ) (e : Fin 2) : ℤ :=
  ⌊(![(p.2 - cfg.leftTime k s i) / cfg.timeLength k s,
    (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - cfg.horizontalOrigin k s i) /
      cfg.timeLength k s] : Fin 2 → ℝ) e / cfg.N k ^ (-(200 * s))⌋

/-- A prepared physical submeasure in one original true label. The row is
still a function of physical continuous time, and the original palette is kept. -/
structure PhysicalPreparation (cfg : Data α) (k : ℕ) (s η : ℝ)
    (source : Measure (α × ℝ)) where
  index : Fin (cfg.n k s)
  current : Measure (α × ℝ)
  row : α × ℝ → Fin 2 → ℝ
  measurable_row : Measurable row
  current_le_source : current ≤ source
  current_le_parent : current ≤ (cfg.ρ k).restrict
    (cfg.B k s index ×ˢ I (cfg.T k s) (cfg.j k s index))
  mass_lower : ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s index) *
    cfg.N k ^ (-η)) ≤ current univ
  row_constraint : ∀ᵐ p ∂current,
    (∀ e, |row p e| ≤ cfg.N k ^ η) ∧
    |row p 0 + cfg.b k p.1 3 * row p 1 - cfg.b k p.1 5| ≤ cfg.N k ^ η * cfg.N k ^ (-s)
  conditional_cap : ∀ (q r : Fin 2 → ℤ) (v : ℤ),
    current {p | cfg.physicalPosition k s index p = q ∧
      (fun e => ⌊row p e / cfg.N k ^ (-s)⌋) = r ∧
      ⌊cfg.b k p.1 3 / cfg.N k ^ (-(200 * s))⌋ = v} ≤
      ENNReal.ofReal (cfg.N k ^ η) *
        cfg.π k (Ico ((v : ℝ) * cfg.N k ^ (-(200 * s)))
          (((v : ℝ) + 1) * cfg.N k ^ (-(200 * s)))) *
        current {p | cfg.physicalPosition k s index p = q ∧
          (fun e => ⌊row p e / cfg.N k ^ (-s)⌋) = r}

end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
