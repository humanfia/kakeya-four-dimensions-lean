import Submission.Obl.k4_horizontal_wide_interval_return.CellCaps
import Submission.Obl.k4_critical_switching_state_preparation.ShiftedPalette

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set
open Submission.Lib.K4MovingMeshBoxes
open scoped ENNReal

namespace CellFrame

variable {F : CellFrame}

/-- The scalar velocity is the original velocity translated by `c₁`.
Two original bins suffice, so the original palette cap is preserved with
only a constant loss. Native affine coefficients still affect only the mesh. -/
theorem cell_residual_angular_cap {α : Type*} [MeasurableSpace α]
    (lam : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    {H Lbound σ ρ δ C d τ P : ℝ} (weight : ℤ → ℝ≥0∞)
    (hH : 1 ≤ H) (hLbound : 0 ≤ Lbound)
    (hq : 0 < F.q) (hg : 0 < F.g) (hg1 : F.g ≤ 1) (ha : 0 < F.a)
    (hσ : 0 < σ) (hσg : σ ≤ F.g) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hmesh₀ : 4 * H ^ 2 * δ ≤ F.q * σ)
    (hmesh₁ : 4 * H ^ 2 * δ ≤ F.q * F.g)
    (hmeshOffset : (3 * Lbound * (F.q * F.g) + 40 * F.a * H ^ 3) * δ ≤
      F.a * ρ * (F.q * F.g))
    (hc : ∀ i, |F.c i| ≤ H) (hC : ∀ i, |F.C i| ≤ H)
    (hL : ∀ i, |F.L i| ≤ Lbound) (hcapC : 0 ≤ C) (hP : 0 ≤ P)
    (E : Set (α × ℝ))
    (hE : ∀ p ∈ E, p.2 ∈ Icc F.t₀ (F.t₀ + F.q) ∧
      |F.zZ p.2 (lineZ (b p.1) p.2)| ≤ H ∧
      |F.U p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2)| ≤ H)
    (q₀ : Fin 2 → ℤ) (j k : ℤ)
    (hpalette : ∀ ℓ, weight ℓ ≤ ENNReal.ofReal P)
    (hcap : ∀ c j' ℓ, lam {p | baseMesh δ
        (![p.2, lineZ (b p.1) p.2, lineY (b p.1) p.2] : Fin 3 → ℝ) = c ∧
        ⌊lineX (b p.1) p.2 / (F.a * ρ)⌋ = j' ∧ ⌊b p.1 3 / τ⌋ = ℓ} ≤
      ENNReal.ofReal (C * δ ^ 3 * (F.a * ρ) ^ d) * weight ℓ) :
    lam (E ∩ {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
      ⌊F.cellSig (b p.1) p.2 / ρ⌋ = j ∧ ⌊F.y₁ (b p.1) / τ⌋ = k}) ≤
      ENNReal.ofReal (6000 * C * H * P * F.q ^ 3 * F.g * σ ^ 2 * (F.a * ρ) ^ d) := by
  classical
  let V (ℓ : ℤ) : Set (α × ℝ) := {p | ⌊b p.1 3 / τ⌋ = ℓ}
  have hV : ∀ ℓ, MeasurableSet (V ℓ) := by
    intro ℓ
    exact ((((measurable_pi_apply 3).comp (hb.comp measurable_fst)).div_const τ).floor)
      (measurableSet_singleton ℓ)
  let A : Set (α × ℝ) := E ∩ {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
    ⌊F.cellSig (b p.1) p.2 / ρ⌋ = j}
  let cap : ℝ := 3000 * C * H * F.q ^ 3 * F.g * σ ^ 2 * (F.a * ρ) ^ d
  have hcap0 : 0 ≤ cap := by dsimp [cap]; positivity
  have hbin (ℓ : ℤ) : lam (A ∩ V ℓ) ≤ ENNReal.ofReal cap * weight ℓ := by
    have hnative : ∀ c j', (lam.restrict (V ℓ))
        {p | baseMesh δ (![p.2, lineZ (b p.1) p.2, lineY (b p.1) p.2] : Fin 3 → ℝ) = c ∧
          ⌊lineX (b p.1) p.2 / (F.a * ρ)⌋ = j'} ≤
        ENNReal.ofReal (C * δ ^ 3 * (F.a * ρ) ^ d) * weight ℓ := by
      intro c j'
      rw [Measure.restrict_apply' (hV ℓ)]
      convert hcap c j' ℓ using 1
      congr 1
      ext p
      simp only [V, mem_inter_iff, mem_ofPred_eq]
      tauto
    have hbound := cell_residual_cap (lam.restrict (V ℓ)) b (weight ℓ) hH hLbound
      hq hg hg1 ha hσ hσg hρ hδ hmesh₀ hmesh₁ hmeshOffset hc hC hL hcapC E hE q₀ j hnative
    rw [Measure.restrict_apply' (hV ℓ)] at hbound
    exact hbound
  let ℓ₀ : ℤ := k + ⌊F.c 1 / τ⌋
  have hcover : E ∩ {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
      ⌊F.cellSig (b p.1) p.2 / ρ⌋ = j ∧ ⌊F.y₁ (b p.1) / τ⌋ = k} ⊆
      (A ∩ V ℓ₀) ∪ (A ∩ V (ℓ₀ + 1)) := by
    rintro p ⟨hpE, hpcode, hpbin, hpvel⟩
    have hraw := Submission.Obl.k4_critical_switching_state_preparation.raw_floor_of_shifted
      (show ⌊(b p.1 3 - F.c 1) / τ⌋ = k from hpvel)
    rcases hraw with hraw | hraw
    · exact Or.inl ⟨⟨hpE, hpcode, hpbin⟩, hraw⟩
    · exact Or.inr ⟨⟨hpE, hpcode, hpbin⟩, hraw⟩
  calc lam (E ∩ _)
      ≤ lam (A ∩ V ℓ₀) + lam (A ∩ V (ℓ₀ + 1)) :=
        (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal cap * weight ℓ₀ + ENNReal.ofReal cap * weight (ℓ₀ + 1) :=
        add_le_add (hbin ℓ₀) (hbin (ℓ₀ + 1))
    _ ≤ ENNReal.ofReal cap * ENNReal.ofReal P + ENNReal.ofReal cap * ENNReal.ofReal P := by
        gcongr <;> exact hpalette _
    _ = (2 : ℝ≥0∞) * ENNReal.ofReal cap * ENNReal.ofReal P := by ring
    _ = ENNReal.ofReal ((2 : ℝ) * cap * P) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hcap0),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
    _ = _ := by congr 1; dsimp [cap]; ring

end CellFrame

end Submission.Obl.k4_horizontal_wide_interval_return
