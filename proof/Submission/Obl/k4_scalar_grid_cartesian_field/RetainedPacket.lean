import Submission.Obl.k4_scalar_grid_cartesian_field.ReadyPacket
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketPalette
import Submission.Obl.k4_scalar_grid_cartesian_field.DataFacts

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set

/-- The field and original-prior palette after the final whole-cell restriction. -/
structure RetainedPacket {data : Data} {k M : ℕ} {Λ B R : ℝ}
    (p : ReadyPacket data k M Λ B R) (C : ℝ) (q : ℕ) where
  μ : Measure Incidence
  𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ
  dominated : μ ≤ p.core.ρ.restrict p.core.S₀
  mass_floor : ENNReal.ofReal (1 / (2 * C * Λ ^ (q + 1))) *
    (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 p.i) (data.A k 1 p.i)) ≤ μ univ
  degree : ∀ e, (𝒯 e).totalDegree ≤ 2 * M
  coefficients : ∀ e b, |(𝒯 e).coeff b| ≤ C * Λ ^ q
  comparison : ∀ᵐ x ∂μ, ∀ t ∈ Icc p.core.a (p.core.a + p.core.h),
    |coreResidual 𝒯 p.core.h ![p.core.a, p.core.y₀] x.1 t| ≤ C * Λ ^ q * p.core.εT
  palette : ∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ (q₀ : Fin 3 → ℤ) (c : ℤ),
    μ {x | physCube (data.N k) B x = q₀ ∧ x.1.2 1 ∈ vel data k r c} ≤
      ENNReal.ofReal (4 * C * Λ ^ (q + 3)) * μ {x | physCube (data.N k) B x = q₀} *
        data.π k (data.γ k 1 p.i) (vel data k r c)

/-- Restore the ORIGINAL palette after Cartesian interpolation using the unchanged fine-cell budget. -/
theorem ReadyPacket.retain {data : Data} {k M : ℕ} {Λ B R C : ℝ} {q : ℕ}
    (p : ReadyPacket data k M Λ B R) (hC : 0 < C) (hout : p.core.Output C q) :
    Nonempty (RetainedPacket p C q) := by
  classical
  have hΛ : 1 ≤ Λ := by simpa only [p.original_Λ] using p.core.hΛ
  have hΛpos : 0 < Λ := by linarith
  have hN : 0 < data.N k := by have := p.core.hN; rw [p.original_N] at this; linarith
  let P : ENNReal := ENNReal.ofReal (packetLength data k) *
    data.ν k (data.γ k 1 p.i) (data.A k 1 p.i)
  letI := p.original.probability_ν
  have hPtop : P ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  obtain ⟨𝒯, S₁, hS₁, hsub, hdegree, hcoeff, hmass, hcomp⟩ := hout
  let μ₁ := p.core.ρ.restrict S₁
  have hμ₁ : μ₁ ≤ p.core.ρ.restrict p.core.S₀ := Measure.restrict_mono_set _ hsub
  have hbasefloor : ENNReal.ofReal (1 / Λ) * P ≤ p.core.ρ p.core.S₀ := by
    apply mass_floor_of_original_budget hΛpos
    simpa only [P, p.original_h, p.original_prior, p.original_Λ] using p.core.original_mass
  have hμfloor : ENNReal.ofReal (1 / (C * Λ ^ (q + 1))) * P ≤ μ₁ univ := by
    calc
      _ = ENNReal.ofReal (1 / (C * Λ ^ q)) * (ENNReal.ofReal (1 / Λ) * P) := by
        have heq : ENNReal.ofReal (1 / (C * Λ ^ (q + 1))) =
            ENNReal.ofReal (1 / (C * Λ ^ q)) * ENNReal.ofReal (1 / Λ) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (C * Λ ^ q))]
          congr 1
          rw [pow_succ]
          field_simp
        rw [heq, mul_assoc]
      _ ≤ ENNReal.ofReal (1 / (C * Λ ^ q)) * p.core.ρ p.core.S₀ := mul_le_mul' le_rfl hbasefloor
      _ ≤ _ := by simpa only [μ₁, Measure.restrict_apply_univ, p.original_Λ] using hmass
  have hcover : ∀ᵐ x ∂μ₁, physCube (data.N k) B x ∈ p.fine_cells :=
    p.fine_cover.filter_mono (ae_mono hμ₁)
  let Index := {r : ℝ // R⁻¹ ≤ r ∧ r ≤ R} × ℤ
  let event : Index → Set Incidence := fun v => {x | x.1.2 1 ∈ vel data k v.1.val v.2}
  let prior : Index → ENNReal := fun v => data.π k (data.γ k 1 p.i) (vel data k v.1.val v.2)
  have hcap (q₀ : Fin 3 → ℤ) (v : Index) :
      μ₁ ((physCube (data.N k) B) ⁻¹' {q₀} ∩ event v) ≤
        ENNReal.ofReal (Λ * (data.N k ^ (-B)) ^ (2 + data.d)) * prior v := by
    exact (hμ₁ _).trans (p.original_joint_cap v.1.val v.1.property.1 v.1.property.2 q₀ v.2)
  obtain ⟨Keep, hKeep, hkept, hpalette⟩ := packet_palette_pruning μ₁
    (physCube (data.N k) B) (measurable_physCube _ _) p.fine_cells hcover P hPtop
    (by positivity : 0 < 1 / (C * Λ ^ (q + 1))) hΛpos hΛpos.le
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _) hμfloor p.fine_budget event prior hcap
  let μ := μ₁.restrict Keep
  have hμ : μ ≤ μ₁ := Measure.restrict_le_self
  refine ⟨⟨μ, 𝒯, hμ.trans hμ₁, ?_, hdegree, ?_, ?_, ?_⟩⟩
  · have hid : (1 / (C * Λ ^ (q + 1))) / 2 = 1 / (2 * C * Λ ^ (q + 1)) := by ring
    simpa only [hid] using hkept
  · simpa only [p.original_Λ] using hcoeff
  · have hmem : ∀ᵐ x ∂μ, x ∈ S₁ := by
      apply (ae_restrict_mem hS₁).filter_mono (ae_mono hμ)
    filter_upwards [hmem] with x hx
    simpa only [p.original_Λ] using hcomp x hx
  · intro r hr₀ hr₁ q₀ c
    have h := hpalette q₀ ((⟨r, hr₀, hr₁⟩, c) : Index)
    have hid : 4 * Λ * Λ / (1 / (C * Λ ^ (q + 1))) = 4 * C * Λ ^ (q + 3) := by
      rw [show q + 3 = (q + 1) + 2 by omega, pow_add]
      field_simp
      <;> ring
    simpa only [hid, μ, event, prior, Set.preimage, Set.mem_singleton_iff, Set.setOf_and] using h

end Submission.Obl.k4_scalar_grid_cartesian_field
