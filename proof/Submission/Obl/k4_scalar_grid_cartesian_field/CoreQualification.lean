import Submission.Obl.k4_scalar_grid_cartesian_field.OriginalPacketFacts

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval)

/-- The exact frozen fit supplies the Cartesian core's qualified row after enlarging only its loss. -/
theorem core_qualification_of_fit (data : Data) (k M : ℕ)
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (data.W k) → Set Incidence) (B ε : ℝ)
    (x : Incidence) (i : Fin (data.n k 1)) {Λ : ℝ} (hN : 0 < data.N k)
    (hΛ : 0 < Λ) (hcoeff : data.N k ^ ε ≤ Λ) (hfit : fit data k M G E B ε x i) :
    ∃ P : Fin 2 → Polynomial ℝ,
      (∀ e, (P e).natDegree ≤ M ∧ ∀ a, |(P e).coeff a| ≤ Λ) ∧
      (∀ e, |G k (data.γ k 1 i) (physCube (data.N k) B x) e - (P e).eval x.2| ≤
        packetLength data k ^ M) ∧
      ENNReal.ofReal (packetLength data k / Λ) ≤ volume {t : ℝ |
        (x.1,t) ∈ E k (data.γ k 1 i) ∧
        t ∈ Icc (blockLeft (data.T k 1) (data.j k 1 i))
          (blockLeft (data.T k 1) (data.j k 1 i) + packetLength data k) ∧
        ∀ e, |G k (data.γ k 1 i) (physCube (data.N k) B (x.1,t)) e - (P e).eval t| ≤
          packetLength data k ^ M} := by
  obtain ⟨P, hP, happrox, hrow⟩ := hfit
  refine ⟨P, (fun e => ⟨(hP e).1, fun a => ((hP e).2 a).trans hcoeff⟩), ?_, ?_⟩
  · simpa only [phys_eq_physCube, packetLength, blockLength] using happrox
  · have hscale : packetLength data k / Λ ≤ packetLength data k * data.N k ^ (-ε) := by
      rw [Real.rpow_neg hN.le, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (blockLength_pos (data.T k 1)).le
      simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN _) hcoeff
    apply (ENNReal.ofReal_le_ofReal hscale).trans
    simpa only [phys_eq_physCube, I_eq_blockInterval, blockInterval, packetLength, blockLength] using hrow

end Submission.Obl.k4_scalar_grid_cartesian_field
