/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/UncappedPacket.lean (namespace renamed to
Submission.Obl.k4_uncapped_native_capping). Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.StageInterfaces
import Submission.Obl.k4_uncapped_native_capping.PacketAnalysis

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

namespace PacketData

/-- The geometric input used by original-law projected caps. -/
structure CappingGeometry {W : ℕ} (p : PacketData W) (N loss U f₀ ξ : ℝ)
    (ν : Fin W → Measure Traj) : Prop where
  prior_lower : ∀ a, ENNReal.ofReal (N ^ (-f₀ - ξ) * |Matrix.det (p.Q a)|) ≤ ν (p.γ a) (p.A a)
  tangent_time : ∀ a, p.tangent a 0 = 0
  physical : ∀ a, ∃ (e n : EuclideanSpace ℝ (Fin 2)) (β : ℝ),
    e = packetAxis p.q (p.tangent a) ∧ ‖e‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ e n = 0 ∧
      p.q / N ^ loss ≤ ‖Matrix.toEuclideanLin (p.Q a).transpose e‖ ∧
      ∀ l ∈ p.A a, |inner ℝ n (v l) - β| ≤ N ^ loss * N ^ (-U)

theorem CappingGeometry.prior_ne_zero
    {W : ℕ} {p : PacketData W} {N K loss U f₀ ξ h : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ} {M D : ℕ}
    (hp : p.CappingGeometry N loss U f₀ ξ ν)
    (hg : p.Geometry N K ω ν E P B M D loss h) (hN : 0 < N) (a : Fin p.C) :
    ν (p.γ a) (p.A a) ≠ 0 := by
  have hdet : 0 < |Matrix.det (p.Q a)| := abs_pos.mpr (hg.charts a).1
  exact ((ENNReal.ofReal_pos.mpr
    (mul_pos (Real.rpow_pos_of_pos hN _) hdet)).trans_le (hp.prior_lower a)).ne'

end PacketData

/-- Repackage the exact intermediate sample without selecting another
witness, changing any arrays, or weakening its outside quantifiers. -/
theorem UncappedNativeSample.exists_packetData
    {N K : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h χ d s m S U f₀ ξ : ℝ}
    (hp : UncappedNativeSample N K W ω ν E P B M D loss h χ d s m S U f₀ ξ) :
    ∃ p : PacketData W,
      p.Geometry N K ω ν E P B M D loss h ∧
      p.ProvisionalAnalysis N χ d s m S U ω ν P B ∧
      (∀ a, ENNReal.ofReal (N ^ (-χ)) ≤ p.law a univ) ∧
      ENNReal.ofReal (N ^ (-loss)) ≤ p.mass ω ν ∧
      p.CappingGeometry N loss U f₀ ξ ν := by
  obtain ⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal,
    hK, ht, hC, hsep, hlst, hlistm, hcharts, hcoords, hbudget, hlaw, hmass, hcert, hcap⟩ := hp
  let p : PacketData W := ⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal⟩
  refine ⟨p, ⟨hK, ht, hC, hsep, hlst, hlistm, hcharts, hcoords, hbudget⟩,
    ⟨fun a => (hlaw a).1, fun a => (hlaw a).2.2.1,
      fun a => (hlaw a).2.2.2.1, fun a => (hlaw a).2.2.2.2.1,
      fun a => (hlaw a).2.2.2.2.2.1, fun a => (hlaw a).2.2.2.2.2.2, hcert⟩,
    fun a => (hlaw a).2.1, hmass,
    ⟨fun a => (hcap a).1, fun a => (hcap a).2.1, fun a => (hcap a).2.2⟩⟩

end
end Submission.Obl.k4_uncapped_native_capping
