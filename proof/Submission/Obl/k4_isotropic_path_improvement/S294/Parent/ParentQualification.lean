-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentQualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- The scalar-coordinate identities are adapted from this LOT tree,
o265/x1030 c13f2967e10c, GlobalParentCoefficients.lean. The coefficient
table and signal bounds themselves are imported from the accepted library. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSignal
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.PotentialFits
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set

noncomputable section

namespace ParentQualification

open ParentSignal Qualification

/-- The scalar hidden coordinate is the global physical parent value. -/
theorem global_signal {P : Po} (hP : P.totalDegree ≤ 2) (l : Ln) (t : ℝ) :
    Jets2.zx (globalCoefficients P l) t = MvPolynomial.eval (xp l t) P :=
  Submission.Lib.K4GlobalParentSignal.global_signal hP l t

theorem global_base (P : Po) (l : Ln) (t : ℝ) :
    Jets2.zy (globalCoefficients P l) t = fun i => y l t i := by
  funext i
  fin_cases i <;> simp [globalCoefficients, Jets2.zy, y, x] <;> ring

theorem global_velocity (P : Po) (l : Ln) :
    Jets2.zv (globalCoefficients P l) = fun i => v l i := by
  funext i
  fin_cases i <;> rfl

theorem global_residual {P : Po} (hP : P.totalDegree ≤ 2)
    (F : ℝ → Fin 2 → ℝ) (l : Ln) (t : ℝ) :
    Jets2.zR F (globalCoefficients P l) t =
      rate P l t - (F t 0 * v l 0 + F t 1 * v l 1) := by
  unfold Jets2.zR
  rw [global_rate hP, global_velocity]
  simp only [dotProduct, Fin.sum_univ_two]

theorem global_spacetime {P : Po} (hP : P.totalDegree ≤ 2) (l : Ln) (t : ℝ) :
    Jets2.zpos (globalCoefficients P l) t =
      ![t, MvPolynomial.eval (xp l t) P, (xp l t) 1, (xp l t) 2] := by
  unfold Jets2.zpos
  rw [global_signal hP, global_base]
  rfl

/-- The checked two-tangent qualification theorem applies to the actual
physical parent and original planar velocities, with no old packet test
substituted for the signal. Every scalar-normal hypothesis remains explicit. -/
theorem native_qualification {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    {M : ℕ} (hM : 2 ≤ M) {c_h : ℝ} (hch : 0 < c_h) :
    ∃ c_ζ : ℝ, 0 < c_ζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N →
      ∀ (ν : Measure Ln) (cz : Ln → Fin 7 → ℝ) (E : Set Ev)
        (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Ln → Fin 7 → ℤ) (K ζ : ℝ) (T : ℕ),
      K ≤ N ^ α → N ^ (-c_h) / K ≤ ((2 : ℝ) ^ T)⁻¹ →
      ((2 : ℝ) ^ T)⁻¹ ≤ K * N ^ (-c_h) →
      ζ ≤ ((2 : ℝ) ^ T)⁻¹ ^ c_ζ → Jets2.ScalarNormal ν cz E F piece K ζ d →
      ∀ (P : Po), P.totalDegree ≤ 2 →
      ∀ (ι : Type) (lab : Ev → ι) (G : Ev → Fin 3 → ℝ) (B graphError rowError : ℝ),
      0 ≤ B → (∀ z ∈ E, ∀ i, |globalCoefficients P z.1 i| ≤ B) →
      (∀ z ∈ E, |rate P z.1 z.2 - ∑ j, G z j * PotentialFits.direction z.1 j| ≤ graphError) →
      (∀ z ∈ E, ∀ i : Fin 2, |G z i.succ - F z.2 i| ≤ rowError) →
      (∀ z ∈ E, ∀ v, (z.1, v) ∈ E → v ∈ Jets2.dyadicBlock T z.2 → lab (z.1, v) = lab z) →
      ∃ z ∈ E, Jets2.NativeQualified E lab G M T (3 * B + (1 + 2 * B) * N ^ ε)
        (graphError + (1 + 2 * B) * (rowError + ((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8)))
        (((2 : ℝ) ^ T)⁻¹ * N ^ (-ε)) z := by
  obtain ⟨c_ζ, hc_ζ, hnext⟩ := Jets2.nativeQualificationStatement d hd0 hd1 M hM c_h hch
  refine ⟨c_ζ, hc_ζ, fun ε hε => ?_⟩
  obtain ⟨α, hα, N₀, hN₀, hfit⟩ := hnext ε hε
  refine ⟨α, hα, N₀, hN₀, ?_⟩
  intro N hN ν cz E F piece K ζ T hK hT₁ hT₂ hζ hnormal P hP ι lab G B ge re hB hcoeff
    hgraph hrow hlab
  apply hfit N hN Ln ν cz E F piece K ζ T hK hT₁ hT₂ hζ hnormal
    ι lab (globalCoefficients P) G B ge re hB hcoeff _ hrow hlab
  intro z hz
  have hh := hgraph z hz
  rw [← global_rate hP] at hh
  simpa [Fin.sum_univ_three, PotentialFits.direction, globalCoefficients] using hh

end ParentQualification

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
