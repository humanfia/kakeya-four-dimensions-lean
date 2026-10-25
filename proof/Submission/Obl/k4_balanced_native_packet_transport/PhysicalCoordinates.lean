import Submission.Obl.k4_balanced_native_packet_transport.NativeCoordinates

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

def physicalScalarBase (t₀ q offset center : ℝ) (v : Fin 3 → ℝ) (p : Inc) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(p.2 - t₀) / q,
    (offset + ∑ i : Fin 3, v i * x p.1 p.2 i.castSucc - center) / q]

def physicalScalarSlope (v : Fin 3 → ℝ) (l : Traj) : ℝ :=
  v 0 + v 1 * l.2 3 + v 2 * l.2 4

/-- Physical and scalar coordinates agree at the exact original incidence. -/
theorem nativeCoeff_physical_coordinates
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q offset center : ℝ) (hq : q ≠ 0) (v : Fin 3 → ℝ)
    {A : Set Traj} {p : Inc} (hp : p.1 ∈ A) :
    let b := nativeCoeff P t₀ q ((offset - center) / q) (fun i => v i / q) A p.1
    WithLp.toLp 2 ![(p.2 - t₀) / q, scalarY b ((p.2 - t₀) / q)] =
        physicalScalarBase t₀ q offset center v p ∧
      scalarX b ((p.2 - t₀) / q) = MvPolynomial.eval (x p.1 p.2) P ∧
      b 1 = physicalScalarSlope v p.1 := by
  dsimp only
  have htime : t₀ + q * ((p.2 - t₀) / q) = p.2 := by field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [nativeCoeff_scalarY P t₀ q ((offset - center) / q) (fun i => v i / q) hp,
      htime]
    unfold physicalScalarBase
    congr 2
    simp only [Fin.sum_univ_three]
    ring
  · rw [nativeCoeff_scalarX P hP t₀ q ((offset - center) / q) (fun i => v i / q) hp,
      htime]
  · simp [nativeCoeff, hp, physicalScalarSlope, x, Fin.sum_univ_three]
    field_simp
    ring

end
end Submission.Obl.k4_balanced_native_packet_transport
