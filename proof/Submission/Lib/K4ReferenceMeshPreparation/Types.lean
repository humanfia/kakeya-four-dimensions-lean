/-
Adapted from: here:o107 (session x0735), original-reference cap and
two-scale record helpers in Submission/Obl/k4_finite_narrowness_path_improvement/.
Accepted history-floor and mesh-cover proofs are imported.
-/
import Submission.Lib.K4AffineMeshCaps.Saturation

namespace Submission.Lib.K4ReferenceMeshPreparation

noncomputable section

open MeasureTheory Set MvPolynomial
open scoped ENNReal

abbrev NativeCellCaps {Ω : Type*} [MeasurableSpace Ω]
    (N K d S R : ℝ) (μ : Measure Ω) (π : Measure ℝ)
    (x : Ω → Fin 4 → ℝ) (P : MvPolynomial (Fin 4) ℝ) (velocity : Ω → ℝ) : Prop :=
  ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
    (∀ a : ℤ, π {w | ⌊w / N ^ (-v)⌋ = a} ≤ ENNReal.ofReal (K * N ^ (-S*v))) ∧
    (∀ (q : Fin 3 → ℤ) (a : ℤ),
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
          (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊eval (x p) P / N ^ (-s)⌋ = a} ≤
        ENNReal.ofReal (K * N ^ (-3*r-d*s))) ∧
    (∀ (q : Fin 3 → ℤ) (a z : ℤ),
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
          (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊eval (x p) P / N ^ (-s)⌋ = a ∧
        ⌊velocity p / N ^ (-v)⌋ = z} ≤
        ENNReal.ofReal (K * N ^ (-3*r-d*s)) * π {w | ⌊w / N ^ (-v)⌋ = z})

abbrev FullCellCaps {Ω : Type*} [MeasurableSpace Ω]
    (N K d S R : ℝ) (μ : Measure Ω) (π : Measure ℝ)
    (x : Ω → Fin 4 → ℝ) (P : MvPolynomial (Fin 4) ℝ) (velocity : Ω → ℝ) : Prop :=
  ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
    (∀ a : ℤ, π {w | ⌊w / N ^ (-v)⌋ = a} ≤ ENNReal.ofReal (K * N ^ (-S*v))) ∧
    (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ),
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
          (fun i : Fin 3 => x p i.castSucc) = q ∧
        ⌊(if h then eval (x p) P else x p 3) / N ^ (-s)⌋ = a} ≤
        ENNReal.ofReal (K * N ^ (-3*r-d*s))) ∧
    (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a z : ℤ),
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
          (fun i : Fin 3 => x p i.castSucc) = q ∧
        ⌊(if h then eval (x p) P else x p 3) / N ^ (-s)⌋ = a ∧
        ⌊velocity p / N ^ (-v)⌋ = z} ≤
        ENNReal.ofReal (K * N ^ (-3*r-d*s)) * π {w | ⌊w / N ^ (-v)⌋ = z})

/-- Subsequent original-law deletions preserve all Boolean cap fields
with the same external palette and the same numerical budget. -/
theorem fullCellCaps_mono_measure {Ω : Type*} [MeasurableSpace Ω]
    {N K d S R : ℝ} {μ ρ : Measure Ω} {π : Measure ℝ}
    {x : Ω → Fin 4 → ℝ} {P : MvPolynomial (Fin 4) ℝ} {velocity : Ω → ℝ}
    (hρ : ρ ≤ μ) (h : FullCellCaps N K d S R μ π x P velocity) :
    FullCellCaps N K d S R ρ π x P velocity := by
  intro r s v hrl hrh hs0 hsh hvl hvh
  obtain ⟨hπ,hp,hj⟩ := h r s v hrl hrh hs0 hsh hvl hvh
  exact ⟨hπ,fun b q a => (hρ _).trans (hp b q a),
    fun b q a z => (hρ _).trans (hj b q a z)⟩

theorem nativeCellCaps_mono_budget {Ω : Type*} [MeasurableSpace Ω]
    {N K K' d S R : ℝ} {μ : Measure Ω} {π : Measure ℝ}
    {x : Ω → Fin 4 → ℝ} {P : MvPolynomial (Fin 4) ℝ} {velocity : Ω → ℝ}
    (hN : 0 ≤ N) (hKK : K ≤ K') (h : NativeCellCaps N K d S R μ π x P velocity) :
    NativeCellCaps N K' d S R μ π x P velocity := by
  have hscale (u : ℝ) : ENNReal.ofReal (K*N^u) ≤ ENNReal.ofReal (K'*N^u) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg hN _))
  intro r s v hrl hrh hs0 hsh hvl hvh
  obtain ⟨hπ,hp,hj⟩ := h r s v hrl hrh hs0 hsh hvl hvh
  exact ⟨fun a => (hπ a).trans (hscale _),
    fun q a => (hp q a).trans (hscale _),
    fun q a z => (hj q a z).trans (mul_le_mul' (hscale _) le_rfl)⟩


end

end Submission.Lib.K4ReferenceMeshPreparation
