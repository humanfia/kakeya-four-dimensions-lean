-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/NativeQualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenNativeQualification.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenNativeQualification.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit abca4d31. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2HigherJets

set_option autoImplicit false

/-!
# Native qualification for the frozen packets of o106 (paper Prop. `a05:qualification`)

The world contract (x0352): a frozen packet `p`, labelled incidences `E ⊆ p.event` carrying a
version-2 scalar-normal world `ScalarNormal ν cz E F piece K ζ d` (any zoomed coefficients `cz`,
e.g. the zoom of `p.scalarCoefficients` in a full original parameter block), the unchanged
original graph row `G`, the velocity-graph estimate
`|(p.signal l)'(t) - G(z) · p.velocity l| ≤ graphError` and the row representation
`|G(z)_{i+1} - F(t)_i| ≤ rowError` on `E`.  Then some `z ∈ E` is natively qualified
(`Jets2.NativeQualified`): the native three-row polynomial `Q₀ = c₁ + 2 c₂ X - V · P`,
`Q_{i+1} = P_i`, built from the ORIGINAL coefficients `c = p.scalarCoefficients z.1` of the
original indexed line (no rescaling), fits `G` on labelled times of the same line in the same
dyadic block, with the same true label, in ordinary time.

* `velocity_graph_eq`: the graph estimate in the coefficient form of `Jets2`;
* `physical_native_qualification_of_higherJets` and `physical_native_qualification` (with the
  version-2 higher jets `Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2.v2_higherJetsStatement`).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

noncomputable section

/-- The velocity-graph estimate of an original line, in the coefficients of the scalar model. -/
theorem velocity_graph_eq (p : PhysicalModel) (G : Fin 3 → ℝ) (l : Ln) (t : ℝ) :
    (p.signal l).derivative.eval t - ∑ j, G j * p.velocity l j =
      p.scalarCoefficients l 1 + 2 * p.scalarCoefficients l 2 * t -
        (G 0 + G 1 * p.scalarCoefficients l 4 + G 2 * p.scalarCoefficients l 6) := by
  rw [← p.scalar_x_derivative l t, Fin.sum_univ_three]
  simp [velocity]

/-- A scalar-normal world has a labelled incidence. -/
theorem nonempty_of_scalarNormal {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}
    {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ}
    {K ζ d : ℝ} (h : ScalarNormal ν c E F piece K ζ d) : E.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  have h1 := h.dense
  rw [measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  have hK : 0 < K⁻¹ := inv_pos.mpr (lt_of_lt_of_le one_pos h.one_le_K)
  linarith

/-- **Native qualification for a frozen packet**, from the higher-jet statement. -/
theorem physical_native_qualification_of_higherJets (hHJ : HigherJetsStatement) {d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) {M : ℕ} (hM : 2 ≤ M) {c_h : ℝ} (hch : 0 < c_h) :
    ∃ c_ζ : ℝ, 0 < c_ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N →
      ∀ (p : PhysicalModel) (ν : Measure Ln) (cz : Ln → Fin 7 → ℝ) (E : Set Ev)
        (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Ln → Fin 7 → ℤ) (K ζ : ℝ) (T : ℕ),
        K ≤ N ^ α → N ^ (-c_h) / K ≤ ((2 : ℝ) ^ T)⁻¹ → ((2 : ℝ) ^ T)⁻¹ ≤ K * N ^ (-c_h) →
        ζ ≤ ((2 : ℝ) ^ T)⁻¹ ^ c_ζ → ScalarNormal ν cz E F piece K ζ d → E ⊆ p.event →
        ∀ (ι : Type) (lab : Ev → ι) (G : Ev → Fin 3 → ℝ)
          (B graphError rowError : ℝ), 17 * p.slack ≤ B →
        (∀ z ∈ E, |(p.signal z.1).derivative.eval z.2 - ∑ j, G z j * p.velocity z.1 j| ≤
          graphError) →
        (∀ z ∈ E, ∀ i : Fin 2, |G z i.succ - F z.2 i| ≤ rowError) →
        (∀ z ∈ E, ∀ v, (z.1, v) ∈ E → v ∈ dyadicBlock T z.2 → lab (z.1, v) = lab z) →
        ∃ z ∈ E, NativeQualified E lab G M T (3 * B + (1 + 2 * B) * N ^ ε)
          (graphError + (1 + 2 * B) * (rowError + ((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8)))
          (((2 : ℝ) ^ T)⁻¹ * N ^ (-ε)) z := by
  obtain ⟨c_ζ, hcζ, h1⟩ := nativeQualificationStatement_of_higherJets hHJ d hd0 hd1 M hM c_h hch
  refine ⟨c_ζ, hcζ, fun ε hε => ?_⟩
  obtain ⟨α, hα, N₀, hN₀, h2⟩ := h1 ε hε
  refine ⟨α, hα, N₀, hN₀, ?_⟩
  intro N hN p ν cz E F piece K ζ T hK hT1 hT2 hζ hSN hEp ι lab G B graphError rowError hB
    hgraph hrow hlab
  have hcB : ∀ z ∈ E, ∀ i, |p.scalarCoefficients z.1 i| ≤ B := fun z hz i =>
    (p.scalar_coefficients_bound z.1 (p.event_assignment z (hEp hz)) i).trans hB
  have hB0 : 0 ≤ B := by
    obtain ⟨z, hz⟩ := nonempty_of_scalarNormal hSN
    exact (abs_nonneg _).trans (hcB z hz 0)
  refine h2 N hN Ln ν cz E F piece K ζ T hK hT1 hT2 hζ hSN ι lab p.scalarCoefficients G B
    graphError rowError hB0 hcB (fun z hz => ?_) hrow hlab
  rw [← velocity_graph_eq p (G z) z.1 z.2]
  exact hgraph z hz

/-- **Native qualification for a frozen packet** (version-2 higher jets, unconditional). -/
theorem physical_native_qualification {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) {M : ℕ} (hM : 2 ≤ M)
    {c_h : ℝ} (hch : 0 < c_h) :
    ∃ c_ζ : ℝ, 0 < c_ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N →
      ∀ (p : PhysicalModel) (ν : Measure Ln) (cz : Ln → Fin 7 → ℝ) (E : Set Ev)
        (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Ln → Fin 7 → ℤ) (K ζ : ℝ) (T : ℕ),
        K ≤ N ^ α → N ^ (-c_h) / K ≤ ((2 : ℝ) ^ T)⁻¹ → ((2 : ℝ) ^ T)⁻¹ ≤ K * N ^ (-c_h) →
        ζ ≤ ((2 : ℝ) ^ T)⁻¹ ^ c_ζ → ScalarNormal ν cz E F piece K ζ d → E ⊆ p.event →
        ∀ (ι : Type) (lab : Ev → ι) (G : Ev → Fin 3 → ℝ)
          (B graphError rowError : ℝ), 17 * p.slack ≤ B →
        (∀ z ∈ E, |(p.signal z.1).derivative.eval z.2 - ∑ j, G z j * p.velocity z.1 j| ≤
          graphError) →
        (∀ z ∈ E, ∀ i : Fin 2, |G z i.succ - F z.2 i| ≤ rowError) →
        (∀ z ∈ E, ∀ v, (z.1, v) ∈ E → v ∈ dyadicBlock T z.2 → lab (z.1, v) = lab z) →
        ∃ z ∈ E, NativeQualified E lab G M T (3 * B + (1 + 2 * B) * N ^ ε)
          (graphError + (1 + 2 * B) * (rowError + ((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8)))
          (((2 : ℝ) ^ T)⁻¹ * N ^ (-ε)) z :=
  physical_native_qualification_of_higherJets Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2.v2_higherJetsStatement hd0 hd1 hM hch

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
