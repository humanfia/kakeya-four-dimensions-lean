import Submission.Obl.k4_raw_localized_native_systems.C.Problems
import Submission.Obl.k4_raw_localized_native_systems.C.RecoveryInterface
import Submission.Obl.k4_raw_localized_native_systems.C.ScalarAssignments

/-
Adapted from this LOT tree, o178, session x0596, `ProjectedPackets.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

def packetTimeLength {p : Data} {k : ℕ} (a : Atlas p k) : ℝ := 1 / (2 : ℝ) ^ a.T

def packetStart {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) : ℝ :=
  ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T

def packetExpand {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C)
    (z : (ℕ × (Fin 6 → ℝ)) × ℝ) : (ℕ × (Fin 6 → ℝ)) × ℝ :=
  (z.1, packetStart a b + packetTimeLength a * z.2)

def packetCoeff {p : Data} {k : ℕ} (a : Atlas p k)
    (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ) (b : Fin a.C) :=
  clippedScalarCoeff (p.P k (a.γ b)) (packetStart a b) (packetTimeLength a)
    (offset b) (tangent b) (a.A b)

def packetObservation {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C)
    (z : (ℕ × (Fin 6 → ℝ)) × ℝ) : EuclideanSpace ℝ (Fin 3) × ℤ :=
  gobs (p.B k (a.γ b)) (gδ (p.N k) p.L) (packetExpand a b z)

/-- The original prior-times-block budget, without its world weight. -/
def packetBudget {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) : ENNReal :=
  ENNReal.ofReal (packetTimeLength a) * p.ν k (a.γ b) (a.A b)

/-- Concrete finite inputs to scalar recovery.  The projected cap tolerance
`ηp` is fixed before the original sample is selected.  The independent loss
`loss` bounds the actual chart geometry, original lists, and retained mass. -/
structure ProjectedPackets (p : Data) (k M D : ℕ)
    (loss h ηp d s m S U : ℝ) where
  atlas : Atlas p k
  known : atlas.KnownAt M D (p.N k ^ loss) 0
  list_measurable : ∀ w b, MeasurableSet {o | b ∈ atlas.lst w o}
  time : (2 : ℝ) ^ atlas.T ≤ p.N k ^ (h + loss)
  native : ∀ b, atlas.R b = p.P k (atlas.γ b)
  offset : Fin atlas.C → ℝ
  tangent : Fin atlas.C → Fin 3 → ℝ
  coordinate_bound : ∀ b, |offset b| ≤ p.N k ^ M ∧
    (∀ i, |tangent b i| ≤ p.N k ^ M) ∧ |(packetTimeLength atlas)⁻¹| ≤ p.N k ^ M
  prior : Fin atlas.C → Measure (ℕ × (Fin 6 → ℝ))
  law : Fin atlas.C → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)
  base : Fin atlas.C → (EuclideanSpace ℝ (Fin 3) × ℤ) → EuclideanSpace ℝ (Fin 2)
  signal : Fin atlas.C → (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ
  projected : ∀ b, ProjectedScalarLaw (p.N k) ηp d s m S U (prior b) (law b)
    (packetCoeff atlas offset tangent b)
  base_measurable : ∀ b, Measurable (base b)
  signal_measurable : ∀ b, Measurable (signal b)
  observed_signal : ∀ b, ∀ᵐ z ∂law b,
    base b (packetObservation atlas b z) =
      WithLp.toLp 2 ![z.2, scalarY (packetCoeff atlas offset tangent b z.1) z.2] ∧
    |scalarX (packetCoeff atlas offset tangent b z.1) z.2 -
      signal b (packetObservation atlas b z)| ≤ p.N k ^ (-1 + ηp)
  assignment_support : ∀ b, ∀ᵐ z ∂law b, z.1 ∈ atlas.A b
  original_domination : ∀ b,
    packetBudget atlas b • Measure.map (packetExpand atlas b) (law b) ≤
      ((p.ν k (atlas.γ b)).prod volume).restrict (atlas.F b)
  retained_mass : ENNReal.ofReal (p.N k ^ (-loss)) ≤
    ∑ b, ENNReal.ofReal (p.ω k (atlas.γ b)) * packetBudget atlas b * law b Set.univ

theorem packetTimeLength_pos {p : Data} {k : ℕ} (a : Atlas p k) :
    0 < packetTimeLength a := by unfold packetTimeLength; positivity

theorem packetExpand_measurable {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) :
    Measurable (packetExpand a b) := by
  exact measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))

theorem packetStart_mem_unit {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) :
    packetStart a b ∈ Set.Icc (0 : ℝ) 1 := by
  have hq : (0 : ℝ) < 2 ^ a.T := by positivity
  refine ⟨div_nonneg (Nat.cast_nonneg _) hq.le, (div_le_one hq).mpr ?_⟩
  exact_mod_cast (a.j b).isLt.le

end
end Submission.Obl.k4_raw_localized_native_systems.C
