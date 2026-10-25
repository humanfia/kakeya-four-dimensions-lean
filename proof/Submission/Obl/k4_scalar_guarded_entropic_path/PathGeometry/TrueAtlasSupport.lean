/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrueAtlasSupport.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueNormalization
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathSupport

/-! Keep each full true source incidence piece separate from the smaller
selected piece used by exact homogenization. The common final law remains
supported in the full piece, whose original true floor is unchanged. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

namespace TrueNormalization

variable {p q : Code} {r b h : ℝ}

/-- The full source TRUE incidence piece for the same retained chart.
It is separate from the subsequently shrunk selected incidence set. -/
def ambientSelected (a : TrueNormalization p q r b h) :
    (k : ℕ) → Fin (W q k) → Set ((ℕ × ScalarCoeff) × ℝ) := by
  rcases a with ⟨hp, atlas, M', D', d', out, heq⟩
  cases heq
  exact fun k i => atlas.C (out.sample k) (out.embedding k i)

theorem selected_subset_ambient (a : TrueNormalization p q r b h)
    (k : ℕ) (i : Fin (W q k)) :
    a.witness.selected k i ⊆ a.ambientSelected k i := by
  rcases a with ⟨hp, atlas, M', D', d', out, heq⟩
  cases heq
  exact out.selected_subset k i

theorem measurableSet_ambientSelected (a : TrueNormalization p q r b h)
    (k : ℕ) (i : Fin (W q k)) : MeasurableSet (a.ambientSelected k i) := by
  rcases a with ⟨hp, atlas, M', D', d', out, heq⟩
  cases heq
  exact ((atlas.true_data (out.sample k)).2.2.1 (out.embedding k i)).2

/-- The floor is evaluated against the ORIGINAL parent incidence law and
uses the unchanged full source piece, prior width and actual time block. -/
theorem ambient_mass_floor (a : TrueNormalization p q r b h)
    (k : ℕ) (i : Fin (W q k)) :
    ENNReal.ofReal (N p (a.witness.sample k) ^ (-f p r) * a.witness.width k i /
      (N p (a.witness.sample k) ^ a.floorLoss k * (2 : ℝ) ^ a.witness.T k)) ≤
      mu p (a.witness.sample k) (a.witness.world k i) (a.ambientSelected k i) := by
  rcases a with ⟨hp, atlas, M', D', d', out, heq⟩
  cases heq
  change ENNReal.ofReal (N p (out.witness.sample k) ^ (-f p r) * out.witness.width k i /
      (N p (out.witness.sample k) ^ atlas.ε (out.sample k) * (2 : ℝ) ^ out.witness.T k)) ≤
    mu p (out.witness.sample k) (out.witness.world k i)
      (atlas.C (out.sample k) (out.embedding k i))
  rw [out.data_eq]
  exact (((atlas.true_data (out.sample k)).2.2.2.2.2.1 (out.embedding k i)).2.2.2.2.2.2.2.2.2.2.2) rfl

/-- Pull the full true source piece to the normalized tagged world. -/
def ambientPreimage (a : TrueNormalization p q r b h) (k : ℕ) :
    Set (Fin (W q k) × PathMeasures.State) :=
  {z | (a.witness.incidenceEquiv a.parent_exact k z.1).symm z.2 ∈ a.ambientSelected k z.1}

theorem measurableSet_ambientPreimage (a : TrueNormalization p q r b h) (k : ℕ) :
    MeasurableSet (a.ambientPreimage k) := by
  have heq : a.ambientPreimage k =
      ⋃ i, ({i} ×ˢ ((a.witness.incidenceEquiv a.parent_exact k i).symm ⁻¹'
        a.ambientSelected k i)) := by
    ext z
    simp [ambientPreimage]
  rw [heq]
  exact MeasurableSet.iUnion fun i => (measurableSet_singleton i).prod
    ((a.measurableSet_ambientSelected k i).preimage
      (a.witness.incidenceEquiv a.parent_exact k i).symm.measurable)

/-- Full final-mixture measure lies in the original true source piece
under this very retained normalization map. -/
theorem ambientSelected_ae (a : TrueNormalization p q r b h) (k : ℕ) :
    ∀ᵐ z ∂PathMeasures.worldMixture q k,
      (a.witness.incidenceEquiv a.parent_exact k z.1).symm z.2 ∈
        a.ambientSelected k z.1 := by
  filter_upwards [PathMeasures.selectedPreimage_ae a.witness a.parent_exact k] with z hz
  exact a.selected_subset_ambient k z.1 hz

end TrueNormalization

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
