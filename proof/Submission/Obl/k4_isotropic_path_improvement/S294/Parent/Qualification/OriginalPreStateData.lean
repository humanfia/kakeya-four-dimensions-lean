-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalPreStateData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DerivativeListsFromDyadicFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory

noncomputable section

/-- The exact metadata prepared before final child states: original
full-prior floors and actual ordinary-cell derivative tables. -/
structure OriginalPreStateData {Λ I : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (palette : Measure (Fin 2 → ℝ)) (dimension exponent : ℝ) (start count : ℕ)
    (level : I → ℕ) (KL : ℝ) where
  floors : OriginalDyadicFloorData ν c E palette dimension exponent start count
  tables : OriginalDerivativeListData c E level (fun _ => KL)

/-- Later arbitrary source cuts preserve the original prior/palette
and all pre-state metadata, without renewing their source references. -/
def OriginalPreStateData.restrict {Λ I : Type*} [MeasurableSpace Λ]
    {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {palette : Measure (Fin 2 → ℝ)} {dimension exponent : ℝ} {start count : ℕ}
    {level : I → ℕ} {KL : ℝ}
    (data : OriginalPreStateData ν c E palette dimension exponent start count level KL)
    {S : Set (Λ × ℝ)} (hSE : S⊆E) :
    OriginalPreStateData ν c S palette dimension exponent start count level KL :=
  ⟨data.floors.restrict hSE,data.tables.restrict hSE⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
