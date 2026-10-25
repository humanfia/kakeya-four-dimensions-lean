-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OriginalPaletteVector, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

open Set MeasureTheory
open ParentSource ParentSource.Native
open scoped ENNReal

noncomputable section

/-- The frozen row packet writes the two original integer velocity
bins as a function on Fin2. This changes only their representation. -/
def palettePairVector (q : ℤ×ℤ) : Fin 2 → ℤ := ![q.1,q.2]

theorem measurable_palettePairVector : Measurable palettePairVector := measurable_of_countable _

theorem palettePairVector_velocity (mesh : ℝ) (vel : Fin 2 → ℝ) :
    palettePairVector (velocityPalette mesh vel)=(fun j => ⌊vel j/mesh⌋) := by
  ext j
  fin_cases j <;> rfl

/-- Every original-palette Borel cap passes to the exact vector-code
singleton required by RowPacket, with its coefficient unchanged. -/
theorem vector_palette_guarded_cap
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (π : Measure (ℤ×ℤ)) (mesh : ℝ) (vel : Ω → Fin 2 → ℝ)
    (guard : Set Ω) (coefficient : ENNReal)
    (hcap : ∀ D : Set (ℤ×ℤ), MeasurableSet D →
      μ (guard∩{z | velocityPalette mesh (vel z)∈D}) ≤ coefficient*π D) :
    ∀ q : Fin 2 → ℤ, μ (guard∩{z | (fun j => ⌊vel z j/mesh⌋)=q}) ≤
      coefficient*(π.map palettePairVector) {q} := by
  intro q
  let D := palettePairVector ⁻¹' {q}
  have hD : MeasurableSet D := measurable_palettePairVector (measurableSet_singleton q)
  have heq : {z | velocityPalette mesh (vel z)∈D}={z | (fun j => ⌊vel z j/mesh⌋)=q} := by
    ext z
    change palettePairVector (velocityPalette mesh (vel z))=q ↔ _
    rw [palettePairVector_velocity]
    rfl
  rw [Measure.map_apply measurable_palettePairVector (measurableSet_singleton q)]
  simpa only [heq] using hcap D hD

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ)

/-- The unchanged original coarse physical-velocity palette, in the
literal Fin2 representation of the frozen row packet. -/
def originalVectorPalette (root : Fin p.C) (mesh : ℝ) : Measure (Fin 2 → ℤ) :=
  ((Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette mesh)).map palettePairVector

theorem originalVectorPalette_probability (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w⊆d.E k w)
    (root : Fin p.C) (hactive : F.active root) (mesh : ℝ) :
    IsProbabilityMeasure (originalVectorPalette F root mesh) := by
  haveI : IsProbabilityMeasure Q.law := Q.probability hd hHE (zero_lt_one.trans_le hp.1)
  haveI : IsProbabilityMeasure (Q.coarseLaw (p.lev root) (F.code root)) :=
    ProbabilityTheory.cond_isProbabilityMeasure (F.coarse_positive root hactive)
  dsimp only [originalVectorPalette]
  infer_instance

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
