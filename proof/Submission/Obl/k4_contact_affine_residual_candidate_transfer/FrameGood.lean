import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ResidualFields
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.OriginalLaw

/-!
# What the residual labels need from one index

`FrameGood` lists the facts at one index `k` that the residual labels use:
the original atlas at the finitely many grid depths (with the original
constant `K`), the horizontal centering of every original label (constant
`K₂`), the original joint palette cap for velocity meshes in `[Rk⁻¹, Rk]`, the
ancestor maps, and the core: it lies in the parent's successful incidence,
every core point lies in a node at every level, a node meeting the core lies in
the parent block and history, and such a node keeps the fraction `θ` of its full
original reference `q * ν(A)` on the core.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (fr : Frame D k s₀ U')

/-- The original block length at level `h`. -/
def ql (h : ℕ) : ℝ := (2 : ℝ) ^ (-(fr.Tl h : ℤ))

/-- The midpoint of an original block. -/
def mid (h : ℕ) (i : Fin (fr.nl h)) : ℝ :=
  ((D.j k (fr.depth h) i : ℕ) + (1 : ℝ) / 2) * fr.ql h

end Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}

/-- The facts at one index used by the residual labels. -/
structure FrameGood (f : Frame D k s₀ U') (Rk θ K₂ e₀' : ℝ) : Prop where
  N_ge : 2 ≤ D.N k
  K_ge : 1 ≤ D.K k
  θ_pos : 0 < θ
  θ_le : θ ≤ 1
  H_ge : 1 ≤ f.H
  K₂_ge : 1 ≤ K₂
  m_pos : 1 ≤ f.m
  U'_pos : 0 < U'
  d_nonneg : 0 ≤ D.d
  κ_pos : 0 < D.κ
  ℓ_eq : D.ℓ = D.κ
  depth_zero : f.depth 0 = s₀
  count : ∀ h ≤ f.m, D.N k ^ (D.κ * f.depth h) / D.K k ≤ (2 : ℝ) ^ f.Tl h ∧
    (2 : ℝ) ^ f.Tl h ≤ D.K k * D.N k ^ (D.κ * f.depth h)
  meas : ∀ h ≤ f.m, ∀ i : Fin (f.nl h), MeasurableSet (D.A k (f.depth h) i) ∧
    MeasurableSet (D.B k (f.depth h) i) ∧ D.B k (f.depth h) i ⊆ D.A k (f.depth h) i
  disj : ∀ h ≤ f.m, ∀ i i' : Fin (f.nl h), i ≠ i' →
    D.j k (f.depth h) i = D.j k (f.depth h) i' →
      Disjoint (D.A k (f.depth h) i) (D.A k (f.depth h) i')
  floor : ∀ h ≤ f.m, ∀ i : Fin (f.nl h),
    ENNReal.ofReal ((D.N k ^ (-f.depth h)) ^ D.d * f.ql h ^ 2 *
      D.N k ^ (-D.ℓ * f.depth h) / D.K k) ≤ D.ν k (D.A k (f.depth h) i)
  ceil : ∀ h ≤ f.m, ∀ i : Fin (f.nl h),
    D.ν k (D.A k (f.depth h) i) ≤ ENNReal.ofReal (D.K k * (D.N k ^ (-f.depth h)) ^ D.d *
      f.ql h ^ 2 * D.N k ^ (-D.ℓ * f.depth h))
  cbound : ∀ h ≤ f.m, ∀ i : Fin (f.nl h), ∀ e, |D.c k (f.depth h) i e| ≤ D.K k
  rows : ∀ h ≤ f.m, ∀ i : Fin (f.nl h), ∀ l ∈ D.A k (f.depth h) i, ∀ t ∈ f.block h i,
    |(D.x k l t) 1 - D.c k (f.depth h) i 0 - t * D.c k (f.depth h) i 1| ≤
      D.K k * f.ql h ∧
    |(D.x k l t) 2 - D.c k (f.depth h) i 2 - t * D.c k (f.depth h) i 3 -
      D.c k (f.depth h) i 4 * (D.x k l t) 1| ≤
      D.K k * f.ql h * D.N k ^ (-D.ℓ * f.depth h) ∧
    |D.b k l 4 - D.c k (f.depth h) i 3 - D.c k (f.depth h) i 4 * D.b k l 3| ≤
      D.K k * D.N k ^ (-D.ℓ * f.depth h)
  joint : ∀ h ≤ f.m, ∀ (i : Fin (f.nl h)) (v : ℝ) (v₀ : ℤ), Rk⁻¹ ≤ v → v ≤ Rk →
    D.μ k {p | p.1 ∈ D.B k (f.depth h) i ∧ p.2 ∈ f.block h i ∧
      ⌊D.b k p.1 3 / (D.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (D.K k * f.ql h) * D.ν k (D.A k (f.depth h) i) *
        D.π k {w : ℝ | ⌊w / (D.N k ^ (-v))⌋ = v₀}
  centered : ∀ h ≤ f.m, ∀ i : Fin (f.nl h),
    |D.c k (f.depth h) i 3 + D.c k (f.depth h) i 0 + f.mid h i * D.c k (f.depth h) i 1| +
      |D.c k (f.depth h) i 4 - f.mid h i| ≤ K₂ * f.ql h
  bmeas : Measurable (D.b k)
  νprob : IsProbabilityMeasure (D.ν k)
  dom : D.μ k ≤ ENNReal.ofReal (D.K k) • (D.ν k).prod volume
  anc_sub : ∀ h < f.m, ∀ i : Fin (f.nl (h + 1)),
    D.A k (f.depth (h + 1)) i ⊆ D.A k (f.depth h) (f.anc h i) ∧
      f.block (h + 1) i ⊆ f.block h (f.anc h i)
  core_meas : MeasurableSet f.core
  core_nonempty : f.core.Nonempty
  core_parent_event : f.core ⊆ f.event 0 f.i₀ f.u₀
  core_cover : ∀ p ∈ f.core, ∀ h ≤ f.m, ∃ i u, p ∈ f.event h i u
  core_inside : ∀ h ≤ f.m, ∀ i u, (f.event h i u ∩ f.core).Nonempty →
    f.block h i ⊆ f.block 0 f.i₀ ∧ f.hist h i u ⊆ f.parentSet
  core_floor : ∀ h ≤ f.m, ∀ i u, (f.event h i u ∩ f.core).Nonempty →
    ENNReal.ofReal (θ * f.ql h) * D.ν k (D.A k (f.depth h) i) ≤
      D.μ k (f.event h i u ∩ f.core)
  contact : ∀ p ∈ f.core, |D.b k p.1 4 + D.b k p.1 0| / f.q₀ ≤ D.N k ^ (-e₀')

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
