-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeNarrowTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeNarrowTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeNarrowTransfer.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeNarrowTransfer.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeNarrowTransfer.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.CoarsePacketWitness
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPaletteTransfer

/-! A fine normalized-palette strip concentration becomes a heavy strip
under the fixed native parent posterior used by the strip packing theorem. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped BigOperators RealInnerProductSpace

section Certificate

variable {T E : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

/-- This supplies the raw-strip heaviness premise of the concrete width exit.
The same `Q.velocityPosterior` supplies the already checked packing ball cap. -/
theorem PreparedAngularPath.coarse_strip_floor (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (b : Fin p.C) (c : ℕ)
    (hPacket : ∀ z ∈ Q.coarseSupport (p.lev b) c, z.1 = p.γ b ∧ z.2 ∈ p.F b)
    (hCpos : Q.law (Q.coarseSupport (p.lev b) c) ≠ 0)
    (hmap : (Q.coarseLaw (p.lev b) c).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ)
    (G : Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (hGC : G ⊆ Q.coarseSupport (p.lev b) c)
    (f : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) → E)
    {a : ℝ} (ha : 0 < a) (A θ : ℝ) (hA : 0 < A) (e : E)
    (he : 0 < (Q.coarseLaw (p.lev b) c).real {z | f z = e})
    (hcap : ∀ a', (Q.coarseLaw (p.lev b) c).real
      {z | z ∈ G ∧ f z = e ∧ p.labelledNormalizedPalette b a z = a'} ≤
        A * (Q.coarseLaw (p.lev b) c).real {z | f z = e} *
          (Q.coarseLaw (p.lev b) c).real {z | p.labelledNormalizedPalette b a z = a'})
    (n : StripSpace) (β r : ℝ) (hn : ‖n‖ = 1)
    (hstrip : θ * (Q.coarseLaw (p.lev b) c).real {z | f z = e} ≤
      (Q.coarseLaw (p.lev b) c).real
        {z | z ∈ G ∧ f z = e ∧ p.normalizedVelocity b z.2 ∈ affineStrip n β r}) :
    θ / A ≤ (Q.velocityPosterior b).real (boundedStrip n β (r + 2 * a) (2 * p.κ)) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  let := Q.probability hd hHE hκ
  let : IsProbabilityMeasure (Q.coarseLaw (p.lev b) c) :=
    ProbabilityTheory.cond_isProbabilityMeasure (μ := Q.law) hCpos
  let C := Q.coarseSupport (p.lev b) c
  let V : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) → StripSpace :=
    fun z => p.normalizedVelocity b z.2
  have hV : Measurable V := (p.measurable_normalizedVelocity b).comp measurable_snd
  have hF (a' : Fin p.C) : MeasurableSet (p.F a') :=
    (hp.2.2.2.2.2.2.2 a').2.2.2.2.2.2.2.2.2.1
  have hC : MeasurableSet C :=
    (measurableSet_labelledSupport Q.residual Q.residual_measurable).inter
      (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF _) measurable_const)
  have hμC : Q.coarseLaw (p.lev b) c Cᶜ = 0 :=
    ae_iff.mp (ProbabilityTheory.ae_cond_mem (μ := Q.law) hC)
  have hNorm (z) (hz : z ∈ C) : ‖V z‖ ≤ 2 * p.κ := by
    have hFb := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.2.2.2.1 z.2 (hPacket z hz).2
    exact hp.normalized_velocity_bound b z.2.1 hFb.2.1
  have hCoord : ∀ z ∈ C, ∀ j, |V z j| ≤ 2 * p.κ := by
    intro z hz j
    have hh : |V z j| ≤ ‖V z‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (V z) j
    exact hh.trans (hNorm z hz)
  obtain ⟨_, _, hfin, _, _⟩ := velocityPalette_card C (nonempty_of_measure_ne_zero hCpos)
    (fun z j => V z j) (by positivity) ha hCoord
  have hFloor := coarse_strip_floor_of_palette_joint_cap (Q.coarseLaw (p.lev b) c) C G hμC hGC
    f V ha (measurable_euclidean_velocityPalette V hV a) hfin (2 * p.κ) hNorm A θ hA e he hcap
    n β r hn hstrip
  calc
    _ ≤ (Q.coarseLaw (p.lev b) c).real {z | V z ∈ boundedStrip n β (r + 2 * a) (2 * p.κ)} := hFloor
    _ = ((Q.coarseLaw (p.lev b) c).map (fun z => p.normalizedVelocity b z.2)).real
        (boundedStrip n β (r + 2 * a) (2 * p.κ)) := by
      change ((Q.coarseLaw (p.lev b) c) {z | V z ∈ boundedStrip n β (r + 2 * a) (2 * p.κ)}).toReal =
        (((Q.coarseLaw (p.lev b) c).map V) (boundedStrip n β (r + 2 * a) (2 * p.κ))).toReal
      rw [Measure.map_apply hV (measurableSet_boundedStrip _ _ _ _)]
      rfl
    _ = _ := congrArg (fun μ : Measure StripSpace => μ.real (boundedStrip n β (r + 2 * a) (2 * p.κ)))
      (Q.coarse_velocity_posterior_eq b c hmap)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
