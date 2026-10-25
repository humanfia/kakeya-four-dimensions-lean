-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedBootstrap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedOneScale
import Submission.WZ.Obl.wz_broad_grains_improvement.StickyGain

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound doubled)
open WangZahlLot.Obl.wz_multiscale_finite_tower (Factorization KatzTao Frostman)

set_option maxHeartbeats 1200000

/-- Align the two accepted formulations of the coarse factorization interface. -/
theorem aligned_alternative_of_one_scale {σ ω : ℝ} (hP : AlignedOneScale σ ω) :
    AlignedAlternative σ ω := by
  intro ζ hζ
  obtain ⟨α, hα, κ, hκ, η, hη, HP⟩ := hP ζ hζ
  refine ⟨α, κ, η, 1 / 100, hα, hκ, hη, by norm_num, ?_⟩
  intro d hd hd100 n x v Y hA haxes
  have hA' : A d η (d ^ (-η)) (d ^ (-η)) n x v Y := by
    simpa only [A, K, WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Admissible,
      ConvexCount, true_and] using hA
  rcases HP d hd hd100 n x v Y hA' haxes with hGain | hCover
  · exact Or.inl hGain
  · right
    simpa only [Factorization, WangZahlLot.Obl.wz_rescaled_fibre_alternatives.GlobalCover,
      KatzTao, Frostman, ConvexCount, SlabBound, doubled, true_and, and_assoc] using hCover

/-- The aligned one-scale theorem suffices for a gain on arbitrary original families. -/
theorem uniform_gain_of_aligned_one_scale {σ ω : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hFrostman : FrostmanAllScales) (hP : AlignedOneScale σ ω) :
    UniformGain σ ω := by
  apply uniform_gain_of_every_scale hσ.le hσ1 hω hFrostman
  exact every_scale_alternative_of_physical hE
    (physical_step_of_aligned hσ.le hω hω1 (aligned_alternative_of_one_scale hP))
    hσ hσ1 hω hω1

/-- The complete original-family improvement, with only the two analytic inputs explicit. -/
theorem improvement_of_aligned_one_scale {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hFrostman : FrostmanAllScales) (hP : AlignedOneScale σ ω)
    (hε : 0 < ε) : L σ ω ζ ε :=
  improvement_of_uniform_gain hε
    (uniform_gain_of_aligned_one_scale hσ hσ1 hω hω1 hE hFrostman hP)

/-- A fixed-length per-incidence prism endpoint closes the original-family gain route. -/
theorem improvement_of_frostman_and_prisms {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hR : R σ ω) (hFrostman : FrostmanAllScales)
    (hPrism : ∀ ζ : ℝ, 0 < ζ → ζ ≤ ω / 1000 → PrismImprovement σ ω ζ)
    (hε : 0 < ε) : L σ ω ζ ε :=
  improvement_of_aligned_one_scale hσ hσ1 hω hω1 hE hFrostman
    (aligned_one_scale_of_prisms hσ hσ1 hω hω1 hE hR hPrism) hε

end WangZahlLot.Obl.wz_broad_grains_improvement
