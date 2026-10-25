-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.FinalPackaging.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Extensions
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Compact
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.CoveringStability

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Final packaging**: a family at scale `δ` with a `1/3`-Lipschitz plane map on its union and a
`1`-Lipschitz slope on `[-1,1]`, together with the slice and local coverings, yields the body of
`Grains σ` at `δ` (compact shadings, globally `1`-Lipschitz slope and plane map). -/
theorem grains_body_of_normalized {σ η η' δ : ℝ} (hδ : 0 < δ) (hη' : δ ^ η ≤ δ ^ η' / 2)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : Family η' δ n x v Y) (hS : Separated η δ n x v)
    (hvol : volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)))
    {f : ℝ → ℝ} (hf : LipschitzOnWith 1 f (Icc (-1 : ℝ) 1))
    (hslice : ∀ z : ℝ, z ∈ Icc (-1) 1 → Covering δ (1 - σ) (δ ^ (-η)) (projectedSlice f (⋃ i, Y i) z))
    {V : Space → Space} (hVL : LipschitzOnWith (1 / 3) V (⋃ i, Y i))
    (hVu : ∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) (hVp : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ)
    (hloc : ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p ∈ ⋃ i, Y i,
      Covering ρ (1 - σ) (δ ^ (-η)) ((fun q => inner ℝ (V p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ)))) :
    ∃ (Y' : Fin n → Set Space),
      Family η δ n x v Y' ∧ Separated η δ n x v ∧ (∀ i, IsCompact (Y' i)) ∧
      volume (⋃ i, Y' i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
      ∃ (g : ℝ → ℝ) (P : Space → Space), LipschitzWith 1 g ∧
        (∀ z : ℝ, z ∈ Icc (-1) 1 → Covering δ (1 - σ) (δ ^ (-η)) (projectedSlice g (⋃ i, Y' i) z)) ∧
        LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y' i) → ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Y' i → |inner ℝ (v i) (P p)| ≤ δ) ∧
        (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y' i) →
          Covering ρ (1 - σ) (δ ^ (-η))
            ((fun q : Space => inner ℝ (P p) q) '' ((⋃ i, Y' i) ∩ ball p (Real.sqrt ρ)))) := by
  obtain ⟨Z, hZY, hZc, hFZ⟩ := hF.compact_refinement hη'
  have hsub : (⋃ i, Z i) ⊆ ⋃ i, Y i := iUnion_mono hZY
  have hball : (⋃ i, Z i) ⊆ ball (0 : Space) 1 := hFZ.union_subset_ball
  obtain ⟨g, hg, hgeq⟩ := extend_slope hball hf
  obtain ⟨P, hP, hPeq⟩ := extend_plane_map (hVL.mono hsub)
  refine ⟨Z, hFZ, hS, hZc, (measure_mono hsub).trans hvol, g, P, hg, ?_, hP, ?_, ?_, ?_⟩
  · intro z hz
    rw [← hgeq z]
    exact (hslice z hz).mono (projectedSlice_mono hsub z)
  · intro p hp; rw [← hPeq hp]; exact hVu p (hsub hp)
  · intro i p hp
    rw [← hPeq (mem_iUnion.2 ⟨i, hp⟩)]
    exact hVp i p (hZY i hp)
  · intro ρ hρ hρ1 p hp
    rw [← hPeq hp]
    refine (hloc ρ hρ hρ1 p (hsub hp)).mono ?_
    exact image_mono (inter_subset_inter_left _ hsub)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
