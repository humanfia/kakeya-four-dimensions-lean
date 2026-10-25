-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.SlabHyp.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CubeHeights
import Submission.WZ.Obl.wz_slab_local_linearity.Covering

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set MeasureTheory

/-- The hypotheses of the frozen slab theorem, before choosing its small-scale
parameters. -/
structure SlabHyp (ρ σ η z₀ c₀ : ℝ) (Z : Set ℝ) (f : ℝ → ℝ)
    (K : Finset (Fin 3 → ℤ)) (V : Space3 → Space3) : Prop where
  heights : Z ⊆ Icc z₀ (z₀ + Real.sqrt ρ)
  f_lip : ∀ z ∈ Icc z₀ (z₀ + Real.sqrt ρ), ∀ z' ∈ Icc z₀ (z₀ + Real.sqrt ρ),
    |f z - f z'| ≤ |z - z'|
  f_bound : ∀ z ∈ Icc z₀ (z₀ + Real.sqrt ρ), |f z| ≤ 4
  region : ∀ p ∈ gridCubes ρ K, |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ p 2 ∈ Z ∧
    |p 0 + f z₀ * p 1 - c₀| ≤ Real.sqrt ρ
  mass : ENNReal.ofReal (ρ ^ (1 + σ / 2 + η)) ≤ volume (gridCubes ρ K)
  normals : ∀ p ∈ gridCubes ρ K, ‖V p‖ = 1 ∧ ρ ^ (2 * η) ≤ (V p 0) ^ 2 + (V p 1) ^ 2
  normal_lip : ∀ p ∈ gridCubes ρ K, ∀ q ∈ gridCubes ρ K, dist (V p) (V q) ≤ dist p q
  global_AD : ∀ z ∈ Z, IntervalAD ρ (1 - σ) (ρ ^ (-η))
    {u : ℝ | ∃ p ∈ gridCubes ρ K, p 2 = z ∧ u = p 0 + f z * p 1}
  local_volume : ∀ p ∈ gridCubes ρ K,
    volume ((fun q : Space3 => inner ℝ (V p) q) '' (gridCubes ρ K ∩ Metric.ball p (Real.sqrt ρ))) ≤
      ENNReal.ofReal (ρ ^ ((1 + σ) / 2 - η))

end WangZahlLot.Obl.wz_slab_local_linearity
