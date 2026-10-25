-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ConcentratedBodies.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.VolumeWidth

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (frozen_prism_volume frozen_prism_compact frozen_prism_convex wideSection_of_volume)
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyGeometry)

noncomputable section

namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

/-- Any selected natural subfamily is a family of normalized convex bodies
with common volume rho squared over 64 and uniformly positive shading density. -/
theorem normalized_bodies_exact (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {k : ℕ} (ι : Fin k → Fin D.L) (j₀ : Fin D.L)
    (hι : ∀ j, ι j ∈ D.Q)
    (hnear : ∀ j, grainNear D.a ρ c D.z D.e j₀ (ι j)) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W) ∧
      BodyGeometry (fun j => f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
        (fun j => f (D.z (ι j))) (δ / 8) (ρ / 128) (ρ ^ 2 / 64) ∧
      (∀ j, MeasurableSet (f '' D.Hg (ι j))) ∧
      (∀ j, f '' D.Hg (ι j) ⊆ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, O (δ ^ (21 * ε / 40)) *
        μ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ≤ μ (f '' D.Hg (ι j))) ∧
      (∀ j, ball (f (D.z (ι j))) (ρ / 100) ⊆
        f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, ∃ p ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)),
        ∃ q ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)), (1 / 4 : ℝ) ≤ dist p q) ∧
      (∀ p q, dist (f p) (f q) ≤ (ρ / (4 * D.a)) * dist p q) ∧
      (∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) ∧
      (∀ q i, f q i = (![ρ / (4 * D.a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i *
        D.e j₀ (q - D.z j₀) i) ∧
      (∀ j, f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)) ⊆ ball (0 : V) 1) := by
  obtain ⟨ha, hρ, hρ1, hc, hc1⟩ := D.dimensions hδ
  obtain ⟨f, hvol, hball, hint, hdiam, hdist, hround, hLip, hcoord⟩ := natural_grain_normalization_exact
    ha hρ hρ1 hc D.grains.2.1 (D.z ∘ ι) (D.e ∘ ι) (D.z j₀) (D.e j₀) hnear
  have hrc : ρ * c ≤ c := D.grains.2.2.1
  have hcompact j : IsCompact (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) :=
    (frozen_prism_compact ha.le D.grains.2.1 hrc _ _).image
      f.toContinuousAffineEquiv.continuous
  have hconvex j : Convex ℝ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) :=
    (frozen_prism_convex _ _ _ _ _).affine_image f.toAffineMap
  have hvol' j : μ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) = O (ρ ^ 2 / 64) := by
    have hv : μ (P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) = O (D.a * (ρ * c) * c) :=
      frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le _ _
    rw [hvol, hv,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ ρ / (64 * D.a * c ^ 2))]
    congr 1
    field_simp
    <;> ring
  have hbound j : f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)) ⊆ closedBall (0 : V) 1 :=
    (hball j).trans ball_subset_closedBall
  have hwide j := wideSection_of_volume (hcompact j) (hconvex j)
    (by positivity : 0 < D.a / (8 * c)) (hint j) (hbound j)
    (by positivity : 0 < ρ ^ 2 / 64) (hvol' j).ge
  have hsqrt : Real.sqrt (ρ ^ 2 / 64) / 16 = ρ / 128 := by
    rw [Real.sqrt_div (sq_nonneg ρ), Real.sqrt_sq hρ.le]
    norm_num
    ring
  have hδa : δ / 8 ≤ D.a / (8 * c) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) (by positivity : 0 < 8 * c)]
    nlinarith [D.grains.1]
  refine ⟨f, hvol, ⟨hcompact, hconvex, hbound, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hround, hdiam, hLip, hdist, hcoord, hball⟩
  · intro j
    exact (ball_subset_ball hδa).trans (hint j)
  · intro j
    obtain ⟨u, hu, v, hv, hd⟩ := hdiam j
    exact ⟨u, hu, v, hv, (by norm_num : (1 / 16 : ℝ) ≤ 1 / 4).trans hd⟩
  · intro j
    simpa only [hsqrt] using hwide j
  · intro j
    change O (ρ ^ 2 / 64) ≤ μ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      μ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ≤ O (384 * (ρ ^ 2 / 64))
    rw [hvol' j]
    exact ⟨le_rfl, ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg ρ])⟩
  · intro j
    exact f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (D.grains.2.2.2.2.1 (ι j)).1
  · intro j
    exact image_mono (D.grains.2.2.2.2.1 (ι j)).2.1
  · intro j
    rw [hvol, hvol]
    calc
      _ = O (ρ / (64 * D.a * c ^ 2)) *
          (O (δ ^ (21 * ε / 40)) * μ (P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))) := by ring
      _ ≤ _ := mul_le_mul' le_rfl (D.selected_density hδ (ι j) (hι j))

/-- The metric body interface, forgetting the exact natural coordinates. -/
theorem normalized_bodies_controlled (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {k : ℕ} (ι : Fin k → Fin D.L) (j₀ : Fin D.L)
    (hι : ∀ j, ι j ∈ D.Q)
    (hnear : ∀ j, grainNear D.a ρ c D.z D.e j₀ (ι j)) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W) ∧
      BodyGeometry (fun j => f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
        (fun j => f (D.z (ι j))) (δ / 8) (ρ / 128) (ρ ^ 2 / 64) ∧
      (∀ j, MeasurableSet (f '' D.Hg (ι j))) ∧
      (∀ j, f '' D.Hg (ι j) ⊆ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, O (δ ^ (21 * ε / 40)) *
        μ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ≤ μ (f '' D.Hg (ι j))) ∧
      (∀ j, ball (f (D.z (ι j))) (ρ / 100) ⊆
        f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, ∃ p ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)),
        ∃ q ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)), (1 / 4 : ℝ) ≤ dist p q) ∧
      (∀ p q, dist (f p) (f q) ≤ (ρ / (4 * D.a)) * dist p q) := by
  obtain ⟨f, hv, hg, hm, hs, hd, hr, hl, hLip, _, _, _⟩ :=
    D.normalized_bodies_exact hδ ι j₀ hι hnear
  exact ⟨f, hv, hg, hm, hs, hd, hr, hl, hLip⟩

/-- The round body interface with the forward metric control omitted. -/
theorem normalized_bodies_round (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {k : ℕ} (ι : Fin k → Fin D.L) (j₀ : Fin D.L)
    (hι : ∀ j, ι j ∈ D.Q)
    (hnear : ∀ j, grainNear D.a ρ c D.z D.e j₀ (ι j)) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W) ∧
      BodyGeometry (fun j => f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
        (fun j => f (D.z (ι j))) (δ / 8) (ρ / 128) (ρ ^ 2 / 64) ∧
      (∀ j, MeasurableSet (f '' D.Hg (ι j))) ∧
      (∀ j, f '' D.Hg (ι j) ⊆ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, O (δ ^ (21 * ε / 40)) *
        μ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ≤ μ (f '' D.Hg (ι j))) ∧
      (∀ j, ball (f (D.z (ι j))) (ρ / 100) ⊆
        f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, ∃ p ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)),
        ∃ q ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)), (1 / 4 : ℝ) ≤ dist p q) := by
  obtain ⟨f, hv, hg, hm, hs, hd, hr, hl, -⟩ := D.normalized_bodies_controlled hδ ι j₀ hι hnear
  exact ⟨f, hv, hg, hm, hs, hd, hr, hl⟩

/-- The body-geometry interface without the extra roundness conclusions. -/
theorem normalized_bodies (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {k : ℕ} (ι : Fin k → Fin D.L) (j₀ : Fin D.L)
    (hι : ∀ j, ι j ∈ D.Q)
    (hnear : ∀ j, grainNear D.a ρ c D.z D.e j₀ (ι j)) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W) ∧
      BodyGeometry (fun j => f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
        (fun j => f (D.z (ι j))) (δ / 8) (ρ / 128) (ρ ^ 2 / 64) ∧
      (∀ j, MeasurableSet (f '' D.Hg (ι j))) ∧
      (∀ j, f '' D.Hg (ι j) ⊆ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, O (δ ^ (21 * ε / 40)) *
        μ (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ≤ μ (f '' D.Hg (ι j))) := by
  obtain ⟨f, hvol, hgeom, hm, hs, hd, -, -⟩ := D.normalized_bodies_round hδ ι j₀ hι hnear
  exact ⟨f, hvol, hgeom, hm, hs, hd⟩

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
