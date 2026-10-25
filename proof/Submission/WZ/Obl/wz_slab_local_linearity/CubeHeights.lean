-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CubeHeights.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.HeightCells

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set

abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- The precise half-open grid cube used by the frozen statement. -/
def gridCube (ρ : ℝ) (k : Fin 3 → ℤ) : Set Space3 :=
  {p | ∀ i : Fin 3, ρ * (k i : ℝ) ≤ p i ∧ p i < ρ * ((k i : ℝ) + 1)}

def gridCubes (ρ : ℝ) (K : Finset (Fin 3 → ℤ)) : Set Space3 := ⋃ k ∈ K, gridCube ρ k

def gridCorner (ρ : ℝ) (k : Fin 3 → ℤ) : Space3 := WithLp.toLp 2 (fun i => ρ * (k i : ℝ))

lemma gridCorner_mem {ρ : ℝ} (hρ : 0 < ρ) (k : Fin 3 → ℤ) :
    gridCorner ρ k ∈ gridCube ρ k := by
  intro i
  change ρ * (k i : ℝ) ≤ ρ * (k i : ℝ) ∧ ρ * (k i : ℝ) < ρ * ((k i : ℝ) + 1)
  constructor
  · exact le_rfl
  · nlinarith

lemma gridCubes_corner_mem {ρ : ℝ} {K : Finset (Fin 3 → ℤ)} (hρ : 0 < ρ)
    {k : Fin 3 → ℤ} (hk : k ∈ K) : gridCorner ρ k ∈ gridCubes ρ K :=
  mem_iUnion₂.mpr ⟨k, hk, gridCorner_mem hρ k⟩

/-- Each occupied three-dimensional cube supplies its entire half-open height
cell, including its lower endpoint. -/
lemma grid_heightCells_subset {ρ : ℝ} (hρ : 0 < ρ)
    {K : Finset (Fin 3 → ℤ)} {Z : Set ℝ}
    (hZ : ∀ p ∈ gridCubes ρ K, p 2 ∈ Z) :
    heightCells ρ (K.image fun k => k 2) ⊆ Z := by
  rintro z hz
  obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hz
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  let p : Space3 := !₂[ρ * (k 0 : ℝ), ρ * (k 1 : ℝ), z]
  have hp : p ∈ gridCube ρ k := by
    intro i
    fin_cases i
    · change ρ * (k 0 : ℝ) ≤ ρ * (k 0 : ℝ) ∧ ρ * (k 0 : ℝ) < ρ * ((k 0 : ℝ) + 1)
      exact ⟨le_rfl, by nlinarith⟩
    · change ρ * (k 1 : ℝ) ≤ ρ * (k 1 : ℝ) ∧ ρ * (k 1 : ℝ) < ρ * ((k 1 : ℝ) + 1)
      exact ⟨le_rfl, by nlinarith⟩
    · exact hzj
  simpa [p] using hZ p (mem_iUnion₂.mpr ⟨k, hk, hp⟩)

lemma heightCells_mono (ρ : ℝ) {K J : Finset ℤ} (hKJ : K ⊆ J) :
    heightCells ρ K ⊆ heightCells ρ J := by
  rintro z hz
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
  exact mem_iUnion₂.mpr ⟨k, hKJ hk, hzk⟩

end WangZahlLot.Obl.wz_slab_local_linearity
