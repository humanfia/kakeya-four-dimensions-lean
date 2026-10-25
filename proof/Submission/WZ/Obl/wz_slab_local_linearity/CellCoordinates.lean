-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellCoordinates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CubeHeights
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityAlign

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set

/-- Change the lattice indexing convention and translate the vertical index. -/
def shiftIndex (k₀ : ℤ) : (Fin 3 → ℤ) ≃ (ℤ × ℤ × ℤ) where
  toFun k := (k 0, k 1, k 2 - k₀)
  invFun q := ![q.1, q.2.1, q.2.2 + k₀]
  left_inv k := by funext i; fin_cases i <;> simp
  right_inv q := by rcases q with ⟨i, j, k⟩; simp

@[simp] lemma shiftIndex_apply (k₀ : ℤ) (k : Fin 3 → ℤ) :
    shiftIndex k₀ k = (k 0, k 1, k 2 - k₀) := rfl

@[simp] lemma shiftIndex_symm_apply (k₀ : ℤ) (q : ℤ × ℤ × ℤ) :
    (shiftIndex k₀).symm q = ![q.1, q.2.1, q.2.2 + k₀] := rfl

def shiftCells (k₀ : ℤ) (K : Finset (Fin 3 → ℤ)) : Finset (ℤ × ℤ × ℤ) :=
  K.map (shiftIndex k₀).toEmbedding

@[simp] lemma card_shiftCells (k₀ : ℤ) (K : Finset (Fin 3 → ℤ)) :
    (shiftCells k₀ K).card = K.card := Finset.card_map _

lemma mem_shiftCells_iff {k₀ : ℤ} {K : Finset (Fin 3 → ℤ)} {q : ℤ × ℤ × ℤ} :
    q ∈ shiftCells k₀ K ↔ (shiftIndex k₀).symm q ∈ K := by
  simp [shiftCells]

noncomputable def heightShift (ρ : ℝ) (k₀ : ℤ) : Space3 := !₂[0, 0, ρ * (k₀ : ℝ)]

lemma cellPos_add_heightShift (ρ : ℝ) (k₀ : ℤ) (q : ℤ × ℤ × ℤ) :
    CellProofs.cellPos ρ q + heightShift ρ k₀ = gridCorner ρ ((shiftIndex k₀).symm q) := by
  ext i
  fin_cases i <;> simp [CellProofs.cellPos, heightShift, gridCorner] <;> ring

lemma cellPos_shiftIndex (ρ : ℝ) (k₀ : ℤ) (k : Fin 3 → ℤ) :
    CellProofs.cellPos ρ (shiftIndex k₀ k) + heightShift ρ k₀ = gridCorner ρ k := by
  simpa only [Equiv.symm_apply_apply] using cellPos_add_heightShift ρ k₀ (shiftIndex k₀ k)

lemma shifted_corner_mem {ρ : ℝ} (hρ : 0 < ρ) {k₀ : ℤ} {K : Finset (Fin 3 → ℤ)}
    {q : ℤ × ℤ × ℤ} (hq : q ∈ shiftCells k₀ K) :
    CellProofs.cellPos ρ q + heightShift ρ k₀ ∈ gridCubes ρ K := by
  rw [cellPos_add_heightShift]
  exact gridCubes_corner_mem hρ (mem_shiftCells_iff.mp hq)

lemma shiftCells_height_image {k₀ : ℤ} {K : Finset (Fin 3 → ℤ)} {S : Finset ℤ}
    (hS : S ⊆ (shiftCells k₀ K).image (fun q => q.2.2)) :
    S.image (fun k => k + k₀) ⊆ K.image (fun k => k 2) := by
  classical
  intro k hk
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (hS hj)
  refine Finset.mem_image.mpr ⟨(shiftIndex k₀).symm q, mem_shiftCells_iff.mp hq, ?_⟩
  simp

lemma shifted_height_card (k₀ : ℤ) (S : Finset ℤ) :
    (S.image (fun k => k + k₀)).card = S.card := by
  classical
  apply Finset.card_image_of_injective
  intro k l hkl
  exact add_right_cancel hkl

end WangZahlLot.Obl.wz_slab_local_linearity
