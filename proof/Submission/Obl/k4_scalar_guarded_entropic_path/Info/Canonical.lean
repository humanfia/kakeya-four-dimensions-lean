import Submission.Obl.k4_scalar_guarded_entropic_path.Info.FiniteCode

/-!
# The canonical finite code of a window

An explicit version of `exists_finite_code`: the atom of an incidence is its grid state
(all base and hidden bins at the tangent resolutions `j / m`, `j ≤ m²`, and the velocity bin
at resolution `m`), read in a fixed finite box. `canonY` records the base/hidden part,
`canonZ` the velocity bin, and `canonQ`, `canonC` decode the bins from `canonY`. Every
window of a stage uses the same code, since all window parents share the resolution `N`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The base/hidden part of a grid state. -/
abbrev GridPart (m : ℕ) : Type := (Fin (m ^ 2 + 1) → Fin 2 → ℤ) × (Fin (m ^ 2 + 1) → ℤ)

/-- A fixed injective coding of grid parts. -/
def gridEnc (m : ℕ) : GridPart m → ℕ :=
  Classical.choose (Countable.exists_injective_nat (GridPart m))

theorem gridEnc_injective (m : ℕ) : Function.Injective (gridEnc m) :=
  Classical.choose_spec (Countable.exists_injective_nat (GridPart m))

/-- Its decoder. -/
def gridDec (m : ℕ) (y : ℕ) : GridPart m := by
  classical
  exact if h : ∃ u, gridEnc m u = y then Classical.choose h else 0

theorem gridDec_gridEnc (m : ℕ) (u : GridPart m) : gridDec m (gridEnc m u) = u := by
  classical
  have h : ∃ u', gridEnc m u' = gridEnc m u := ⟨u, rfl⟩
  simp only [gridDec, h, dif_pos]
  exact gridEnc_injective m (Classical.choose_spec h)

/-- The grid part of an incidence at resolution `N`. -/
def gridPart (N : ℝ) (m : ℕ) (z : Incidence) : GridPart m :=
  ((gridTuple N m z).1, (gridTuple N m z).2.1)

theorem measurable_gridPart (N : ℝ) (m : ℕ) : Measurable (gridPart N m) :=
  (measurable_fst.comp (measurable_gridTuple N m)).prodMk
    (measurable_fst.comp (measurable_snd.comp (measurable_gridTuple N m)))

/-- The finite box of grid states. -/
def boxSet (m : ℕ) (M : ℤ) : Finset (GridTuple m) := (gridBox_finite m M).toFinset

/-- The number of atoms of the canonical code: the box, and one atom for the outside. -/
def canonN (m : ℕ) (M : ℤ) : ℕ := (boxSet m M).card + 1

/-- The atom of a grid state. -/
def boxIndex (m : ℕ) (M : ℤ) (u : GridTuple m) : Fin (canonN m M) := by
  classical
  exact if h : u ∈ boxSet m M then Fin.castSucc ((boxSet m M).equivFin ⟨u, h⟩) else Fin.last _

/-- The canonical code: the box index of the grid state. -/
def canonX (N : ℝ) (m : ℕ) (M : ℤ) (z : Incidence) : Fin (canonN m M) :=
  boxIndex m M (gridTuple N m z)

/-- The grid state of an atom of the canonical code (`0` for the outside atom). -/
def canonState (m : ℕ) (M : ℤ) (i : Fin (canonN m M)) : GridTuple m :=
  if h : (i : ℕ) < (boxSet m M).card then ((boxSet m M).equivFin.symm ⟨i, h⟩).1 else 0

/-- The base/hidden record of an atom. -/
def canonY (m : ℕ) (M : ℤ) (i : Fin (canonN m M)) : ℕ :=
  gridEnc m ((canonState m M i).1, (canonState m M i).2.1)

/-- The velocity record of an atom. -/
def canonZ (m : ℕ) (M : ℤ) (i : Fin (canonN m M)) : ℤ := (canonState m M i).2.2

/-- Decoders of the base and hidden bins. -/
def canonQ (m : ℕ) (j : Fin (m ^ 2 + 1)) (y : ℕ) : Fin 2 → ℤ := (gridDec m y).1 j

def canonC (m : ℕ) (j : Fin (m ^ 2 + 1)) (y : ℕ) : ℤ := (gridDec m y).2 j

theorem canonState_boxIndex {m : ℕ} {M : ℤ} {u : GridTuple m} (hu : u ∈ boxSet m M) :
    canonState m M (boxIndex m M u) = u := by
  classical
  have hb : boxIndex m M u = Fin.castSucc ((boxSet m M).equivFin ⟨u, hu⟩) := by
    unfold boxIndex; simp [hu]; rfl
  rw [hb]
  unfold canonState
  have hlt : ((Fin.castSucc ((boxSet m M).equivFin ⟨u, hu⟩) : Fin ((boxSet m M).card + 1)) : ℕ) <
      (boxSet m M).card := by simp
  rw [dite_eq_left_of_eq_true (eq_true hlt)]
  simp

theorem canonState_canonX {N : ℝ} {m : ℕ} {M : ℤ} {z : Incidence}
    (hz : gridTuple N m z ∈ boxSet m M) : canonState m M (canonX N m M z) = gridTuple N m z :=
  canonState_boxIndex hz

theorem canonY_canonX {N : ℝ} {m : ℕ} {M : ℤ} {z : Incidence}
    (hz : gridTuple N m z ∈ boxSet m M) :
    canonY m M (canonX N m M z) = gridEnc m (gridPart N m z) := by
  rw [canonY, canonState_canonX hz]; rfl

theorem canonZ_canonX {N : ℝ} {m : ℕ} {M : ℤ} {z : Incidence}
    (hz : gridTuple N m z ∈ boxSet m M) :
    canonZ m M (canonX N m M z) = velocityBin N (m : ℝ) (z.1.2 1) := by
  rw [canonZ, canonState_canonX hz]; rfl

theorem measurable_canonX (N : ℝ) (m : ℕ) (M : ℤ) : Measurable (canonX N m M) :=
  (measurable_of_countable (boxIndex m M)).comp (measurable_gridTuple N m)

/-- The box size that contains every bounded incidence. -/
def canonM (N K : ℝ) (m : ℕ) : ℤ := ⌈3 * K * N ^ (m : ℝ)⌉ + 1

theorem gridTuple_mem_boxSet {N K : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    {z : Incidence} (ht : z.2 ∈ Icc (0 : ℝ) 1) (hl : ∀ e, |z.1.2 e| ≤ K) :
    gridTuple N m z ∈ boxSet m (canonM N K m) := by
  rw [boxSet, Set.Finite.mem_toFinset]
  exact gridTuple_mem_gridBox hN hK hm ht hl

/-- **Canonical decoding.** On bounded incidences the canonical code decodes every tested
base and hidden bin and the finest velocity bin. -/
theorem canon_decode {N K : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    {z : Incidence} (ht : z.2 ∈ Icc (0 : ℝ) 1) (hl : ∀ e, |z.1.2 e| ≤ K) :
    canonZ m (canonM N K m) (canonX N m (canonM N K m) z) = velocityBin N (m : ℝ) (z.1.2 1) ∧
      ∀ j : Fin (m ^ 2 + 1),
        baseBin N ((j : ℝ) / (m : ℝ)) z =
          canonQ m j (canonY m (canonM N K m) (canonX N m (canonM N K m) z)) ∧
        hiddenBin N ((j : ℝ) / (m : ℝ)) z =
          canonC m j (canonY m (canonM N K m) (canonX N m (canonM N K m) z)) := by
  have hz := gridTuple_mem_boxSet hN hK hm ht hl
  refine ⟨canonZ_canonX hz, fun j => ⟨?_, ?_⟩⟩
  · rw [canonY_canonX hz, canonQ, gridDec_gridEnc]; rfl
  · rw [canonY_canonX hz, canonC, gridDec_gridEnc]; rfl

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
