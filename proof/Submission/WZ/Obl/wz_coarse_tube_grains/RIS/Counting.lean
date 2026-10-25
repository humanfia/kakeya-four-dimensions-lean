-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Multiplicity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Multiplicity within a fiber of an assigned cover. -/
noncomputable def fiberMultiplicity {n k : ℕ} (f : Fin n → Fin k)
    (Y : Fin n → Set Space) (j : Fin k) (p : Space) : ENNReal :=
  ∑ i ∈ Finset.univ.filter (fun i => f i = j), (Y i).indicator (fun _ => 1) p

/-- Summing over fibers counts every shading once. -/
theorem sum_fiberMultiplicity {n k : ℕ} (f : Fin n → Fin k)
    (Y : Fin n → Set Space) (p : Space) :
    ∑ j, fiberMultiplicity f Y j p = multiplicity Y p := by
  classical
  exact Finset.sum_fiberwise Finset.univ f (fun i => (Y i).indicator (fun _ => 1) p)

/-- A uniform fine multiplicity bound multiplies the multiplicity of the covering family. -/
theorem multiplicity_le_mul_of_fiber_bound {n k : ℕ} (f : Fin n → Fin k)
    {Y : Fin n → Set Space} {Z : Fin k → Set Space}
    (hcover : ∀ i, Y i ⊆ Z (f i)) {M : ENNReal} {p : Space}
    (hlocal : ∀ j, fiberMultiplicity f Y j p ≤ M) :
    multiplicity Y p ≤ M * multiplicity Z p := by
  classical
  calc
    multiplicity Y p = ∑ j, fiberMultiplicity f Y j p := (sum_fiberMultiplicity f Y p).symm
    _ ≤ ∑ j, M * (Z j).indicator (fun _ => 1) p := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hp : p ∈ Z j
      · simpa only [Set.indicator_of_mem hp, mul_one] using hlocal j
      · have hfiber : fiberMultiplicity f Y j p = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hij : f i = j := (Finset.mem_filter.mp hi).2
          apply Set.indicator_of_notMem
          intro hpi
          exact hp (hij ▸ hcover i hpi)
        simp [hfiber, Set.indicator_of_notMem hp]
    _ = M * multiplicity Z p := (Finset.mul_sum _ _ _).symm

/-- The compatible fine/intermediate/coarse decomposition gives a product bound.
The geometric work is exactly the two covers and their local multiplicity estimates. -/
theorem three_level_multiplicity {n k l : ℕ} (f : Fin n → Fin k) (g : Fin k → Fin l)
    {Y : Fin n → Set Space} {Z : Fin k → Set Space} {W : Fin l → Set Space}
    (hYZ : ∀ i, Y i ⊆ Z (f i)) (hZW : ∀ j, Z j ⊆ W (g j))
    {A B C : ENNReal} {p : Space}
    (hfine : ∀ j, fiberMultiplicity f Y j p ≤ A)
    (hmedium : ∀ j, fiberMultiplicity g Z j p ≤ B)
    (hcoarse : multiplicity W p ≤ C) :
    multiplicity Y p ≤ A * B * C := by
  calc
    multiplicity Y p ≤ A * multiplicity Z p := multiplicity_le_mul_of_fiber_bound f hYZ hfine
    _ ≤ A * (B * multiplicity W p) :=
      mul_le_mul_right (multiplicity_le_mul_of_fiber_bound g hZW hmedium) _
    _ ≤ A * (B * C) := mul_le_mul_right (mul_le_mul_right hcoarse _) _
    _ = _ := (mul_assoc _ _ _).symm

/-- A tube may contribute to several grains. Covering each shading by pieces
supports the same multiplicity estimate without assigning it to one grain. -/
theorem multiplicity_le_mul_of_piece_cover {n k : ℕ}
    {Y : Fin n → Set Space} {Z : Fin k → Set Space}
    (P : Fin n → Fin k → Set Space)
    (hcover : ∀ i, Y i ⊆ ⋃ j, P i j) (hsupport : ∀ i j, P i j ⊆ Z j)
    {M : ENNReal} {p : Space}
    (hlocal : ∀ j, multiplicity (fun i => P i j) p ≤ M) :
    multiplicity Y p ≤ M * multiplicity Z p := by
  classical
  calc
    multiplicity Y p ≤ ∑ i, ∑ j, (P i j).indicator (fun _ => (1 : ENNReal)) p := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hp : p ∈ Y i
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover i hp)
        rw [Set.indicator_of_mem hp]
        calc
          1 = (P i j).indicator (fun _ => (1 : ENNReal)) p :=
            (Set.indicator_of_mem hj (fun _ : Space => (1 : ENNReal))).symm
          _ ≤ _ := Finset.single_le_sum
            (f := fun j : Fin k => (P i j).indicator (fun _ => (1 : ENNReal)) p)
            (fun _ _ => bot_le) (Finset.mem_univ j)
      · simp [Set.indicator_of_notMem hp]
    _ = ∑ j, multiplicity (fun i => P i j) p := Finset.sum_comm
    _ ≤ ∑ j, M * (Z j).indicator (fun _ => 1) p := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hp : p ∈ Z j
      · simpa only [Set.indicator_of_mem hp, mul_one] using hlocal j
      · have hpieces : multiplicity (fun i => P i j) p = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact Set.indicator_of_notMem (fun hi => hp (hsupport i j hi)) _
        simp [hpieces, Set.indicator_of_notMem hp]
    _ = M * multiplicity Z p := (Finset.mul_sum _ _ _).symm

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
