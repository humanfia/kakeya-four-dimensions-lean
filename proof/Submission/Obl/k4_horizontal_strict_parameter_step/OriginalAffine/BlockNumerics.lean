/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 89648dfeac59b903d3d93ae0dca8d07a6202ebdf, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/BlockNumerics.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.MeshChoice
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Submission.Obl.k4_horizontal_strict_parameter_step

/-- A fixed time belongs to at most two closed grid intervals, including
all boundary points. -/
lemma closed_grid_blocks_card {H : ℕ} (hH : 0 < H) (S : Finset (Fin H)) (t : ℝ)
    (hS : ∀ j ∈ S, (j : ℝ) / H ≤ t ∧ t ≤ ((j : ℝ) + 1) / H) : S.card ≤ 2 := by
  classical
  have hHp : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  let φ : Fin H → ℤ := fun j => (j : ℕ)
  have hφ : Function.Injective φ := fun j j' hh => Fin.ext (Int.ofNat_inj.mp hh)
  have hsub : S.image φ ⊆ Finset.Icc (⌊t * H⌋ - 1) ⌊t * H⌋ := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hlo : (j : ℝ) ≤ t * H := (div_le_iff₀ hHp).mp (hS j hj).1
    have hhi : t * H ≤ (j : ℝ) + 1 := (le_div_iff₀ hHp).mp (hS j hj).2
    have hflo : (j : ℤ) ≤ ⌊t * H⌋ := by
      apply Int.le_floor.mpr
      simpa only [Int.cast_natCast] using hlo
    have hfhi : ⌊t * H⌋ ≤ (j : ℤ) + 1 := by
      apply (Int.floor_le_floor hhi).trans_eq
      rw [Int.floor_add_one, Int.floor_natCast]
    apply Finset.mem_Icc.mpr
    dsimp [φ]
    constructor <;> omega
  calc
    S.card = (S.image φ).card := (Finset.card_image_of_injective _ hφ).symm
    _ ≤ (Finset.Icc (⌊t * H⌋ - 1) ⌊t * H⌋).card := Finset.card_le_card hsub
    _ = 2 := by rw [Int.card_Icc]; omega

/-- Uniform same-block child counts combine with only a factor two at a
fixed time.  No deletion of endpoint times is required. -/
lemma card_of_closed_block_fibers {ι : Type*} {H : ℕ} (hH : 0 < H)
    (S : Finset ι) (block : ι → Fin H) (t B : ℝ) (hB : 0 ≤ B)
    (ht : ∀ i ∈ S, (block i : ℝ) / H ≤ t ∧ t ≤ ((block i : ℝ) + 1) / H)
    (hcount : ∀ j, ((S.filter (fun i => block i = j)).card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ 2 * B := by
  classical
  have hblocks : (S.image block).card ≤ 2 := by
    apply closed_grid_blocks_card hH _ t
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact ht i hi
  have hsplit : S.card = ∑ j ∈ S.image block, (S.filter (fun i => block i = j)).card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter S (S.image block) block
    rw [Finset.filter_eq_self.mpr (fun i hi => Finset.mem_image_of_mem block hi)] at h
    exact h.symm
  calc
    (S.card : ℝ) = ∑ j ∈ S.image block, ((S.filter (fun i => block i = j)).card : ℝ) := by
      rw [hsplit, Nat.cast_sum]
    _ ≤ ∑ _j ∈ S.image block, B := Finset.sum_le_sum (fun j _ => hcount j)
    _ = ((S.image block).card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hblocks) hB

end Submission.Obl.k4_horizontal_strict_parameter_step
