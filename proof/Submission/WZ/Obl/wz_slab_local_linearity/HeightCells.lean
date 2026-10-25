-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.HeightCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.Covering

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric MeasureTheory
open scoped ENNReal

/-- The complete height interval supplied by a half-open grid cube. -/
def heightCell (ρ : ℝ) (k : ℤ) : Set ℝ := Ico (ρ * k) (ρ * ((k : ℝ) + 1))

def heightCells (ρ : ℝ) (K : Finset ℤ) : Set ℝ := ⋃ k ∈ K, heightCell ρ k

lemma measurableSet_heightCells (ρ : ℝ) (K : Finset ℤ) : MeasurableSet (heightCells ρ K) := by
  unfold heightCells heightCell
  exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_Ico

lemma heightCell_disjoint {ρ : ℝ} (hρ : 0 ≤ ρ) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (heightCell ρ i) (heightCell ρ j) := by
  have h (a b : ℤ) (hab : a < b) : Disjoint (heightCell ρ a) (heightCell ρ b) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast Int.add_one_le_iff.mpr hab
    have hh := mul_le_mul_of_nonneg_left hab' hρ
    exact not_lt_of_ge ((show ρ * b ≤ z from hz'.1).trans' hh) hz.2
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact h i j hij
  · exact (h j i hji).symm

lemma volume_heightCell (ρ : ℝ) (k : ℤ) : volume (heightCell ρ k) = ENNReal.ofReal ρ := by
  rw [heightCell, Real.volume_Ico]
  congr 1
  ring

lemma volume_heightCells {ρ : ℝ} (hρ : 0 ≤ ρ) (K : Finset ℤ) :
    volume (heightCells ρ K) = ENNReal.ofReal ((K.card : ℝ) * ρ) := by
  rw [heightCells, measure_biUnion_finset (fun i _ j _ hij => heightCell_disjoint hρ hij)
    (fun _ _ => measurableSet_Ico)]
  simp only [volume_heightCell, Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

lemma CoverLower.le_card_of_finset_image {ι X : Type*} [PseudoMetricSpace X]
    {S : Set X} {r N : ℝ} (h : CoverLower S r N) (hr : 0 ≤ r)
    (K : Finset ι) (f : ι → X) (hS : S ⊆ f '' (K : Set ι)) : N ≤ (K.card : ℝ) := by
  classical
  let e := K.equivFin
  apply h K.card (fun j => f (e.symm j))
  rintro x hx
  obtain ⟨k, hk, rfl⟩ := hS hx
  refine mem_iUnion.mpr ⟨e ⟨k, hk⟩, ?_⟩
  simpa [e, mem_closedBall] using hr

/-- An entropy lower bound for one point in each retained height cell gives a
Lebesgue measure lower bound for the union of the full cells. -/
lemma volume_heightCells_lower {X : Type*} [PseudoMetricSpace X]
    {ρ r N : ℝ} {S : Set X} (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (K : Finset ℤ) (f : ℤ → X) (hS : S ⊆ f '' (K : Set ℤ))
    (hcover : CoverLower S r N) :
    ENNReal.ofReal (N * ρ) ≤ volume (heightCells ρ K) := by
  rw [volume_heightCells hρ]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (hcover.le_card_of_finset_image hr K f hS) hρ)

/-- Affine approximation at the lower endpoint of every retained cell extends
across the whole cell, using the Lipschitz bound and a bounded affine slope. -/
lemma affine_on_heightCells {ρ a b : ℝ} {K : Finset ℤ} {f : ℝ → ℝ} {Z : Set ℝ}
    (hρ : 0 < ρ) (hZ : heightCells ρ K ⊆ Z) (hb : |b| ≤ 4)
    (hf : ∀ x ∈ Z, ∀ y ∈ Z, |f x - f y| ≤ |x - y|)
    (hanchor : ∀ k ∈ K, |f (ρ * k) - (a + b * (ρ * k))| ≤ 4 * ρ) :
    ∀ z ∈ heightCells ρ K, |f z - (a + b * z)| ≤ 9 * ρ := by
  intro z hz
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
  have hkmem : ρ * k ∈ heightCells ρ K := by
    apply mem_iUnion₂.mpr
    refine ⟨k, hk, le_rfl, ?_⟩
    nlinarith
  have hzd : |z - ρ * k| ≤ ρ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hzk.1)]
    have hz' := hzk.2
    linarith
  have hfd : |f z - f (ρ * k)| ≤ ρ := (hf z (hZ hz) _ (hZ hkmem)).trans hzd
  have hbd : |b * (ρ * k - z)| ≤ 4 * ρ := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul hb hzd (abs_nonneg _) (by norm_num)
  calc
    |f z - (a + b * z)| =
        |(f z - f (ρ * k)) + (f (ρ * k) - (a + b * (ρ * k))) + b * (ρ * k - z)| := by
          congr 1; ring
    _ ≤ |f z - f (ρ * k)| + |f (ρ * k) - (a + b * (ρ * k))| + |b * (ρ * k - z)| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 9 * ρ := by linarith [hanchor k hk]

end WangZahlLot.Obl.wz_slab_local_linearity
