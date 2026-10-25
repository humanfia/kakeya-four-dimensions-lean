-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NormalizedFactoring.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoverPruning
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.PrismGeometry
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Saturation

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file NormalizedFactoring.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective exists_enumerate)
open WangZahlLot.Obl.wz_concentrated_convex_factorization (enumerate_ncard)

attribute [local instance] Classical.propDecidable

/-- The long affine prisms in convex factorization can be replaced by the exact
prisms of branch (C).  This costs a factor four in cardinality and quadratic
losses in the saturation and incidence constants. -/
theorem normalize_saturated_cover {n p : ℕ} (A : Fin n → Set Space)
    (W : Fin p → Set Space) {a b w c H D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 < w) (hc : 0 < c)
    (hH : 0 < H) (hD : 0 < D)
    (hball : ∀ i, A i ⊆ Metric.ball (0 : Space) 1)
    (hupper : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((contained A U : ℝ) * w) ≤ ENNReal.ofReal c * volume U)
    (hshape : ∀ j, ∃ e : Space ≃ᵃⁱ[ℝ] Space,
      W j = e '' {y : Space | |y 0| ≤ a ∧ |y 1| ≤ b ∧ |y 2| ≤ 2})
    (hcover : ∀ i, ∃ j, A i ⊆ W j)
    (hdegree : ∀ i, (ncard {j | A i ⊆ W j} : ℝ) ≤ D)
    (hsat : ∀ j, c * a * b ≤ H * (contained A (W j) : ℝ) * w) :
    ∃ (k : ℕ) (g : Fin k → Fin n) (q : ℕ) (z e₁ e₂ e₃ : Fin q → Space),
      Function.Injective g ∧ (n : ℝ) ≤ 4 * k ∧
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
      (let P := fun j => Prism (min a 1) (min b 1) (z j) (e₁ j) (e₂ j) (e₃ j)
       (∀ i, ∃ j, A (g i) ⊆ P j) ∧
       (∀ i, (ncard {j | A (g i) ⊆ P j} : ℝ) ≤ 64 * H * D) ∧
       (∀ j, c * (8 * min a 1 * min b 1) ≤
         (32 * H * D) * (contained (fun i => A (g i)) (P j) : ℝ) * w)) := by
  classical
  have hgeo (j : Fin p) : ∃ z e₁ e₂ e₃ : Space,
      Orthonormal ℝ ![e₁, e₂, e₃] ∧
      W j ∩ Metric.ball (0 : Space) 1 ⊆ Prism (min a 1) (min b 1) z e₁ e₂ e₃ := by
    obtain ⟨e, he⟩ := hshape j
    rw [he]
    exact normalize_affine_prism a b e
  choose z e₁ e₂ e₃ he hsub using hgeo
  let Q := fun j => Prism (min a 1) (min b 1) (z j) (e₁ j) (e₂ j) (e₃ j)
  have hmina : 0 ≤ min a 1 := le_min ha zero_le_one
  have hminb : 0 ≤ min b 1 := le_min hb zero_le_one
  have harea : min a 1 * min b 1 ≤ a * b :=
    mul_le_mul (min_le_left _ _) (min_le_left _ _) hminb ha
  have hvol (j) : volume (Q j) = ENNReal.ofReal (8 * min a 1 * min b 1) :=
    prism_volume hmina hminb _ _ _ _ (he j)
  have hkeep (i j) (hij : A i ⊆ W j) : A i ⊆ Q j :=
    (Set.subset_inter hij (hball i)).trans (hsub j)
  have hbound (j) : (contained A (Q j) : ℝ) * w ≤ 8 * c * a * b := by
    have hh := hupper (Q j) (prism_convex _ _ _ _ _ _)
    rw [hvol j, ← ENNReal.ofReal_mul hc.le] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    have hm := mul_le_mul_of_nonneg_left harea (by positivity : 0 ≤ 8 * c)
    nlinarith only [hh', hm]
  have hload (j) : (contained A (Q j) : ℝ) ≤ (8 * H) * contained A (W j) := by
    apply (mul_le_mul_iff_left₀ hw).mp
    have hm := mul_le_mul_of_nonneg_left (hsat j) (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith only [hbound j, hm]
  obtain ⟨J, R, hsize, hcoverR, hdegreeR, hfib⟩ :=
    prune_changed_cover A W Q hD (by positivity : 0 < 8 * H)
      hcover hdegree hkeep hload
  have hsatR (j) (hj : j ∈ J) : c * (8 * min a 1 * min b 1) ≤
      (32 * H * D) * ((R.filter fun i => A i ⊆ Q j).card : ℝ) * w := by
    have hm₁ := mul_le_mul_of_nonneg_left harea (by positivity : 0 ≤ 8 * c)
    have hm₂ := mul_le_mul_of_nonneg_left (hsat j) (by norm_num : (0 : ℝ) ≤ 8)
    have hm₃ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hfib j hj) hH.le) hw.le
    nlinarith only [hm₁, hm₂, hm₃]
  refine ⟨R.card, enumerate R, J.card, z ∘ enumerate J, e₁ ∘ enumerate J,
    e₂ ∘ enumerate J, e₃ ∘ enumerate J, enumerate_injective R, hsize,
    (fun j => he (enumerate J j)), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj, hij⟩ := hcoverR (enumerate R i) (enumerate_mem R i)
    obtain ⟨j', rfl⟩ := exists_enumerate J hj
    exact ⟨j', hij⟩
  · intro i
    change (ncard {j | A (enumerate R i) ⊆ Q (enumerate J j)} : ℝ) ≤ _
    rw [enumerate_ncard J (fun j => A (enumerate R i) ⊆ Q j)]
    convert hdegreeR (enumerate R i) (enumerate_mem R i) using 1 <;> ring
  · intro j
    change c * (8 * min a 1 * min b 1) ≤ (32 * H * D) *
      (ncard {i | A (enumerate R i) ⊆ Q (enumerate J j)} : ℝ) * w
    rw [enumerate_ncard R (fun i => A i ⊆ Q (enumerate J j))]
    exact hsatR (enumerate J j) (enumerate_mem J j)

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
