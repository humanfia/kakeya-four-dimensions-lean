-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Slab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

/-- A closed slab written with an arbitrary continuous linear functional. -/
def slab (ℓ : E →L[ℝ] ℝ) (s r : ℝ) : Set E := {x | |ℓ x - s| ≤ r}

lemma slab_isClosed (ℓ : E →L[ℝ] ℝ) (s r : ℝ) : IsClosed (slab ℓ s r) := by
  apply isClosed_le _ continuous_const
  fun_prop

lemma homothety_coord (ℓ : E →L[ℝ] ℝ) (p q : E) (s t : ℝ) :
    ℓ (AffineMap.homothety p t q) - s =
      (1 - t) * (ℓ p - s) + t * (ℓ q - s) := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, map_add, map_smul,
    map_sub, smul_eq_mul]
  ring

/-- Two contractions of a slab toward a distant point are disjoint when their
contraction parameters are separated by more than the relative slab thickness. -/
lemma disjoint_homothetic_slabs (ℓ : E →L[ℝ] ℝ) (p : E) (s r t t' : ℝ)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (ht1 : t ≤ 1) (ht' : 0 ≤ t') (ht1' : t' ≤ 1)
    (hsep : 2 * r < |t - t'| * |ℓ p - s|) :
    Disjoint (AffineMap.homothety p t '' slab ℓ s r)
      (AffineMap.homothety p t' '' slab ℓ s r) := by
  rw [Set.disjoint_left]
  rintro z ⟨q, hq, rfl⟩ ⟨q', hq', he⟩
  have he' := congrArg (fun y => ℓ y - s) he
  rw [homothety_coord, homothety_coord] at he'
  have heq : (t - t') * (ℓ p - s) = t * (ℓ q - s) - t' * (ℓ q' - s) := by
    nlinarith [he']
  have hbound : |t - t'| * |ℓ p - s| ≤ 2 * r := by
    calc |t - t'| * |ℓ p - s| = |(t - t') * (ℓ p - s)| := (abs_mul _ _).symm
      _ = |t * (ℓ q - s) - t' * (ℓ q' - s)| := congrArg abs heq
      _ ≤ |t * (ℓ q - s)| + |t' * (ℓ q' - s)| := abs_sub _ _
      _ = t * |ℓ q - s| + t' * |ℓ q' - s| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg ht']
      _ ≤ t * r + t' * r := add_le_add
        (mul_le_mul_of_nonneg_left hq ht) (mul_le_mul_of_nonneg_left hq' ht')
      _ ≤ 2 * r := by nlinarith
  exact (not_lt_of_ge hbound) hsep

/-- Equally spaced contraction parameters in the interval `[1/2,1)`. -/
noncomputable def contraction (N : ℕ) (j : Fin N) : ℝ :=
  ((N : ℝ) + (j : ℕ)) / (2 * N)

lemma contraction_bounds {N : ℕ} (hN : 0 < N) (j : Fin N) :
    1 / 2 ≤ contraction N j ∧ contraction N j ≤ 1 := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hj : (j : ℝ) < N := by exact_mod_cast j.isLt
  unfold contraction
  constructor
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
    have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    linarith
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
    linarith

lemma contraction_separation {N : ℕ} (hN : 0 < N) {j k : Fin N} (hjk : j ≠ k) :
    (1 : ℝ) / (2 * N) ≤ |contraction N j - contraction N k| := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hne : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
  have hgap : (1 : ℝ) ≤ |(j : ℝ) - (k : ℝ)| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have h' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have h' : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  unfold contraction
  rw [← sub_div, add_sub_add_left_eq_sub, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
  exact div_le_div_of_nonneg_right hgap (by positivity)

/-- Packing contractions of a slab intersection into a compact convex set. -/
lemma slab_contraction_packing {U : Set E} (hUc : IsCompact U) (hUconv : Convex ℝ U)
    (ℓ : E →L[ℝ] ℝ) (s r : ℝ) (hr : 0 ≤ r) {p : E} (hp : p ∈ U)
    {N : ℕ} (hN : 0 < N) (hfar : 4 * (N : ℝ) * r < |ℓ p - s|) :
    (N : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) * volume (U ∩ slab ℓ s r) ≤ volume U := by
  let A : Fin N → Set E := fun j =>
    AffineMap.homothety p (contraction N j) '' (U ∩ slab ℓ s r)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hAcomp : ∀ j, IsCompact (A j) := by
    intro j
    exact (hUc.inter_right (slab_isClosed ℓ s r)).image (by
      change Continuous (fun q : E => contraction N j • (q - p) + p)
      fun_prop)
  have hAsub : ∀ j, A j ⊆ U := by
    intro j q hq
    obtain ⟨y, hy, rfl⟩ := hq
    obtain ⟨ht, ht1⟩ := contraction_bounds hN j
    have he : AffineMap.homothety p (contraction N j) y =
        (1 - contraction N j) • p + contraction N j • y := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [he]
    exact hUconv hp hy.1 (by linarith) (by linarith) (by ring)
  have hAdisj : Pairwise (fun j k => Disjoint (A j) (A k)) := by
    intro j k hjk
    obtain ⟨ht, ht1⟩ := contraction_bounds hN j
    obtain ⟨ht', ht1'⟩ := contraction_bounds hN k
    have hgap := contraction_separation hN hjk
    have hsep : 2 * r < |contraction N j - contraction N k| * |ℓ p - s| := by
      calc 2 * r < (1 / (2 * N)) * |ℓ p - s| := by
            rw [one_div, inv_mul_eq_div, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
            nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hgap (abs_nonneg _)
    exact (disjoint_homothetic_slabs ℓ p s r _ _ hr (by linarith) ht1
      (by linarith) ht1' hsep).mono (Set.image_mono inter_subset_right)
        (Set.image_mono inter_subset_right)
  have hAlower : ∀ j, ENNReal.ofReal (1 / 8 : ℝ) * volume (U ∩ slab ℓ s r) ≤ volume (A j) := by
    intro j
    obtain ⟨ht, ht1⟩ := contraction_bounds hN j
    dsimp [A]
    rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonneg (by positivity : 0 ≤ contraction N j ^ 3)]
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ht 3
    norm_num at this ⊢
    exact this
  calc (N : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) * volume (U ∩ slab ℓ s r)
      = ∑ j : Fin N, ENNReal.ofReal (1 / 8 : ℝ) * volume (U ∩ slab ℓ s r) := by
        simp [mul_assoc]
    _ ≤ ∑ j : Fin N, volume (A j) := Finset.sum_le_sum fun j _ => hAlower j
    _ = volume (⋃ j, A j) := by
      simpa only [tsum_fintype] using
        (measure_iUnion (μ := volume) hAdisj (fun j => (hAcomp j).measurableSet)).symm
    _ ≤ volume U := measure_mono (iUnion_subset hAsub)

/-- A quantitative slab concentration lemma in dimension three. A compact convex set
with a fraction `t` of its volume in a slab lies in the slab enlarged by `80 / t`.
The proof packs disjoint contractions and does not require Brunn's theorem. -/
lemma subset_enlarged_slab_of_mass {U : Set E} (hUc : IsCompact U)
    (hUconv : Convex ℝ U) (hUpos : volume U ≠ 0) (ℓ : E →L[ℝ] ℝ)
    (s r t : ℝ) (hr : 0 ≤ r) (ht : 0 < t) (ht1 : t ≤ 1)
    (hmass : ENNReal.ofReal t * volume U ≤ volume (U ∩ slab ℓ s r)) :
    U ⊆ slab ℓ s (80 * r / t) := by
  let N : ℕ := ⌈16 / t⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity : (0 : ℝ) < 16 / t)
  have hNlow : (16 : ℝ) ≤ (N : ℝ) * t :=
    (div_le_iff₀ ht).mp (Nat.le_ceil (16 / t))
  have hNhigh : (N : ℝ) * t ≤ 17 := by
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 16 / t)
    have h' := mul_le_mul_of_nonneg_right h.le ht.le
    dsimp [N]
    rw [add_mul, div_mul_cancel₀ _ ht.ne'] at h'
    nlinarith
  intro p hp
  by_contra hnot
  have hfar : 80 * r / t < |ℓ p - s| := lt_of_not_ge hnot
  have hpack := slab_contraction_packing hUc hUconv ℓ s r hr hp hN
    (lt_of_le_of_lt (show 4 * (N : ℝ) * r ≤ 80 * r / t from by
      rw [le_div_iff₀ ht]
      nlinarith [mul_le_mul_of_nonneg_right hNhigh hr]) hfar)
  have hineq : ((N : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal t) * volume U ≤
      volume U := by
    calc _ = ((N : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ)) * (ENNReal.ofReal t * volume U) := by
          rw [mul_assoc]
      _ ≤ ((N : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ)) * volume (U ∩ slab ℓ s r) :=
        mul_le_mul_right hmass _
      _ ≤ volume U := hpack
  have hcoeff : (N : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal t ≤ 1 := by
    apply (ENNReal.mul_le_mul_iff_left hUpos hUc.measure_ne_top).mp
    simpa only [one_mul] using hineq
  have heq : (N : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal t =
      ENNReal.ofReal ((N : ℝ) * (1 / 8 : ℝ) * t) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    simp
  rw [heq, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at hcoeff
  nlinarith

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
