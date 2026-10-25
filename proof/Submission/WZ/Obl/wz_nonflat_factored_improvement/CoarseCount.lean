-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.CoarseCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseGeometry
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Counts

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

abbrev PrismCount (a b L : ℝ) {q : ℕ} (W : Fin q → Set Space) : Prop :=
  ∀ U : Set Space, Convex ℝ U →
    ENNReal.ofReal ((Set.ncard {j | W j ⊆ U} : ℝ) * a * b) ≤
      ENNReal.ofReal L * volume U

/-- Convex counts pass from assigned prisms to their enlarged, normalized tubes. -/
theorem prismCount_to_coarse {a b κ r L : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hκ : 0 < κ) (hL : 0 ≤ L) {q M : ℕ} {W : Fin q → Set Space}
    (hcount : PrismCount a b L W) (j : Fin M → Fin q) (hj : Function.Injective j)
    (z w : Fin M → Space)
    (hcontain : ∀ i, (fun p : Space => κ • p) '' W (j i) ⊆ tube r (z i) (w i)) :
    ConvexCount r (r ^ 2 / (a * b) * L * κ⁻¹ ^ 3) z w := by
  intro U hU
  have hc := hcount ((fun p : Space => κ • p) ⁻¹' U)
    (hU.linear_preimage (LinearMap.lsmul ℝ Space κ))
  have hsub : {i | tube r (z i) (w i) ⊆ U} ⊆
      {i | W (j i) ⊆ (fun p : Space => κ • p) ⁻¹' U} := by
    intro i hi p hp
    exact hi (hcontain i ⟨p, hp, rfl⟩)
  have hn : Set.ncard {i | tube r (z i) (w i) ⊆ U} ≤
      Set.ncard {i | W i ⊆ (fun p : Space => κ • p) ⁻¹' U} :=
    (Set.ncard_mono hsub).trans (subfamily_count j hj (fun i => W i ⊆ (fun p : Space => κ • p) ⁻¹' U))
  have hn' : (Set.ncard {i | tube r (z i) (w i) ⊆ U} : ℝ) * a * b ≤
      (Set.ncard {i | W i ⊆ (fun p : Space => κ • p) ⁻¹' U} : ℝ) * a * b := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) ha.le) hb.le
  have hr : 0 ≤ r ^ 2 / (a * b) := by positivity
  calc
    _ = ENNReal.ofReal (r ^ 2 / (a * b)) *
        ENNReal.ofReal ((Set.ncard {i | tube r (z i) (w i) ⊆ U} : ℝ) * a * b) := by
      rw [← ENNReal.ofReal_mul hr]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (r ^ 2 / (a * b)) *
        (ENNReal.ofReal L * volume ((fun p : Space => κ • p) ⁻¹' U)) :=
      mul_le_mul_right ((ENNReal.ofReal_le_ofReal hn').trans hc) _
    _ = _ := by
      rw [volume_smul_preimage hκ, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_mul (mul_nonneg hr hL)]

/-- The original prism count bounds every fibre of an enlarged tube. -/
theorem prism_fiber_bound {a b κ r L : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hκ : 0 < κ) (hL : 0 ≤ L) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {q : ℕ} {W : Fin q → Set Space} (hcount : PrismCount a b L W)
    (F : Finset (Fin q)) (z w : Space) (hw : ‖w‖ = 1)
    (hcontain : ∀ j ∈ F, (fun p : Space => κ • p) '' W j ⊆ tube r z w) :
    (F.card : ℝ) ≤ 56 * (r ^ 2 / (a * b) * L * κ⁻¹ ^ 3) := by
  have hc := hcount ((fun p : Space => κ • p) ⁻¹' tube r z w)
    ((tube_convex r z w).linear_preimage (LinearMap.lsmul ℝ Space κ))
  have hn : F.card ≤ Set.ncard {j | W j ⊆ (fun p : Space => κ • p) ⁻¹' tube r z w} := by
    rw [← Set.ncard_coe_finset F]
    apply Set.ncard_mono
    intro j hj p hp
    exact hcontain j hj ⟨p, hp, rfl⟩
  have hc' : ENNReal.ofReal ((F.card : ℝ) * a * b) ≤
      ENNReal.ofReal (L * κ⁻¹ ^ 3 * (56 * r ^ 2)) := by
    calc
      _ ≤ ENNReal.ofReal ((Set.ncard {j | W j ⊆
          (fun p : Space => κ • p) ⁻¹' tube r z w} : ℝ) * a * b) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) ha.le) hb.le
      _ ≤ ENNReal.ofReal L * volume ((fun p : Space => κ • p) ⁻¹' tube r z w) := hc
      _ ≤ ENNReal.ofReal L * (ENNReal.ofReal (κ⁻¹ ^ 3) * ENNReal.ofReal (56 * r ^ 2)) := by
        rw [volume_smul_preimage hκ]
        gcongr
        exact tube_volume_upper hr hr1 z w hw
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_mul (by positivity)]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hc'
  calc
    _ ≤ (L * κ⁻¹ ^ 3 * (56 * r ^ 2)) / (a * b) :=
      (le_div_iff₀ (mul_pos ha hb)).mpr (by nlinarith only [hreal])
    _ = _ := by ring

end WangZahlLot.Obl.wz_nonflat_factored_improvement
