-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.PrismGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Basic
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file PrismGeometry.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

lemma basis_of_frame {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ Space, B 0 = e₁ ∧ B 1 = e₂ ∧ B 2 = e₃ := by
  have he' : Orthonormal ℝ ((univ : Set (Fin 3)).domRestrict ![e₁, e₂, e₃]) :=
    he.comp _ Subtype.val_injective
  obtain ⟨B, hB⟩ := he'.exists_orthonormalBasis_extension_of_card_eq (by simp [Space])
  exact ⟨B, by simpa using hB 0 (mem_univ _),
    by simpa using hB 1 (mem_univ _), by simpa using hB 2 (mem_univ _)⟩

lemma prism_convex (a b : ℝ) (c e₁ e₂ e₃ : Space) :
    Convex ℝ (Prism a b c e₁ e₂ e₃) := by
  have h (e : Space) (r : ℝ) : Convex ℝ {y : Space | |inner ℝ e (y - c)| ≤ r} := by
    have he : {y : Space | |inner ℝ e (y - c)| ≤ r} =
        {y | inner ℝ e c - r ≤ inner ℝ e y} ∩
          {y | inner ℝ e y ≤ inner ℝ e c + r} := by
      ext y
      simp only [mem_ofPred_eq, mem_inter_iff, inner_sub_right, abs_le]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    rw [he]
    exact (convex_halfSpace_ge (innerSL ℝ e).toLinearMap.isLinear _).inter
      (convex_halfSpace_le (innerSL ℝ e).toLinearMap.isLinear _)
  exact (h e₁ a).inter ((h e₂ b).inter (h e₃ 1))

lemma prism_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (c e₁ e₂ e₃ : Space) (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    volume (Prism a b c e₁ e₂ e₃) = ENNReal.ofReal (8 * a * b) := by
  obtain ⟨B, h₁, h₂, h₃⟩ := basis_of_frame he
  let d : Fin 3 → ℝ := ![a, b, 1]
  have hset : Prism a b c e₁ e₂ e₃ =
      {y : Space | ∀ i, -d i ≤ B.repr (y - c) i ∧ B.repr (y - c) i ≤ d i} := by
    ext y
    simp only [Prism, mem_ofPred_eq, OrthonormalBasis.repr_apply_apply]
    constructor
    · rintro ⟨h₁', h₂', h₃'⟩ i
      fin_cases i
      · simpa [d, h₁] using abs_le.mp h₁'
      · simpa [d, h₂] using abs_le.mp h₂'
      · simpa [d, h₃] using abs_le.mp h₃'
    · intro h
      exact ⟨by simpa [d, h₁] using abs_le.mpr (h 0),
        by simpa [d, h₂] using abs_le.mpr (h 1),
        by simpa [d, h₃] using abs_le.mpr (h 2)⟩
  rw [hset, WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
  simp only [Fin.prod_univ_three]
  change ENNReal.ofReal (a - -a) * ENNReal.ofReal (b - -b) *
    ENNReal.ofReal (1 - -(1 : ℝ)) = _
  simp only [sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- A prism needs no longitudinal extension beyond the unit ball.  Removing its
longitudinal centre coordinate preserves all points of the ball satisfying its
two transverse constraints. -/
lemma prism_recenter_longitudinal {a b : ℝ} (c e₁ e₂ e₃ : Space)
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    Metric.ball (0 : Space) 1 ∩
      {y | |inner ℝ e₁ (y - c)| ≤ a ∧ |inner ℝ e₂ (y - c)| ≤ b} ⊆
      Prism a b (c - inner ℝ e₃ c • e₃) e₁ e₂ e₃ := by
  have h₁₃ : inner ℝ e₁ e₃ = 0 := by
    simpa using (orthonormal_iff_ite.mp he (0 : Fin 3) 2)
  have h₂₃ : inner ℝ e₂ e₃ = 0 := by
    simpa using (orthonormal_iff_ite.mp he (1 : Fin 3) 2)
  have h₃₃ : inner ℝ e₃ e₃ = 1 := by
    simpa using (orthonormal_iff_ite.mp he (2 : Fin 3) 2)
  have hnorm : ‖e₃‖ = 1 := by simpa using he.norm_eq_one (2 : Fin 3)
  rintro y ⟨hy, h₁, h₂⟩
  have hy' : ‖y‖ < 1 := by simpa using hy
  change |inner ℝ e₁ (y - (c - inner ℝ e₃ c • e₃))| ≤ a ∧
    |inner ℝ e₂ (y - (c - inner ℝ e₃ c • e₃))| ≤ b ∧
    |inner ℝ e₃ (y - (c - inner ℝ e₃ c • e₃))| ≤ 1
  simp only [inner_sub_right, inner_smul_right, h₁₃, h₂₃, h₃₃,
    mul_zero, mul_one, sub_zero, sub_self]
  refine ⟨by simpa [inner_sub_right] using h₁, by simpa [inner_sub_right] using h₂, ?_⟩
  exact (abs_real_inner_le_norm e₃ y).trans (by simpa [hnorm] using hy'.le)

/-- Transverse widths can be capped at one simultaneously for an entire family:
coordinates whose width exceeds one are centred at zero, and the unit ball
supplies their bound.  The long coordinate is centred at zero as well. -/
lemma prism_normalize (a b : ℝ) (c e₁ e₂ e₃ : Space)
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    ∃ c' : Space, Metric.ball (0 : Space) 1 ∩
      {y | |inner ℝ e₁ (y - c)| ≤ a ∧ |inner ℝ e₂ (y - c)| ≤ b} ⊆
      Prism (min a 1) (min b 1) c' e₁ e₂ e₃ := by
  classical
  obtain ⟨B, hB₀, hB₁, hB₂⟩ := basis_of_frame he
  let t : Fin 3 → ℝ := ![if a ≤ 1 then inner ℝ e₁ c else 0,
    if b ≤ 1 then inner ℝ e₂ c else 0, 0]
  let c' : Space := B.repr.symm (WithLp.toLp 2 t)
  have hc' (i : Fin 3) : inner ℝ (B i) c' = t i := by
    rw [← OrthonormalBasis.repr_apply_apply]
    dsimp only [c']
    rw [B.repr.apply_symm_apply]
  refine ⟨c', ?_⟩
  rintro y ⟨hy, h₁, h₂⟩
  have hy' : ‖y‖ ≤ 1 := (show ‖y‖ < 1 by simpa using hy).le
  have hi (i : Fin 3) : |inner ℝ (B i) y| ≤ 1 :=
    (abs_real_inner_le_norm _ _).trans (by simpa [B.norm_eq_one i] using hy')
  have hcoord (i : Fin 3) : inner ℝ (B i) (y - c') = inner ℝ (B i) y - t i := by
    rw [inner_sub_right, hc']
  change |inner ℝ e₁ (y - c')| ≤ min a 1 ∧
    |inner ℝ e₂ (y - c')| ≤ min b 1 ∧ |inner ℝ e₃ (y - c')| ≤ 1
  rw [← hB₀, ← hB₁, ← hB₂, hcoord, hcoord, hcoord]
  refine ⟨?_, ?_, ?_⟩
  · by_cases ha : a ≤ 1
    · simpa [t, ha, min_eq_left ha, hB₀, inner_sub_right] using h₁
    · simpa [t, ha, min_eq_right (le_of_not_ge ha)] using hi 0
  · by_cases hb : b ≤ 1
    · simpa [t, hb, min_eq_left hb, hB₁, inner_sub_right] using h₂
    · simpa [t, hb, min_eq_right (le_of_not_ge hb)] using hi 1
  · simpa [t] using hi 2

lemma normalized_widths {δ a b : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha : δ ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    δ ≤ min a 1 ∧ min a 1 ≤ min b 1 ∧ min b 1 ≤ 1 ∧
      a * b / 4 ≤ min a 1 * min b 1 ∧ min a 1 * min b 1 ≤ a * b := by
  have ha0 := hδ.trans ha
  have hb0 := ha0.trans hab
  have ha2 : a ≤ 2 := hab.trans hb
  have hhalf₁ : a / 2 ≤ min a 1 := le_min (by linarith) (by linarith)
  have hhalf₂ : b / 2 ≤ min b 1 := le_min (by linarith) (by linarith)
  have hmin₁ : 0 ≤ min a 1 := le_min ha0 zero_le_one
  have hmin₂ : 0 ≤ min b 1 := le_min hb0 zero_le_one
  refine ⟨le_min ha hδ1, min_le_min hab le_rfl, min_le_right _ _, ?_, ?_⟩
  · nlinarith [mul_le_mul hhalf₁ hhalf₂ (by positivity : 0 ≤ b / 2) hmin₁]
  · exact mul_le_mul (min_le_left _ _) (min_le_left _ _) hmin₂ ha0

/-- Normalize the affine-image presentation used by the accepted convex
factorization theorem to the frame presentation used in branch (C). -/
lemma normalize_affine_prism (a b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space) :
    ∃ c e₁ e₂ e₃ : Space, Orthonormal ℝ ![e₁, e₂, e₃] ∧
      (e '' {y : Space | |y 0| ≤ a ∧ |y 1| ≤ b ∧ |y 2| ≤ 2}) ∩
          Metric.ball (0 : Space) 1 ⊆ Prism (min a 1) (min b 1) c e₁ e₂ e₃ := by
  let B₀ := EuclideanSpace.basisFun (Fin 3) ℝ
  let B := B₀.map e.linearIsometryEquiv
  have hB : Orthonormal ℝ ![B 0, B 1, B 2] := by
    convert B.orthonormal using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨c, hc⟩ := prism_normalize a b (e 0) (B 0) (B 1) (B 2) hB
  refine ⟨c, B 0, B 1, B 2, hB, ?_⟩
  rintro y ⟨⟨z, hz, rfl⟩, hy⟩
  have he (i : Fin 3) : inner ℝ (B i) (e z - e 0) = z i := by
    have hez : e z - e 0 = e.linearIsometryEquiv z := by
      simpa only [vsub_eq_sub, sub_zero] using (e.map_vsub z 0).symm
    rw [hez]
    change inner ℝ (e.linearIsometryEquiv (B₀ i)) (e.linearIsometryEquiv z) = z i
    rw [e.linearIsometryEquiv.inner_map_map, ← OrthonormalBasis.repr_apply_apply]
    rfl
  apply hc
  refine ⟨hy, ?_, ?_⟩
  · simpa only [he] using hz.1
  · simpa only [he] using hz.2.1

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
