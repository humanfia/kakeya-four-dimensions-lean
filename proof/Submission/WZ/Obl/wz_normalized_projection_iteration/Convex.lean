-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Convex.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric Module MeasureTheory
open scoped ENNReal Pointwise

/-- A maximal simplex gives coordinates of size at most one on a compact body. -/
theorem exists_bounded_basis {W : Set Space} (hW : IsCompact W)
    (hWi : (interior W).Nonempty) :
    ∃ x ∈ W, ∃ b : Basis (Fin 3) ℝ Space,
      (∀ i, x + b i ∈ W) ∧ ∀ p ∈ W, ∀ i, |b.repr (p - x) i| ≤ 1 := by
  classical
  obtain ⟨x, hx⟩ := hWi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let t : ℝ := r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  let y₀ : Fin 3 → Space := fun i => x + t • e i
  have hy₀ : ∀ i, y₀ i ∈ W := by
    intro i
    apply hball
    simp only [mem_ball, y₀, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, e.norm_eq_one, mul_one]
    dsimp [t]
    linarith
  have hdet₀ : e.toBasis.det (fun i => y₀ i - x) ≠ 0 := by
    simp only [y₀, add_sub_cancel_left]
    rw [AlternatingMap.map_smul_univ]
    change ((∏ _ : Fin 3, t) • e.toBasis.det e.toBasis) ≠ 0
    rw [Basis.det_self]
    simp [ht.ne']
  let K : Set (Fin 3 → Space) := {y | ∀ i, y i ∈ W}
  have hK : IsCompact K := isCompact_pi_infinite (fun _ => hW)
  have hcont : Continuous (fun y : Fin 3 → Space => |e.toBasis.det (fun i => y i - x)|) := by
    simp only [Basis.det_apply, Matrix.det_fin_three, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    fun_prop
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨y₀, hy₀⟩ hcont.continuousOn
  let v : Fin 3 → Space := fun i => y i - x
  have hdet : e.toBasis.det v ≠ 0 := by
    have hh := hmax hy₀
    exact abs_pos.mp ((abs_pos.mpr hdet₀).trans_le hh)
  obtain ⟨hli, hspan⟩ := e.toBasis.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  let b : Basis (Fin 3) ℝ Space := Basis.mk hli hspan.ge
  refine ⟨x, interior_subset hx, b, ?_, ?_⟩
  · intro i
    simpa [b, v] using hy i
  · intro p hp i
    have hupdate : (Function.update y i p) ∈ K := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using hp
      · simpa [Function.update_of_ne hji] using hy j
    have hbound := hmax hupdate
    have heq : (fun j => Function.update y i p j - x) = Function.update v i (p - x) := by
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp [Function.update_of_ne hji, v]
    change |e.toBasis.det (fun j => Function.update y i p j - x)| ≤ |e.toBasis.det v| at hbound
    rw [heq] at hbound
    have hcramer := congrArg (fun f : Space →ₗ[ℝ] ℝ => f (p - x))
      (e.toBasis.det_smul_mk_coord_eq_det_update hli hspan.ge i)
    change e.toBasis.det v * b.repr (p - x) i = e.toBasis.det (Function.update v i (p - x)) at hcramer
    rw [← hcramer, abs_mul] at hbound
    exact (mul_le_mul_iff_right₀ (abs_pos.mpr hdet)).mp (by simpa using hbound)

/-- A coordinate box lies in a fixed dilation of a simplex contained in a convex set. -/
theorem coordinate_box_subset_dilation {W : Set Space} (hW : Convex ℝ W)
    {x : Space} (hx : x ∈ W) (b : Basis (Fin 3) ℝ Space)
    (hb : ∀ i, x + b i ∈ W) {R : ℝ} (hR : 1 ≤ R) :
    {p : Space | ∀ i, |b.repr (p - x) i| ≤ R} ⊆
      AffineMap.homothety (x + (1 / 4 : ℝ) • (∑ i, b i)) (16 * R) '' W := by
  intro p hp
  have hRp : 0 < R := by linarith
  let a : Fin 3 → ℝ := fun i => b.repr (p - x) i
  let w : Fin 3 → ℝ := fun i => (a i + (16 * R - 1) / 4) / (16 * R)
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    have hh := (abs_le.mp (hp i)).1
    apply div_nonneg _ (by positivity)
    dsimp [a] at *
    linarith
  have hws : w 0 + w 1 + w 2 ≤ 1 := by
    have h0 := (abs_le.mp (hp 0)).2
    have h1 := (abs_le.mp (hp 1)).2
    have h2 := (abs_le.mp (hp 2)).2
    dsimp [w, a]
    rw [← add_div, ← add_div, div_le_one (by positivity : 0 < 16 * R)]
    linarith
  have hmem : (1 - (w 0 + w 1 + w 2)) • x +
      w 0 • (x + b 0) + w 1 • (x + b 1) + w 2 • (x + b 2) ∈ W := by
    convert hW.sum_mem (t := Finset.univ)
      (w := ![1 - (w 0 + w 1 + w 2), w 0, w 1, w 2])
      (z := ![x, x + b 0, x + b 1, x + b 2]) ?_ ?_ ?_ using 1
    · simp [Fin.sum_univ_four]
    · intro i _
      fin_cases i
      · simpa using sub_nonneg.mpr hws
      · exact hw0 0
      · exact hw0 1
      · exact hw0 2
    · simp [Fin.sum_univ_four]
      ring
    · intro i _
      fin_cases i
      · exact hx
      · exact hb 0
      · exact hb 1
      · exact hb 2
  have hq : x + (w 0 • b 0 + w 1 • b 1 + w 2 • b 2) ∈ W := by
    convert hmem using 1
    module
  refine ⟨_, hq, ?_⟩
  have ha : a 0 • b 0 + a 1 • b 1 + a 2 • b 2 = p - x := by
    simpa [a, Fin.sum_univ_three] using b.sum_repr (p - x)
  have hw (i : Fin 3) : (16 * R) * w i = a i + (16 * R - 1) / 4 := by
    dsimp [w]
    field_simp
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, Fin.sum_univ_three]
  have hid : (16 * R) •
      (x + (w 0 • b 0 + w 1 • b 1 + w 2 • b 2) -
        (x + (1 / 4 : ℝ) • (b 0 + b 1 + b 2))) +
      (x + (1 / 4 : ℝ) • (b 0 + b 1 + b 2)) =
      x + (a 0 • b 0 + a 1 • b 1 + a 2 • b 2) := by
    simp only [smul_sub, smul_add, smul_smul, hw]
    module
  rw [hid, ha]
  abel

/-- A bounded convex body admits a volume-controlled container for its affine differences. -/
theorem exists_convex_difference_container {W : Set Space} (hW : Convex ℝ W)
    (hWb : Bornology.IsBounded W) (hWi : (interior W).Nonempty)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ U : Set Space, Convex ℝ U ∧
      volume U = ENNReal.ofReal ((48 * R) ^ 3) * volume W ∧
      ∀ p ∈ W, ∀ q ∈ W, ∀ z ∈ W, p + R • (q - z) ∈ U := by
  obtain ⟨x, hx, b, hb, hcoord⟩ := exists_bounded_basis hWb.isCompact_closure
    (hWi.mono (interior_mono subset_closure))
  let c : Space := x + (1 / 4 : ℝ) • (∑ i, b i)
  let U : Set Space := AffineMap.homothety c (48 * R) '' closure W
  refine ⟨U, hW.closure.affine_image _, ?_, ?_⟩
  · dsimp [U]
    rw [Measure.addHaar_image_homothety,
      finrank_euclideanSpace_fin]
    rw [abs_of_nonneg (by positivity), measure_closure_of_null_frontier (hW.addHaar_frontier volume)]
  · intro p hp q hq z hz
    have hc := coordinate_box_subset_dilation hW.closure hx b hb
      (show (1 : ℝ) ≤ 3 * R by linarith)
    have hmem : p + R • (q - z) ∈ {p : Space | ∀ i, |b.repr (p - x) i| ≤ 3 * R} := by
      intro i
      have h1 := hcoord p (subset_closure hp) i
      have h2 := hcoord q (subset_closure hq) i
      have h3 := hcoord z (subset_closure hz) i
      have heq : p + R • (q - z) - x = (p - x) + R • ((q - x) - (z - x)) := by module
      have heq' : b.repr (p + R • (q - z) - x) i =
          b.repr (p - x) i + R * (b.repr (q - x) i - b.repr (z - x) i) := by
        rw [heq]
        simp
      rw [heq']
      calc
        _ ≤ |b.repr (p - x) i| + |R * (b.repr (q - x) i - b.repr (z - x) i)| := abs_add_le _ _
        _ ≤ 1 + R * (1 + 1) := by
          rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ R)]
          exact add_le_add h1 (mul_le_mul_of_nonneg_left
            ((abs_sub _ _).trans (add_le_add h2 h3)) (by linarith))
        _ ≤ 3 * R := by linarith
    have hh := hc hmem
    simpa only [show 16 * (3 * R) = 48 * R by ring] using hh

end WangZahlLot.Obl.wz_normalized_projection_iteration
