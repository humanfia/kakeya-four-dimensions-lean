-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainScale
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- A closed interval-ball of radius `h` is covered by `⌈h / ρ⌉₊ + 1` closed balls of radius
`ρ`. -/
theorem closedBall_real_cover (t h ρ : ℝ) (hρ : 0 < ρ) (hh : 0 ≤ h) :
    ∃ c : Fin (⌈h / ρ⌉₊ + 1) → ℝ, closedBall t h ⊆ ⋃ j, closedBall (c j) ρ := by
  refine ⟨fun j => t - h + ρ + 2 * ρ * (j : ℝ), ?_⟩
  intro y hy
  rw [mem_closedBall, Real.dist_eq, abs_le] at hy
  -- the index of the ball containing `y`
  set j := ⌊(y - (t - h)) / (2 * ρ)⌋₊ with hj
  have hy0 : 0 ≤ (y - (t - h)) / (2 * ρ) := div_nonneg (by linarith) (by positivity)
  have hjle : (j : ℝ) ≤ (y - (t - h)) / (2 * ρ) := Nat.floor_le hy0
  have hjlt : (y - (t - h)) / (2 * ρ) < j + 1 := Nat.lt_floor_add_one _
  have hjN : j < ⌈h / ρ⌉₊ + 1 := by
    have h1 : (y - (t - h)) / (2 * ρ) ≤ h / ρ := by
      rw [div_le_div_iff₀ (by positivity) hρ]; nlinarith
    have h2 : (j : ℝ) ≤ ⌈h / ρ⌉₊ := hjle.trans (h1.trans (Nat.le_ceil _))
    have : j ≤ ⌈h / ρ⌉₊ := by exact_mod_cast h2
    omega
  refine mem_iUnion.2 ⟨⟨j, hjN⟩, ?_⟩
  rw [mem_closedBall, Real.dist_eq, abs_le]
  simp only
  rw [le_div_iff₀ (by positivity)] at hjle
  rw [div_lt_iff₀ (by positivity)] at hjlt
  constructor <;> nlinarith

/-- **Counting grains in a window.**  If each position `t` of `P` carries a set `G t` of volume at
least `m`, the sets of positions farther than `2 h` apart are disjoint, and all of them lie in a
region of volume at most `U`, then `P` is covered by at most `(U / m) (h / ρ + 2)` closed balls of
radius `ρ`. -/
theorem window_count {P : Set ℝ} (hPb : Bornology.IsBounded P) {G : ℝ → Set Space}
    {Ω : Set Space} {h ρ m U : ℝ} (hh : 0 < h) (hρ : 0 < ρ) (hm : 0 < m) (hU : 0 ≤ U)
    (hGm : ∀ t ∈ P, MeasurableSet (G t)) (hGv : ∀ t ∈ P, ENNReal.ofReal m ≤ volume (G t))
    (hGΩ : ∀ t ∈ P, G t ⊆ Ω) (hΩ : volume Ω ≤ ENNReal.ofReal U)
    (hdisj : ∀ t ∈ P, ∀ t' ∈ P, 2 * h < dist t t' → Disjoint (G t) (G t')) :
    ∃ (N : ℕ) (c : Fin N → ℝ), P ⊆ ⋃ j, closedBall (c j) ρ ∧
      (N : ℝ) ≤ U / m * (2 * h / ρ + 2) := by
  classical
  have htb : TotallyBounded P := hPb.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨F, hFP, hsep, hcov⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover htb
      (by positivity : 0 < 2 * h)
  -- the separated positions carry disjoint grains
  have hFcard : (F.card : ℝ) * m ≤ U := by
    have h1 : ∑ t ∈ F, volume (G t) ≤ volume Ω := by
      rw [← measure_biUnion_finset (fun t ht t' ht' hne => hdisj t (hFP ht) t' (hFP ht')
        (hsep t ht t' ht' hne)) (fun t ht => hGm t (hFP ht))]
      exact measure_mono (iUnion₂_subset fun t ht => hGΩ t (hFP ht))
    have h2 : ∑ _t ∈ F, ENNReal.ofReal m ≤ ∑ t ∈ F, volume (G t) :=
      Finset.sum_le_sum fun t ht => hGv t (hFP ht)
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h2
    have h3 := (h2.trans h1).trans hΩ
    exact (ENNReal.ofReal_le_ofReal_iff hU).1 h3
  -- cover each `2h`-ball by `ρ`-balls
  set K := ⌈2 * h / ρ⌉₊ + 1 with hK
  have hcover := fun t => closedBall_real_cover t (2 * h) ρ hρ (by positivity)
  choose cc hcc using hcover
  let e : F × Fin K ≃ Fin (F.card * K) :=
    (Equiv.prodCongr F.equivFin (Equiv.refl _)).trans finProdFinEquiv
  refine ⟨F.card * K, fun j => cc (e.symm j).1 (e.symm j).2, ?_, ?_⟩
  · intro y hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.1 (hcov hy)
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcc t hyt)
    refine mem_iUnion.2 ⟨e (⟨t, ht⟩, j), ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact hj
  · have hKle : (K : ℝ) ≤ 2 * h / ρ + 2 := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * h / ρ)
      rw [hK]; push_cast; linarith
    have hF : (F.card : ℝ) ≤ U / m := by rw [le_div_iff₀ hm]; exact hFcard
    push_cast
    exact mul_le_mul hF hKle (Nat.cast_nonneg _) (le_trans (by positivity) hF)

/-- Volume of a slab piece of a ball: `O(A² (β - α))`. -/
theorem volume_ball_slab_le {u : Space} (hu : ‖u‖ = 1) (p : Space) {A α β : ℝ} (hA : 0 ≤ A)
    (hαβ : α ≤ β) :
    volume (closedBall p A ∩ {y | inner ℝ u y ∈ Icc α β}) ≤
      ENNReal.ofReal ((2 * A) ^ 2 * (β - α)) := by
  classical
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hu
  let lo : Fin 3 → ℝ := fun i => if i = 0 then α - inner ℝ u p else -A
  let hi : Fin 3 → ℝ := fun i => if i = 0 then β - inner ℝ u p else A
  have hsub : closedBall p A ∩ {y | inner ℝ u y ∈ Icc α β} ⊆
      {y : Space | ∀ i, lo i ≤ b.repr (y - p) i ∧ b.repr (y - p) i ≤ hi i} := by
    rintro y ⟨hy, hyab⟩
    intro i
    simp only [OrthonormalBasis.repr_apply_apply]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [lo, hi, if_true, hb, inner_sub_right]
      exact ⟨by linarith [hyab.1], by linarith [hyab.2]⟩
    · simp only [lo, hi, hi0, if_false]
      have h1 := abs_real_inner_le_norm (b i) (y - p)
      rw [b.norm_eq_one i, one_mul, ← dist_eq_norm] at h1
      have h2 := h1.trans (mem_closedBall.1 hy)
      exact abs_le.1 h2
  refine (measure_mono hsub).trans ?_
  rw [WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
  rw [Fin.prod_univ_three]
  simp only [lo, hi, Fin.isValue, if_true, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, if_false]
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by nlinarith)]
  apply ENNReal.ofReal_le_ofReal
  have : β - inner ℝ u p - (α - inner ℝ u p) = β - α := by ring
  rw [this]
  nlinarith

/-- **Window volume**: a slab piece of a ball is covered by `O((A + r)² (β - α + 2 r) / r³)`
closed balls of radius `r`; hence a set with volume at most `U` in every such ball has volume at
most that many times `U` in the slab piece. -/
theorem volume_window_le {u : Space} (hu : ‖u‖ = 1) (p : Space) {A α β r U : ℝ} (hA : 0 ≤ A)
    (hαβ : α ≤ β) (hr : 0 < r) {E : Set Space}
    (hE : ∀ c : Space, volume (E ∩ closedBall c r) ≤ ENNReal.ofReal U) (hU : 0 ≤ U) :
    volume (E ∩ (closedBall p A ∩ {y | inner ℝ u y ∈ Icc α β})) ≤
      ENNReal.ofReal (8 * (2 * (A + r)) ^ 2 * (β - α + 2 * r) / r ^ 3 * U) := by
  classical
  set Ω := closedBall p A ∩ {y | inner ℝ u y ∈ Icc α β} with hΩ
  set Ω' := closedBall p (A + r) ∩ {y | inner ℝ u y ∈ Icc (α - r) (β + r)} with hΩ'
  have hr2 : 0 < r / 2 := by positivity
  obtain ⟨S, -, hS⟩ := exists_cells_cover p hA hr2
  set T := S.filter fun m => (gridCube (r / 2) m ∩ Ω).Nonempty with hT
  -- each cube meeting `Ω` lies in the enlarged slab piece
  have hcube : ∀ m ∈ T, gridCube (r / 2) m ⊆ Ω' := by
    intro m hm y hy
    obtain ⟨y0, hy0Q, hy0Ω⟩ := (Finset.mem_filter.1 hm).2
    have hd : dist y y0 < r := by
      have := diam_le_of_mem_gridCube hr2 hy hy0Q; linarith
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall]
      calc dist y p ≤ dist y y0 + dist y0 p := dist_triangle _ _ _
        _ ≤ r + A := add_le_add hd.le (mem_closedBall.1 hy0Ω.1)
        _ = A + r := by ring
    · have h1 : |inner ℝ u y - inner ℝ u y0| ≤ r := by
        rw [← inner_sub_right]
        calc |inner ℝ u (y - y0)| ≤ ‖u‖ * ‖y - y0‖ := abs_real_inner_le_norm _ _
          _ ≤ r := by rw [hu, one_mul, ← dist_eq_norm]; exact hd.le
      have h2 := hy0Ω.2
      simp only [mem_setOf_eq, mem_Icc] at h2 ⊢
      rw [abs_le] at h1
      constructor <;> linarith
  -- the number of such cubes
  have hTcard : (T.card : ℝ) * (r / 2) ^ 3 ≤ (2 * (A + r)) ^ 2 * (β - α + 2 * r) := by
    have h1 : volume (⋃ m ∈ T, gridCube (r / 2) m) = ∑ m ∈ T, volume (gridCube (r / 2) m) :=
      measure_biUnion_finset (fun m _ m' _ hmm => gridCube_disjoint hr2 hmm)
        (fun m _ => measurableSet_gridCube _ m)
    have h2 : volume (⋃ m ∈ T, gridCube (r / 2) m) ≤ volume Ω' :=
      measure_mono (iUnion₂_subset hcube)
    have h3 := volume_ball_slab_le hu p (A := A + r) (α := α - r) (β := β + r) (by linarith)
      (by linarith)
    rw [h1] at h2
    simp only [volume_gridCube hr2, Finset.sum_const, nsmul_eq_mul] at h2
    have h4 := h2.trans h3
    rw [← ENNReal.ofReal_pow hr2.le, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h4
    have h5 := (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).1 h4
    have : β + r - (α - r) = β - α + 2 * r := by ring
    rw [this] at h5
    exact h5
  -- covering `E ∩ Ω` by balls around the corners of the cubes
  let cn : (Fin 3 → ℤ) → Space := fun m => WithLp.toLp 2 fun j => r / 2 * (m j : ℝ)
  have hcov : E ∩ Ω ⊆ ⋃ m ∈ T, E ∩ closedBall (cn m) r := by
    rintro y ⟨hyE, hyΩ⟩
    set m := cubeIndex (r / 2) y
    have hym : y ∈ gridCube (r / 2) m := mem_gridCube_cubeIndex hr2 y
    have hmS : m ∈ S := hS y (mem_closedBall.1 hyΩ.1)
    have hmT : m ∈ T := Finset.mem_filter.2 ⟨hmS, y, hym, hyΩ⟩
    refine mem_iUnion₂.2 ⟨m, hmT, hyE, ?_⟩
    have := diam_le_of_mem_gridCube hr2 hym (corner_mem_gridCube hr2 m)
    rw [mem_closedBall]; linarith
  calc volume (E ∩ Ω) ≤ volume (⋃ m ∈ T, E ∩ closedBall (cn m) r) := measure_mono hcov
    _ ≤ ∑ m ∈ T, volume (E ∩ closedBall (cn m) r) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ T, ENNReal.ofReal U := Finset.sum_le_sum fun m _ => hE (cn m)
    _ = ENNReal.ofReal ((T.card : ℝ) * U) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hr3 : 0 < (r / 2) ^ 3 := by positivity
        have hT' : (T.card : ℝ) ≤ (2 * (A + r)) ^ 2 * (β - α + 2 * r) / (r / 2) ^ 3 := by
          rw [le_div_iff₀ hr3]; exact hTcard
        have e : (2 * (A + r)) ^ 2 * (β - α + 2 * r) / (r / 2) ^ 3 =
            8 * (2 * (A + r)) ^ 2 * (β - α + 2 * r) / r ^ 3 := by field_simp; ring
        rw [e] at hT'
        exact mul_le_mul_of_nonneg_right hT' hU

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
