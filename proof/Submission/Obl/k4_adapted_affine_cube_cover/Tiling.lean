import Mathlib

/-!
# Middle-half lattice tiles for `Submission.k4_adapted_affine_cube_cover`

Given a basis `b` of `EuclideanSpace ℝ (Fin n)` with `‖b i‖ ≤ 1`, a scale `η > 0` with
`n * η ≤ 1/8` and a centre `c`, we build finitely many pairwise disjoint affine cubes
`a + η • b([0,1]^n)` inside `ball c 1` whose total volume is at least
`2^(-n) * volume (ball c (1/4))`: tile the space by the cells `2η • b(z + [0,1]^n)`, `z ∈ ℤ^n`,
keep the cells lying in `ball c 1` (they cover `ball c (1/4)`, since a cell has diameter at most
`2nη ≤ 1/4`), and take the closed middle half of each kept cell.

Written by session x0172 for o052.
-/

namespace Submission.Obl.k4_adapted_affine_cube_cover

open MeasureTheory Set
open scoped Pointwise

variable {n : ℕ}

/-- The affine cube `a + s • b([0,1]^n)`, written exactly as the tiles of the frozen statement. -/
def affCube (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n))
    (s : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun t : Fin n → ℝ => a + s • (∑ i : Fin n, t i • b i)) '' Set.Icc (0 : Fin n → ℝ) 1

theorem isCompact_affCube (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (s : ℝ) : IsCompact (affCube b a s) :=
  isCompact_Icc.image (by fun_prop)

theorem measurableSet_affCube (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (s : ℝ) : MeasurableSet (affCube b a s) :=
  (isCompact_affCube b a s).isClosed.measurableSet

theorem mem_affCube {b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} {s : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ affCube b a s ↔ ∀ i, 0 ≤ b.repr (x - a) i ∧ b.repr (x - a) i ≤ s := by
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩ i
    have h : b.repr (a + s • ∑ j, t j • b j - a) i = s * t i := by
      rw [add_sub_cancel_left, map_smul, Finsupp.smul_apply, b.repr_sum_self, smul_eq_mul]
    rw [h]
    have h0 : 0 ≤ t i := ht0 i
    have h1 : t i ≤ 1 := ht1 i
    exact ⟨mul_nonneg hs.le h0, by nlinarith⟩
  · intro h
    refine ⟨fun i => b.repr (x - a) i / s,
      ⟨fun i => div_nonneg (h i).1 hs.le, fun i => (div_le_one hs).2 (h i).2⟩, ?_⟩
    have hsum : ∑ i, (b.repr (x - a) i / s) • b i = s⁻¹ • (x - a) := by
      calc ∑ i, (b.repr (x - a) i / s) • b i = s⁻¹ • ∑ i, b.repr (x - a) i • b i := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [smul_smul, div_eq_inv_mul]
        _ = s⁻¹ • (x - a) := by rw [b.sum_repr]
    simp only
    rw [hsum, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]

/-- The linear map `x ↦ ∑ i, x i • b i` of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def frameMap (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  b.equivFun.symm.toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap

theorem frameMap_apply (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : frameMap b x = ∑ i, x i • b i := by
  simp [frameMap, Module.Basis.equivFun_symm_apply]

theorem det_frameMap (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    LinearMap.det (frameMap b) = (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b := by
  set e0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have h := e0.det_comp (frameMap b) e0
  have hB : (frameMap b ∘ e0) = b := by
    funext j
    simp [frameMap_apply, e0]
  rw [hB, Module.Basis.det_self, mul_one] at h
  exact h.symm

theorem affCube_eq_image (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    affCube b a s = (fun y => a + y) '' (s • (frameMap b '' (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1))) := by
  rw [← Set.image_smul, Set.image_image, Set.image_image, Set.image_image, affCube]
  congr 1
  funext t
  simp [frameMap_apply]

theorem volume_affCube (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 ≤ s) :
    volume (affCube b a s) =
      ENNReal.ofReal (s ^ n * |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b|) := by
  have hcube : volume (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1) = 1 := by
    rw [Set.image_eq_preimage_of_inverse (f := WithLp.toLp 2) (g := WithLp.ofLp)
      (fun x => WithLp.ofLp_toLp 2 x) (fun x => WithLp.toLp_ofLp 2 x),
      (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi]
    simp
  rw [affCube_eq_image, Set.image_add_left, measure_preimage_add, Measure.addHaar_smul,
    Measure.addHaar_image_linearMap, hcube, mul_one, finrank_euclideanSpace_fin, det_frameMap,
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (pow_nonneg hs n)]

theorem volume_affCube_pos (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) : 0 < volume (affCube b a s) := by
  rw [volume_affCube b a hs.le, ENNReal.ofReal_pos]
  have hdet := ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.isUnit_det b).ne_zero
  positivity

/-- Two points of an affine cube of side `s` over a basis of vectors of norm at most one are at
distance at most `n * s`. -/
theorem norm_sub_le_of_mem_affCube {b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))}
    (hb : ∀ i, ‖b i‖ ≤ 1) {a : EuclideanSpace ℝ (Fin n)} {s : ℝ} (hs : 0 < s)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ affCube b a s) (hy : y ∈ affCube b a s) :
    ‖x - y‖ ≤ n * s := by
  rw [mem_affCube hs] at hx hy
  have hr : ∀ i, b.repr (x - y) i = b.repr (x - a) i - b.repr (y - a) i := by
    intro i
    rw [← Finsupp.sub_apply, ← map_sub, sub_sub_sub_cancel_right]
  calc ‖x - y‖ = ‖∑ i, b.repr (x - y) i • b i‖ := by rw [b.sum_repr]
    _ ≤ ∑ i, ‖b.repr (x - y) i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, s := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, hr, Real.norm_eq_abs]
        obtain ⟨hx0, hx1⟩ := hx i
        obtain ⟨hy0, hy1⟩ := hy i
        calc |b.repr (x - a) i - b.repr (y - a) i| * ‖b i‖ ≤ s * 1 :=
              mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) (hb i) (norm_nonneg _) hs.le
          _ = s := mul_one s
    _ = n * s := by simp

/-- The anchor `η • b(2z + 1/2)` of the middle-half tile with integer index `z`. -/
noncomputable def anchor (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ)
    (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  ∑ i, (η * (2 * (z i : ℝ) + 1 / 2)) • b i

/-- The corner `2η • b(z)` of the lattice cell with integer index `z`. -/
noncomputable def corner (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ)
    (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  ∑ i, (2 * η * (z i : ℝ)) • b i

theorem repr_sub_anchor (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ)
    (z : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    b.repr (x - anchor b η z) i = b.repr x i - η * (2 * (z i : ℝ) + 1 / 2) := by
  rw [map_sub, Finsupp.sub_apply, anchor, b.repr_sum_self]

theorem repr_sub_corner (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ)
    (z : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    b.repr (x - corner b η z) i = b.repr x i - 2 * η * (z i : ℝ) := by
  rw [map_sub, Finsupp.sub_apply, corner, b.repr_sum_self]

theorem repr_corner (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ)
    (z : Fin n → ℤ) (i : Fin n) : b.repr (corner b η z) i = 2 * η * (z i : ℝ) := by
  rw [corner, b.repr_sum_self]

/-- Finitely many disjoint middle-half tiles `a + η • b([0,1]^n)` inside `ball c 1`; the cells
of side `2η` containing them cover `ball c (1/4)`, so their total volume is at least
`2^(-n) * volume (ball c (1/4))`. -/
theorem exists_tiling (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ i, ‖b i‖ ≤ 1) {η : ℝ} (hη : 0 < η) (hnη : (n : ℝ) * η ≤ 1 / 8)
    (c : EuclideanSpace ℝ (Fin n)) :
    ∃ (k : ℕ) (a : Fin k → EuclideanSpace ℝ (Fin n)),
      (∀ h, affCube b (a h) η ⊆ Metric.ball c 1) ∧
      Pairwise (Function.onFun Disjoint fun h => affCube b (a h) η) ∧
      volume (Metric.ball c (1 / 4)) ≤ 2 ^ n * ∑ h, volume (affCube b (a h) η) := by
  classical
  have h2η : 0 < 2 * η := by positivity
  set cell : (Fin n → ℤ) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun z => affCube b (corner b η z) (2 * η) with hcell
  set tile : (Fin n → ℤ) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun z => affCube b (anchor b η z) η with htile
  have htile_cell : ∀ z, tile z ⊆ cell z := by
    intro z x hx
    simp only [htile, hcell, mem_affCube hη, mem_affCube h2η, repr_sub_anchor,
      repr_sub_corner] at hx ⊢
    intro i
    obtain ⟨h0, h1⟩ := hx i
    constructor <;> nlinarith
  have hdisj : ∀ z w, z ≠ w → Disjoint (tile z) (tile w) := by
    intro z w hzw
    rw [Set.disjoint_left]
    intro x hxz hxw
    apply hzw
    funext i
    simp only [htile, mem_affCube hη, repr_sub_anchor] at hxz hxw
    obtain ⟨hz0, hz1⟩ := hxz i
    obtain ⟨hw0, hw1⟩ := hxw i
    have h1 : (z i : ℝ) < w i + 1 := by nlinarith
    have h2 : (w i : ℝ) < z i + 1 := by nlinarith
    have h1' : z i < w i + 1 := by exact_mod_cast h1
    have h2' : w i < z i + 1 := by exact_mod_cast h2
    omega
  have hcover : ∀ x ∈ Metric.ball c (1 / 4), ∃ z, x ∈ cell z ∧ cell z ⊆ Metric.ball c 1 := by
    intro x hx
    set z : Fin n → ℤ := fun i => ⌊b.repr x i / (2 * η)⌋ with hz
    have hxz : x ∈ cell z := by
      simp only [hcell, mem_affCube h2η, repr_sub_corner]
      intro i
      have h1 := Int.floor_le (b.repr x i / (2 * η))
      have h2 := Int.lt_floor_add_one (b.repr x i / (2 * η))
      rw [le_div_iff₀ h2η] at h1
      rw [div_lt_iff₀ h2η] at h2
      simp only [hz]
      constructor <;> nlinarith
    refine ⟨z, hxz, ?_⟩
    intro y hy
    have hd := norm_sub_le_of_mem_affCube hb h2η hy hxz
    rw [Metric.mem_ball] at hx ⊢
    calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
      _ < 1 := by rw [dist_eq_norm y x]; nlinarith
  let Z : Set (Fin n → ℤ) := {z | cell z ⊆ Metric.ball c 1}
  have hZ : Z.Finite := by
    obtain ⟨R, hR⟩ := (isCompact_closedBall c 1).exists_bound_of_continuousOn
      (b.equivFun.toLinearMap.continuous_of_finiteDimensional).continuousOn
    let M : ℤ := ⌈R / (2 * η)⌉
    refine (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-M) M)
      fun _ => Set.finite_Icc _ _).subset ?_
    intro z hz
    have hcz : corner b η z ∈ cell z := by
      simp only [hcell, mem_affCube h2η, sub_self, map_zero, Finsupp.coe_zero, Pi.zero_apply,
        le_refl, true_and]
      intro i
      positivity
    have hRz := hR _ (Metric.ball_subset_closedBall (hz hcz))
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have hi : |2 * η * (z i : ℝ)| ≤ R := by
      have h := norm_le_pi_norm (b.equivFun.toLinearMap (corner b η z)) i
      simp only [LinearEquiv.coe_coe, Module.Basis.equivFun_apply, repr_corner,
        Real.norm_eq_abs] at h
      exact h.trans hRz
    have hzi : |(z i : ℝ)| ≤ R / (2 * η) := by
      rw [le_div_iff₀ h2η]
      rw [abs_mul, abs_of_pos h2η] at hi
      linarith
    have hM : R / (2 * η) ≤ (M : ℝ) := Int.le_ceil _
    constructor
    · have : -(M : ℝ) ≤ z i := by linarith [neg_abs_le (z i : ℝ)]
      exact_mod_cast this
    · have : (z i : ℝ) ≤ M := by linarith [le_abs_self (z i : ℝ)]
      exact_mod_cast this
  set F := hZ.toFinset with hF
  let e : Fin F.card ≃ F := F.equivFin.symm
  refine ⟨F.card, fun h => anchor b η (e h).1, ?_, ?_, ?_⟩
  · intro h
    have hz : (e h).1 ∈ Z := hZ.mem_toFinset.mp (e h).2
    exact (htile_cell _).trans hz
  · intro h h' hne
    apply hdisj
    intro heq
    exact hne (e.injective (Subtype.ext heq))
  · have hcov : Metric.ball c (1 / 4) ⊆ ⋃ z ∈ F, cell z := by
      intro x hx
      obtain ⟨z, hxz, hz⟩ := hcover x hx
      exact Set.mem_biUnion (hZ.mem_toFinset.mpr hz) hxz
    have hvol : ∀ z, volume (cell z) = 2 ^ n * volume (tile z) := by
      intro z
      simp only [hcell, htile]
      rw [volume_affCube _ _ h2η.le, volume_affCube _ _ hη.le, mul_pow, mul_assoc,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]
    calc volume (Metric.ball c (1 / 4)) ≤ volume (⋃ z ∈ F, cell z) := measure_mono hcov
      _ ≤ ∑ z ∈ F, volume (cell z) := measure_biUnion_finset_le F cell
      _ = ∑ z ∈ F, 2 ^ n * volume (tile z) := Finset.sum_congr rfl fun z _ => hvol z
      _ = 2 ^ n * ∑ z ∈ F, volume (tile z) := (Finset.mul_sum _ _ _).symm
      _ = 2 ^ n * ∑ h, volume (affCube b (anchor b η (e h).1) η) := by
          congr 1
          rw [← Finset.sum_coe_sort F, ← e.sum_comp]

end Submission.Obl.k4_adapted_affine_cube_cover
