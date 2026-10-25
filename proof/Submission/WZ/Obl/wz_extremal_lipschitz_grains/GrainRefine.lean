-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainRefine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainCount

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-! ### Shadings made of grid cubes

Coarse shadings are finite unions of half-open grid cubes of side `s`; refinements keep or drop
whole cubes, so volumes are cube counts. -/

/-- The union of the grid cubes with indices in `M`. -/
def cubeSet (s : ℝ) (M : Finset (Fin 3 → ℤ)) : Set Space := ⋃ m ∈ M, gridCube s m

theorem measurableSet_cubeSet (s : ℝ) (M : Finset (Fin 3 → ℤ)) : MeasurableSet (cubeSet s M) :=
  Finset.measurableSet_biUnion _ fun m _ => measurableSet_gridCube s m

theorem mem_cubeSet {s : ℝ} (hs : 0 < s) {M : Finset (Fin 3 → ℤ)} {p : Space} :
    p ∈ cubeSet s M ↔ cubeIndex s p ∈ M := by
  constructor
  · intro hp
    obtain ⟨m, hm, hpm⟩ := mem_iUnion₂.1 hp
    rwa [cubeIndex_eq_of_mem hs hpm]
  · intro hp
    exact mem_iUnion₂.2 ⟨_, hp, mem_gridCube_cubeIndex hs p⟩

theorem cubeSet_mono {s : ℝ} {M M' : Finset (Fin 3 → ℤ)} (h : M ⊆ M') :
    cubeSet s M ⊆ cubeSet s M' :=
  biUnion_subset_biUnion_left (by exact_mod_cast h)

theorem volume_cubeSet {s : ℝ} (hs : 0 < s) (M : Finset (Fin 3 → ℤ)) :
    volume (cubeSet s M) = M.card * ENNReal.ofReal s ^ 3 := by
  rw [cubeSet, measure_biUnion_finset (fun m _ m' _ hmm => gridCube_disjoint hs hmm)
    (fun m _ => measurableSet_gridCube s m)]
  simp only [volume_gridCube hs, Finset.sum_const, nsmul_eq_mul]

/-- The multiplicity of a family of cube sets at a cube. -/
noncomputable def cubeLabels {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (m : Fin 3 → ℤ) : ℕ :=
  (Finset.univ.filter fun j => m ∈ M j).card

theorem fineMult_cubeSet {s : ℝ} (hs : 0 < s) {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ))
    (p : Space) : fineMult (fun j => cubeSet s (M j)) p = cubeLabels M (cubeIndex s p) := by
  classical
  rw [fineMult, cubeLabels, ← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [mem_cubeSet hs]

/-- **Trimming**: keep the cubes of multiplicity at least `μ`. -/
noncomputable def trimCubes {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (μ : ℝ) :
    Fin k → Finset (Fin 3 → ℤ) :=
  fun j => (M j).filter fun m => μ ≤ (cubeLabels M m : ℝ)

theorem trimCubes_subset {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (μ : ℝ) (j : Fin k) :
    trimCubes M μ j ⊆ M j := Finset.filter_subset _ _

theorem cubeLabels_trimCubes {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (μ : ℝ) {m : Fin 3 → ℤ}
    (hm : μ ≤ (cubeLabels M m : ℝ)) : cubeLabels (trimCubes M μ) m = cubeLabels M m := by
  classical
  unfold cubeLabels trimCubes
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩

/-- At a kept cube the multiplicity is at least the threshold. -/
theorem le_cubeLabels_trimCubes {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (μ : ℝ) {j : Fin k}
    {m : Fin 3 → ℤ} (hm : m ∈ trimCubes M μ j) : μ ≤ (cubeLabels (trimCubes M μ) m : ℝ) := by
  have h := (Finset.mem_filter.1 hm).2
  rw [cubeLabels_trimCubes M μ h]
  exact h

/-- The cube count lost by trimming is at most `μ` times the number of cubes in the union. -/
theorem card_trimCubes_ge {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) {μ : ℝ} (hμ : 0 ≤ μ) :
    (∑ j, ((M j).card : ℝ)) - μ * ((Finset.univ.biUnion M).card : ℝ) ≤
      ∑ j, ((trimCubes M μ j).card : ℝ) := by
  classical
  -- double counting over the union of the cube sets
  set U := Finset.univ.biUnion M with hU
  have hcount : ∀ (N : Fin k → Finset (Fin 3 → ℤ)), (∀ j, N j ⊆ M j) →
      ∑ j, ((N j).card : ℝ) = ∑ m ∈ U, (cubeLabels N m : ℝ) := by
    intro N hN
    have h1 : ∀ j, ((N j).card : ℝ) = ∑ m ∈ U, if m ∈ N j then (1 : ℝ) else 0 := by
      intro j
      rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2
      apply (Finset.inter_eq_right.2 _).symm
      intro m hm
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hN j hm⟩
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [cubeLabels, Finset.sum_boole]
  rw [hcount M (fun j => subset_rfl), hcount (trimCubes M μ) (trimCubes_subset M μ),
    show ((U.card : ℕ) : ℝ) = ∑ _m ∈ U, (1 : ℝ) by simp]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro m _
  by_cases hm : μ ≤ (cubeLabels M m : ℝ)
  · rw [cubeLabels_trimCubes M μ hm]
    linarith
  · push Not at hm
    have : (0 : ℝ) ≤ (cubeLabels (trimCubes M μ) m : ℝ) := Nat.cast_nonneg _
    linarith

/-! ### Blocks of grid cubes -/

/-- The block of `N × N × N` grid cubes containing a cube index. -/
def blockOf (N : ℕ) (m : Fin 3 → ℤ) : Fin 3 → ℤ := fun c => m c / (N : ℤ)

/-- The grid cube of side `N s` containing a point is the block of its grid cube of side `s`. -/
theorem cubeIndex_mul {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (p : Space) :
    cubeIndex ((N : ℝ) * s) p = blockOf N (cubeIndex s p) := by
  funext c
  simp only [cubeIndex, blockOf]
  rw [← Int.floor_div_natCast]
  congr 1
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **Density refinement** (property (P)): keep the cubes lying in blocks that contain at least
`θ` cubes of the set. -/
noncomputable def denseCubes {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (N : ℕ) (θ : ℝ) :
    Fin k → Finset (Fin 3 → ℤ) :=
  fun j => (M j).filter fun m =>
    θ ≤ (((M j).filter fun m' => blockOf N m' = blockOf N m).card : ℝ)

theorem denseCubes_subset {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (N : ℕ) (θ : ℝ) (j : Fin k) :
    denseCubes M N θ j ⊆ M j := Finset.filter_subset _ _

/-- In every block a kept cube set is either empty or has at least `θ` cubes. -/
theorem denseCubes_block {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (N : ℕ) (θ : ℝ) (j : Fin k)
    (B : Fin 3 → ℤ) (hne : ((denseCubes M N θ j).filter fun m => blockOf N m = B).Nonempty) :
    θ ≤ (((denseCubes M N θ j).filter fun m => blockOf N m = B).card : ℝ) := by
  classical
  obtain ⟨m, hm⟩ := hne
  rw [Finset.mem_filter] at hm
  obtain ⟨hmD, hmB⟩ := hm
  have hθ := (Finset.mem_filter.1 hmD).2
  have heq : ((denseCubes M N θ j).filter fun m => blockOf N m = B) =
      (M j).filter fun m' => blockOf N m' = blockOf N m := by
    ext m'
    simp only [denseCubes, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm', -⟩, hB⟩; exact ⟨hm', by rw [hB, hmB]⟩
    · rintro ⟨hm', hB⟩
      refine ⟨⟨hm', ?_⟩, by rw [hB, hmB]⟩
      have e : ((M j).filter fun m'' => blockOf N m'' = blockOf N m') =
          (M j).filter fun m'' => blockOf N m'' = blockOf N m := by rw [hB]
      rw [e]; exact hθ
  rw [heq]; exact hθ

/-- The cube count lost by the density refinement is at most `θ` per occupied block. -/
theorem card_denseCubes_ge {k : ℕ} (M : Fin k → Finset (Fin 3 → ℤ)) (N : ℕ) {θ : ℝ} (hθ : 0 ≤ θ)
    (j : Fin k) :
    ((M j).card : ℝ) - θ * (((M j).image (blockOf N)).card : ℝ) ≤
      ((denseCubes M N θ j).card : ℝ) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := M j) (fun m =>
    θ ≤ (((M j).filter fun m' => blockOf N m' = blockOf N m).card : ℝ))
  have hlost : (((M j).filter fun m => ¬ θ ≤
      (((M j).filter fun m' => blockOf N m' = blockOf N m).card : ℝ)).card : ℝ) ≤
      θ * (((M j).image (blockOf N)).card : ℝ) := by
    set Sp := ((M j).image (blockOf N)).filter fun B =>
      ¬ θ ≤ (((M j).filter fun m' => blockOf N m' = B).card : ℝ) with hSp
    have hsub : ((M j).filter fun m => ¬ θ ≤
        (((M j).filter fun m' => blockOf N m' = blockOf N m).card : ℝ)) ⊆
        Sp.biUnion fun B => (M j).filter fun m' => blockOf N m' = B := by
      intro m hm
      rw [Finset.mem_filter] at hm
      exact Finset.mem_biUnion.2 ⟨blockOf N m, Finset.mem_filter.2
        ⟨Finset.mem_image_of_mem _ hm.1, hm.2⟩, Finset.mem_filter.2 ⟨hm.1, rfl⟩⟩
    calc _ ≤ (((Sp.biUnion fun B => (M j).filter fun m' => blockOf N m' = B)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ B ∈ Sp, (((M j).filter fun m' => blockOf N m' = B).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _B ∈ Sp, θ := by
          apply Finset.sum_le_sum
          intro B hB
          exact le_of_lt (not_le.1 (Finset.mem_filter.1 hB).2)
      _ = Sp.card * θ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ θ * (((M j).image (blockOf N)).card : ℝ) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_filter_le _ _) hθ
  have : ((M j).card : ℝ) = ((denseCubes M N θ j).card : ℝ) + (((M j).filter fun m => ¬ θ ≤
      (((M j).filter fun m' => blockOf N m' = blockOf N m).card : ℝ)).card : ℝ) := by
    rw [denseCubes]; exact_mod_cast hsplit.symm
  linarith

/-! ### Saturation of a measurable refinement -/

/-- **Saturation**: the cubes of `M j` in which `Z j` occupies at least the fraction `c`. -/
noncomputable def satCubes {k : ℕ} (s : ℝ) (M : Fin k → Finset (Fin 3 → ℤ))
    (Z : Fin k → Set Space) (c : ℝ) : Fin k → Finset (Fin 3 → ℤ) :=
  fun j => (M j).filter fun m => ENNReal.ofReal (c * s ^ 3) ≤ volume (Z j ∩ gridCube s m)

theorem satCubes_subset {k : ℕ} (s : ℝ) (M : Fin k → Finset (Fin 3 → ℤ))
    (Z : Fin k → Set Space) (c : ℝ) (j : Fin k) : satCubes s M Z c j ⊆ M j :=
  Finset.filter_subset _ _

open Classical in
/-- Pointwise counting bounds for `Z` pass to the saturated cubes, divided by `c`. -/
theorem card_satCubes_le {k : ℕ} {s : ℝ} (hs : 0 < s) (M : Fin k → Finset (Fin 3 → ℤ))
    {Z : Fin k → Set Space} (hZ : ∀ j, MeasurableSet (Z j)) {c B : ℝ} (hc : 0 < c)
    (L : Finset (Fin k)) (hB : ∀ x, ((L.filter fun j => x ∈ Z j).card : ℝ) ≤ B)
    (m : Fin 3 → ℤ) : ((L.filter fun j => m ∈ satCubes s M Z c j).card : ℝ) ≤ B / c := by
  classical
  set Q := gridCube s m
  have hQm : MeasurableSet Q := measurableSet_gridCube s m
  have hQv : volume Q = ENNReal.ofReal (s ^ 3) := by
    rw [volume_gridCube hs, ENNReal.ofReal_pow hs.le]
  set L' := L.filter fun j => m ∈ satCubes s M Z c j
  have hB0 : 0 ≤ B := le_trans (Nat.cast_nonneg _) (hB 0)
  -- lower bound
  have h1 : (L'.card : ℝ≥0∞) * ENNReal.ofReal (c * s ^ 3) ≤ ∑ j ∈ L, volume (Z j ∩ Q) := by
    calc (L'.card : ℝ≥0∞) * ENNReal.ofReal (c * s ^ 3) = ∑ _j ∈ L', ENNReal.ofReal (c * s ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ L', volume (Z j ∩ Q) := by
          apply Finset.sum_le_sum
          intro j hj
          exact (Finset.mem_filter.1 (Finset.mem_filter.1 hj).2).2
      _ ≤ ∑ j ∈ L, volume (Z j ∩ Q) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => zero_le)
  -- upper bound by integrating the pointwise count
  have h2 : ∑ j ∈ L, volume (Z j ∩ Q) ≤ ENNReal.ofReal B * volume Q := by
    have e : ∀ j ∈ L, volume (Z j ∩ Q) = ∫⁻ x in Q, (Z j).indicator 1 x := by
      intro j _
      rw [lintegral_indicator_one (hZ j), Measure.restrict_apply (hZ j)]
    rw [Finset.sum_congr rfl e, ← lintegral_finset_sum _ (fun j _ =>
      (measurable_one.indicator (hZ j)))]
    calc ∫⁻ x in Q, ∑ j ∈ L, (Z j).indicator 1 x ≤ ∫⁻ _x in Q, ENNReal.ofReal B := by
          apply lintegral_mono
          intro x
          have hx := hB x
          calc ∑ j ∈ L, (Z j).indicator 1 x = ((L.filter fun j => x ∈ Z j).card : ℝ≥0∞) := by
                rw [Finset.card_filter, Nat.cast_sum]
                apply Finset.sum_congr rfl
                intro j _
                by_cases h : x ∈ Z j <;> simp [h]
            _ ≤ ENNReal.ofReal B := by
                rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hx
      _ = ENNReal.ofReal B * volume Q := by rw [setLIntegral_const]
  have h3 := h1.trans h2
  rw [hQv, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul hB0] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  rw [le_div_iff₀ hc]
  have hs3 : 0 < s ^ 3 := by positivity
  nlinarith

/-- The volume of `Z` outside the saturated cubes is at most `c` times the cube volume. -/
theorem volume_le_satCubes {k : ℕ} {s : ℝ} (hs : 0 < s) (M : Fin k → Finset (Fin 3 → ℤ))
    {Z : Fin k → Set Space} (hZ : ∀ j, Z j ⊆ cubeSet s (M j)) {c : ℝ} (hc : 0 ≤ c)
    (j : Fin k) :
    (volume (Z j)).toReal ≤ ((satCubes s M Z c j).card : ℝ) * s ^ 3 +
      c * ((M j).card : ℝ) * s ^ 3 := by
  classical
  have hcov : Z j ⊆ ⋃ m ∈ M j, Z j ∩ gridCube s m := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.1 (hZ j hx)
    exact mem_iUnion₂.2 ⟨m, hm, hx, hxm⟩
  have hfin : ∀ m, volume (Z j ∩ gridCube s m) ≤ ENNReal.ofReal (s ^ 3) := by
    intro m
    calc volume (Z j ∩ gridCube s m) ≤ volume (gridCube s m) := measure_mono inter_subset_right
      _ = ENNReal.ofReal (s ^ 3) := by rw [volume_gridCube hs, ENNReal.ofReal_pow hs.le]
  have h1 : volume (Z j) ≤ ∑ m ∈ M j, volume (Z j ∩ gridCube s m) :=
    (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
  have h2 : ∑ m ∈ M j, volume (Z j ∩ gridCube s m) ≤
      ∑ m ∈ M j, (if m ∈ satCubes s M Z c j then ENNReal.ofReal (s ^ 3)
        else ENNReal.ofReal (c * s ^ 3)) := by
    apply Finset.sum_le_sum
    intro m hm
    split_ifs with h
    · exact hfin m
    · have : ¬ ENNReal.ofReal (c * s ^ 3) ≤ volume (Z j ∩ gridCube s m) := by
        intro h'; exact h (Finset.mem_filter.2 ⟨hm, h'⟩)
      exact (not_le.1 this).le
  have h3 : ∑ m ∈ M j, (if m ∈ satCubes s M Z c j then ENNReal.ofReal (s ^ 3)
        else ENNReal.ofReal (c * s ^ 3)) ≤
      ENNReal.ofReal (((satCubes s M Z c j).card : ℝ) * s ^ 3 + c * ((M j).card : ℝ) * s ^ 3) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have e : (M j).filter (fun m => m ∈ satCubes s M Z c j) = satCubes s M Z c j := by
      ext m; simp only [Finset.mem_filter, satCubes]; tauto
    rw [e, ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
    · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have : (((M j).filter fun m => m ∉ satCubes s M Z c j).card : ℝ) ≤ (M j).card := by
        exact_mod_cast Finset.card_filter_le _ _
      have hcs : 0 ≤ c * s ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hcs]
  have h4 := (h1.trans h2).trans h3
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h4

/-! ### Block geometry -/

theorem cubeSet_inter_block {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (M : Finset (Fin 3 → ℤ))
    (B : Fin 3 → ℤ) :
    cubeSet s M ∩ gridCube ((N : ℝ) * s) B = cubeSet s (M.filter fun m => blockOf N m = B) := by
  have hNs : 0 < (N : ℝ) * s := mul_pos (by exact_mod_cast hN) hs
  ext p
  rw [mem_inter_iff, mem_cubeSet hs, mem_cubeSet hs, mem_gridCube_iff hNs, cubeIndex_mul hs hN,
    Finset.mem_filter]

theorem gridCube_subset_block {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (m : Fin 3 → ℤ) :
    gridCube s m ⊆ gridCube ((N : ℝ) * s) (blockOf N m) := by
  have hNs : 0 < (N : ℝ) * s := mul_pos (by exact_mod_cast hN) hs
  intro p hp
  rw [mem_gridCube_iff hNs, cubeIndex_mul hs hN, cubeIndex_eq_of_mem hs hp]

/-- A cube set inside an `r`-tube meets at most `3456 / ω` blocks of side `ω = N s ≥ r`. -/
theorem card_blocks_le {s r : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) {z w : Space}
    (hw : ‖w‖ = 1) {M : Finset (Fin 3 → ℤ)} (hM : cubeSet s M ⊆ tube r z w)
    (hr : r ≤ (N : ℝ) * s) (h3 : 3 * ((N : ℝ) * s) ≤ 1) :
    ((M.image (blockOf N)).card : ℝ) ≤ 3456 / ((N : ℝ) * s) := by
  classical
  set ω := (N : ℝ) * s with hω
  have hω0 : 0 < ω := mul_pos (by exact_mod_cast hN) hs
  -- every occupied block lies in the `3 ω`-tube
  have hsub : ∀ B ∈ M.image (blockOf N), gridCube ω B ⊆ tube (3 * ω) z w := by
    intro B hB y hy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hB
    have hc := corner_mem_gridCube hs m
    have hcT : (WithLp.toLp 2 fun j => s * (m j : ℝ) : Space) ∈ tube r z w :=
      hM (mem_iUnion₂.2 ⟨m, hm, hc⟩)
    have hcB := gridCube_subset_block hs hN m hc
    have hd := diam_le_of_mem_gridCube hω0 hy hcB
    obtain ⟨q, hq, hcq⟩ := mem_thickening_iff.1 hcT
    refine mem_thickening_iff.2 ⟨q, hq, ?_⟩
    calc dist y q ≤ dist y _ + dist _ q := dist_triangle _ _ _
      _ < 2 * ω + r := add_lt_add hd hcq
      _ ≤ 3 * ω := by linarith
  have hdisj : (↑(M.image (blockOf N)) : Set (Fin 3 → ℤ)).PairwiseDisjoint (gridCube ω) :=
    fun B _ B' _ hBB => gridCube_disjoint hω0 hBB
  have h1 : ∑ B ∈ M.image (blockOf N), volume (gridCube ω B) ≤ volume (tube (3 * ω) z w) := by
    rw [← measure_biUnion_finset hdisj (fun B _ => measurableSet_gridCube ω B)]
    exact measure_mono (iUnion₂_subset hsub)
  have h2 := WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le (by positivity : 0 < 3 * ω)
    h3 z w hw
  simp only [volume_gridCube hω0, Finset.sum_const, nsmul_eq_mul] at h1
  have h4 := h1.trans h2
  rw [← ENNReal.ofReal_pow hω0.le, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h4
  have h5 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4
  rw [le_div_iff₀ hω0]
  have hω3 : 0 < ω ^ 3 := by positivity
  nlinarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
