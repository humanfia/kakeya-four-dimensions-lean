-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TSBalance.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSCubes

/-!
# Balanced cover by dyadic pigeonholing over grid cubes

The fine mass is split over the grid cubes reached by the contracted shading. Cubes of
tiny density carry little mass; among the dyadic density levels one level carries a
`1 / (L + 1)` fraction of the rest. Restricting to its cubes gives comparable densities
in every reached cube.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical

/-- Density of a set in a grid cube. -/
noncomputable def cubeDensity (s : ℝ) (E : Set Space) (m : Fin 3 → ℤ) : ℝ :=
  (volume (E ∩ gridCube s m)).toReal / s ^ 3

/-- Cubes of dyadic density level `l`. -/
noncomputable def levelCubes (β s : ℝ) (K : ℕ) (E : Set Space) (l : ℕ) :
    Finset (Fin 3 → ℤ) :=
  (cubeBox K).filter (fun m => β ^ (l + 1) < cubeDensity s E m ∧
    cubeDensity s E m ≤ β ^ l)

theorem cubeDensity_le_one {s : ℝ} (hs : 0 < s) (E : Set Space) (m : Fin 3 → ℤ) :
    cubeDensity s E m ≤ 1 := by
  unfold cubeDensity
  rw [div_le_one (by positivity)]
  have h := measure_mono (μ := volume) (inter_subset_right : E ∩ gridCube s m ⊆ gridCube s m)
  rw [volume_gridCube hs, ← ENNReal.ofReal_pow hs.le] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

theorem cubeDensity_nonneg (s : ℝ) (E : Set Space) (m : Fin 3 → ℤ) (hs : 0 < s) :
    0 ≤ cubeDensity s E m := by
  unfold cubeDensity; positivity

/-- Every cube of positive density lies in exactly one dyadic level or is sparse. -/
theorem exists_level {β s : ℝ} (hs : 0 < s) (E : Set Space) (m : Fin 3 → ℤ) (L : ℕ)
    (hm : β ^ (L + 1) < cubeDensity s E m) :
    ∃ l ≤ L, β ^ (l + 1) < cubeDensity s E m ∧ cubeDensity s E m ≤ β ^ l := by
  have hd1 := cubeDensity_le_one hs E m
  induction L with
  | zero => exact ⟨0, le_rfl, hm, by simpa using hd1⟩
  | succ L ih =>
    by_cases h : β ^ (L + 1) < cubeDensity s E m
    · obtain ⟨l, hl, h1, h2⟩ := ih h
      exact ⟨l, hl.trans (Nat.le_succ _), h1, h2⟩
    · exact ⟨L + 1, le_rfl, hm, le_of_not_gt h⟩

theorem disjoint_smul_of_ne_zero {c : ℝ} (hc : c ≠ 0) {A B : Set Space} (h : Disjoint A B) :
    Disjoint (c • A) (c • B) := by
  rw [Set.disjoint_left]
  rintro p ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have : b = a := by
    have := congrArg (fun q => c⁻¹ • q) hab
    simpa [smul_smul, inv_mul_cancel₀ hc] using this
  rw [this] at hb
  exact Set.disjoint_left.mp h ha hb

/-- Fine mass of a cube. -/
noncomputable def cubeMass {n : ℕ} (lam s : ℝ) (Z : Fin n → Set Space) (m : Fin 3 → ℤ) : ℝ :=
  ∑ i, (volume (Z i ∩ lam⁻¹ • gridCube s m)).toReal

theorem cubeMass_nonneg {n : ℕ} (lam s : ℝ) (Z : Fin n → Set Space) (m : Fin 3 → ℤ) :
    0 ≤ cubeMass lam s Z m :=
  Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

/-- The mass of a finite union of cubes is the sum of cube masses. -/
theorem sum_volume_inter_iUnion {n : ℕ} {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s)
    {Z : Fin n → Set Space} (hZ : ∀ i, MeasurableSet (Z i)) (hZfin : ∀ i, volume (Z i) ≠ ⊤)
    (S : Finset (Fin 3 → ℤ)) :
    ∑ i, (volume (Z i ∩ lam⁻¹ • ⋃ m ∈ S, gridCube s m)).toReal =
      ∑ m ∈ S, cubeMass lam s Z m := by
  unfold cubeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he : Z i ∩ lam⁻¹ • ⋃ m ∈ S, gridCube s m = ⋃ m ∈ S, (Z i ∩ lam⁻¹ • gridCube s m) := by
    rw [Set.smul_set_iUnion₂, inter_iUnion₂]
  rw [he, measure_biUnion_finset]
  · rw [ENNReal.toReal_sum]
    intro m _
    exact ne_top_of_le_ne_top (hZfin i) (measure_mono inter_subset_left)
  · intro m _ m' _ hmm
    apply Disjoint.mono inter_subset_right inter_subset_right
    exact disjoint_smul_of_ne_zero (inv_ne_zero hlam.ne') (gridCube_disjoint hs hmm)
  · intro m _
    exact (hZ i).inter ((measurableSet_gridCube s m).const_smul₀ lam⁻¹)

theorem smul_inv_smul_set {c : ℝ} (hc : c ≠ 0) (A : Set Space) : c • c⁻¹ • A = A := by
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Dyadic pigeonholing of densities over grid cubes. -/
theorem balanced_refinement {n : ℕ} {ρ β : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 100)
    (hβ : 0 < β)
    {Z : Fin n → Set Space} (hZ : ∀ i, MeasurableSet (Z i)) (hZball : ∀ i, Z i ⊆ ball 0 1)
    (K : ℕ) (hK : 2 / ρ + 1 ≤ K) (L : ℕ) :
    ∃ (l : ℕ) (S : Set Space), MeasurableSet S ∧
      (∑ i, (volume (Z i)).toReal -
          (cubeBox K).card * (n * 8 * ρ ^ 3 * β ^ (L + 1))) / (L + 1) ≤
        ∑ i, (volume (Z i ∩ S)).toReal ∧
      ∀ m, (gridCube ρ m ∩ (1 - 2 * (16 * ρ)) • ⋃ i, (Z i ∩ S)).Nonempty →
        ENNReal.ofReal (β ^ (l + 1)) * volume (gridCube ρ m) ≤
          volume (((1 - 2 * (16 * ρ)) • ⋃ i, (Z i ∩ S)) ∩ gridCube ρ m) ∧
        volume (((1 - 2 * (16 * ρ)) • ⋃ i, (Z i ∩ S)) ∩ gridCube ρ m) ≤
          ENNReal.ofReal (β⁻¹ * β ^ (l + 1)) * volume (gridCube ρ m) := by
  classical
  set lam : ℝ := 1 - 2 * (16 * ρ) with hlam_def
  have hl0 : 0 < lam := by rw [hlam_def]; linarith
  have hl1 : lam ≤ 1 := by rw [hlam_def]; linarith
  have hlh : 1 / 2 ≤ lam := by rw [hlam_def]; linarith
  set E : Set Space := lam • ⋃ i, Z i with hE_def
  have hZfin : ∀ i, volume (Z i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (hZball i))
  set box := cubeBox K
  -- the total mass is the sum of cube masses over the box
  have hcover : ∀ i, Z i ⊆ lam⁻¹ • ⋃ m ∈ box, gridCube ρ m := by
    intro i p hp
    have hlp : lam • p ∈ ball (0 : Space) 2 := by
      have h1 := hZball i hp
      rw [mem_ball_zero_iff] at h1 ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
      nlinarith [norm_nonneg p]
    have hm := mem_reachedF hρ hK (A := {lam • p}) (by simpa using hlp)
      ⟨lam • p, mem_gridCube_cubeIndex hρ _, rfl⟩
    refine ⟨lam • p, mem_iUnion₂.mpr ⟨cubeIndex ρ (lam • p),
      (Finset.mem_filter.mp hm).1, mem_gridCube_cubeIndex hρ _⟩, ?_⟩
    simp only [smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]
  have htotal : ∑ i, (volume (Z i)).toReal = ∑ m ∈ box, cubeMass lam ρ Z m := by
    rw [← sum_volume_inter_iUnion hl0 hρ hZ hZfin box]
    apply Finset.sum_congr rfl
    intro i _
    rw [inter_eq_left.mpr (hcover i)]
  -- cube masses are controlled by densities
  have hmass_le : ∀ m, cubeMass lam ρ Z m ≤ n * 8 * ρ ^ 3 * cubeDensity ρ E m := by
    intro m
    have hU : (⋃ i, Z i) ∩ lam⁻¹ • gridCube ρ m = lam⁻¹ • (E ∩ gridCube ρ m) := by
      rw [hE_def, Set.smul_set_inter₀ (inv_ne_zero hl0.ne'), smul_smul,
        inv_mul_cancel₀ hl0.ne', one_smul]
    have hvol : (volume ((⋃ i, Z i) ∩ lam⁻¹ • gridCube ρ m)).toReal ≤
        8 * (volume (E ∩ gridCube ρ m)).toReal := by
      rw [hU, Measure.addHaar_smul, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      rw [abs_of_pos (pow_pos (inv_pos.mpr hl0) 3)]
      have : lam⁻¹ ≤ 2 := by rw [inv_le_comm₀ hl0 (by norm_num)]; linarith
      calc lam⁻¹ ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (inv_nonneg.mpr hl0.le) this 3
        _ = 8 := by norm_num
    have hfinU : volume ((⋃ i, Z i) ∩ lam⁻¹ • gridCube ρ m) ≠ ⊤ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne
        (measure_mono (inter_subset_left.trans (iUnion_subset hZball)))
    unfold cubeMass
    calc ∑ i, (volume (Z i ∩ lam⁻¹ • gridCube ρ m)).toReal
        ≤ ∑ _i : Fin n, (volume ((⋃ i, Z i) ∩ lam⁻¹ • gridCube ρ m)).toReal := by
          apply Finset.sum_le_sum
          intro i _
          exact ENNReal.toReal_mono hfinU
            (measure_mono (inter_subset_inter_left _ (subset_iUnion Z i)))
      _ = n * (volume ((⋃ i, Z i) ∩ lam⁻¹ • gridCube ρ m)).toReal := by simp
      _ ≤ n * (8 * (volume (E ∩ gridCube ρ m)).toReal) :=
          mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg _)
      _ = n * 8 * ρ ^ 3 * cubeDensity ρ E m := by
          unfold cubeDensity
          field_simp
  -- sparse cubes and levels
  set sparse := box.filter (fun m => cubeDensity ρ E m ≤ β ^ (L + 1))
  have hsparse : ∑ m ∈ sparse, cubeMass lam ρ Z m ≤
      box.card * (n * 8 * ρ ^ 3 * β ^ (L + 1)) := by
    calc ∑ m ∈ sparse, cubeMass lam ρ Z m ≤ ∑ _m ∈ sparse, n * 8 * ρ ^ 3 * β ^ (L + 1) := by
          apply Finset.sum_le_sum
          intro m hm
          exact (hmass_le m).trans (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hm).2
            (by positivity))
      _ = sparse.card * (n * 8 * ρ ^ 3 * β ^ (L + 1)) := by simp
      _ ≤ box.card * (n * 8 * ρ ^ 3 * β ^ (L + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hsplit : ∑ m ∈ box, cubeMass lam ρ Z m ≤ ∑ m ∈ sparse, cubeMass lam ρ Z m +
      ∑ l ∈ Finset.range (L + 1), ∑ m ∈ levelCubes β ρ K E l, cubeMass lam ρ Z m := by
    have hpt : ∀ m ∈ box, cubeMass lam ρ Z m ≤
        (if cubeDensity ρ E m ≤ β ^ (L + 1) then cubeMass lam ρ Z m else 0) +
        ∑ l ∈ Finset.range (L + 1),
          (if β ^ (l + 1) < cubeDensity ρ E m ∧ cubeDensity ρ E m ≤ β ^ l
            then cubeMass lam ρ Z m else 0) := by
      intro m hm
      have hnn : ∀ l ∈ Finset.range (L + 1), 0 ≤ (if β ^ (l + 1) < cubeDensity ρ E m ∧
          cubeDensity ρ E m ≤ β ^ l then cubeMass lam ρ Z m else 0) := by
        intro l _; split_ifs <;> simp [cubeMass_nonneg]
      by_cases hd : cubeDensity ρ E m ≤ β ^ (L + 1)
      · rw [if_pos hd]
        have := Finset.sum_nonneg hnn
        linarith
      · push Not at hd
        obtain ⟨l, hl, h1, h2⟩ := exists_level hρ E m L hd
        rw [if_neg (not_le.mpr hd), zero_add]
        have hmem : l ∈ Finset.range (L + 1) := Finset.mem_range.mpr (by omega)
        calc cubeMass lam ρ Z m = (if β ^ (l + 1) < cubeDensity ρ E m ∧
              cubeDensity ρ E m ≤ β ^ l then cubeMass lam ρ Z m else 0) := by
              rw [if_pos ⟨h1, h2⟩]
          _ ≤ _ := Finset.single_le_sum hnn hmem
    calc ∑ m ∈ box, cubeMass lam ρ Z m
        ≤ ∑ m ∈ box, ((if cubeDensity ρ E m ≤ β ^ (L + 1) then cubeMass lam ρ Z m
            else 0) + ∑ l ∈ Finset.range (L + 1),
          (if β ^ (l + 1) < cubeDensity ρ E m ∧ cubeDensity ρ E m ≤ β ^ l
            then cubeMass lam ρ Z m else 0)) := Finset.sum_le_sum hpt
      _ = ∑ m ∈ sparse, cubeMass lam ρ Z m +
          ∑ l ∈ Finset.range (L + 1), ∑ m ∈ levelCubes β ρ K E l, cubeMass lam ρ Z m := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          congr 1
          · rw [Finset.sum_filter]
          · apply Finset.sum_congr rfl
            intro l _
            rw [levelCubes, Finset.sum_filter]
  -- the heaviest level
  obtain ⟨l, hlL, hlmax⟩ := Finset.exists_max_image (Finset.range (L + 1))
    (fun l => ∑ m ∈ levelCubes β ρ K E l, cubeMass lam ρ Z m) ⟨0, by simp⟩
  have hlev : ∑ l ∈ Finset.range (L + 1), ∑ m ∈ levelCubes β ρ K E l, cubeMass lam ρ Z m ≤
      (L + 1) * ∑ m ∈ levelCubes β ρ K E l, cubeMass lam ρ Z m := by
    calc _ ≤ ∑ _l' ∈ Finset.range (L + 1), ∑ m ∈ levelCubes β ρ K E l, cubeMass lam ρ Z m :=
          Finset.sum_le_sum hlmax
      _ = (L + 1) * ∑ m ∈ levelCubes β ρ K E l, cubeMass lam ρ Z m := by simp
  set U := ⋃ m ∈ levelCubes β ρ K E l, gridCube ρ m with hU_def
  refine ⟨l, lam⁻¹ • U, ?_, ?_, ?_⟩
  · exact (Finset.measurableSet_biUnion _ (fun m _ => measurableSet_gridCube ρ m)).const_smul₀ _
  · rw [sum_volume_inter_iUnion hl0 hρ hZ hZfin, div_le_iff₀ (by positivity)]
    rw [htotal] at *
    have : (∑ m ∈ box, cubeMass lam ρ Z m) - box.card * (n * 8 * ρ ^ 3 * β ^ (L + 1)) ≤
        (L + 1) * ∑ m ∈ levelCubes β ρ K E l, cubeMass lam ρ Z m := by linarith
    linarith
  · intro m hm
    have hset : lam • ⋃ i, (Z i ∩ lam⁻¹ • U) = E ∩ U := by
      rw [← iUnion_inter, Set.smul_set_inter₀ hl0.ne', smul_inv_smul_set hl0.ne']
    rw [hset] at hm ⊢
    obtain ⟨q, hqm, hqE, hqU⟩ := hm
    obtain ⟨m', hm', hqm'⟩ := mem_iUnion₂.mp hqU
    have hmm : m = m' := by
      by_contra hne
      exact Set.disjoint_left.mp (gridCube_disjoint hρ hne) hqm hqm'
    rw [← hmm] at hm'
    have hcubeU : gridCube ρ m ⊆ U := fun p hp => mem_iUnion₂.mpr ⟨m, hm', hp⟩
    have hEU : E ∩ U ∩ gridCube ρ m = E ∩ gridCube ρ m := by
      ext p
      constructor
      · rintro ⟨⟨hpE, -⟩, hpm⟩; exact ⟨hpE, hpm⟩
      · rintro ⟨hpE, hpm⟩; exact ⟨⟨hpE, hcubeU hpm⟩, hpm⟩
    rw [hEU]
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hm'
    have hfin : volume (E ∩ gridCube ρ m) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [volume_gridCube hρ]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (measure_mono inter_subset_right)
    have hvolE : volume (E ∩ gridCube ρ m) = ENNReal.ofReal (cubeDensity ρ E m * ρ ^ 3) := by
      unfold cubeDensity
      rw [div_mul_cancel₀ _ (by positivity), ENNReal.ofReal_toReal hfin]
    rw [hvolE, volume_gridCube hρ, ← ENNReal.ofReal_pow hρ.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    constructor
    · apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right h1.le (by positivity)
    · apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc cubeDensity ρ E m ≤ β ^ l := h2
        _ = β⁻¹ * β ^ (l + 1) := by rw [pow_succ]; field_simp

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
