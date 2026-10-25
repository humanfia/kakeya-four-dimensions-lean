-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Count.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Hyp

/-!
# The volume of the coarse set

The coarse set of row `m` consists of the cubes meeting the fine slice at the representative
height `zrep m`. Since at most `N` shadings meet a cube and every slice of a shading of a
non-horizontal tube has area at most `24 δ² / θ²`, the number of these cubes is at least the
fine slice mass divided by `N · 24 δ² / θ²`. Choosing `zrep m` with at least half the average
slice mass of the row gives a lower bound for the volume of the coarse set in terms of the fine
mass in the rows.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- A row of the grid. -/
def row (s : ℝ) (m : ℤ) : Set ℝ := Ico (s * m) (s * (m + 1))

lemma measurableSet_row (s : ℝ) (m : ℤ) : MeasurableSet (row s m) := measurableSet_Ico

lemma volume_row {s : ℝ} (hs : 0 < s) (m : ℤ) : volume (row s m) = ENNReal.ofReal s := by
  rw [row, Real.volume_Ico]; congr 1; ring

/-- The fine slice of the kept shadings in a region at a height. -/
def fineSlice {n : ℕ} (Y : Fin n → Set Space) (Sk : Finset (Fin n)) (PR : Set Space)
    (z : ℝ) : Set Space :=
  (⋃ i ∈ Sk, Y i ∩ PR) ∩ {p | p 2 = z}

section

variable {σ δ s θ K N : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
  {Eo : Set Space} {f : ℝ → ℝ} {P : Space → Space}

/-- The slice mass of the kept shadings at one height is at most the number of cubes meeting
the fine slice times `N · 24 δ² / θ²`. -/
theorem slice_mass_le_card (hS : FineSetup σ δ s θ K N x v Y Eo f P) (Sk : Finset (Fin n))
    (PR : Set Space) {Kb : ℕ} (hKb : 2 / s + 1 ≤ Kb) (z : ℝ) :
    ∑ i ∈ Sk, sliceArea (Y i ∩ PR) z ≤
      ((Coarse.reachedF s Kb (fineSlice Y Sk PR z)).card : ℝ≥0∞) *
        ENNReal.ofReal (N * (24 * δ ^ 2 / θ ^ 2)) := by
  classical
  have hs := s_pos hS
  set F := fineSlice Y Sk PR z
  set KF := Coarse.reachedF s Kb F
  have hFball : F ⊆ ball 0 2 := by
    intro p hp
    obtain ⟨hp1, -⟩ := hp
    obtain ⟨i, -, hpi, -⟩ := mem_iUnion₂.mp hp1
    exact ball_subset_ball (by norm_num) (hS.Eo_ball (hS.sub_Eo i hpi))
  have hcov := Coarse.subset_iUnion_reachedF hs hKb hFball
  -- each slice is covered by the slices of the cube pieces
  have h1 : ∀ i ∈ Sk, sliceArea (Y i ∩ PR) z ≤
      ∑ k ∈ KF, sliceArea (Y i ∩ Coarse.gridCube s k) z := by
    intro i hi
    rw [← sliceArea_inter_height (Y i ∩ PR) (H := {z}) (mem_singleton z)]
    refine (sliceArea_mono ?_ z).trans (sliceArea_biUnion_le KF _ z)
    intro p hp
    obtain ⟨⟨hpY, hpPR⟩, hpz⟩ := hp
    have hpF : p ∈ F := ⟨mem_iUnion₂.mpr ⟨i, hi, hpY, hpPR⟩, hpz⟩
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp (hcov hpF)
    exact mem_iUnion₂.mpr ⟨k, hk, hpY, hpk⟩
  -- per cube, at most `N` shadings contribute
  have h2 : ∀ k, ∑ i ∈ Sk, sliceArea (Y i ∩ Coarse.gridCube s k) z ≤
      ENNReal.ofReal (N * (24 * δ ^ 2 / θ ^ 2)) := by
    intro k
    set T := Finset.univ.filter (fun i => (Y i ∩ Coarse.gridCube s k).Nonempty)
    have hT : (T.card : ℝ) ≤ N := by
      have := hS.cube k
      rwa [show {i | (Y i ∩ Coarse.gridCube s k).Nonempty} = (T : Set (Fin n)) by
        ext i; simp [T], Set.ncard_coe_finset] at this
    calc ∑ i ∈ Sk, sliceArea (Y i ∩ Coarse.gridCube s k) z
        ≤ ∑ i ∈ T, sliceArea (Y i ∩ Coarse.gridCube s k) z := by
          rw [← Finset.sum_filter_add_sum_filter_not Sk
            (fun i => (Y i ∩ Coarse.gridCube s k).Nonempty)]
          have hz : ∑ i ∈ Sk.filter (fun i => ¬(Y i ∩ Coarse.gridCube s k).Nonempty),
              sliceArea (Y i ∩ Coarse.gridCube s k) z = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hne := (Finset.mem_filter.mp hi).2
            rw [not_nonempty_iff_eq_empty] at hne
            rw [hne]
            exact sliceArea_eq_zero (by simp)
          rw [hz, add_zero]
          apply Finset.sum_le_sum_of_subset
          intro i hi
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (Finset.mem_filter.mp hi).2
      _ ≤ ∑ _i ∈ T, ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          have hne := (Finset.mem_filter.mp hi).2
          have hvθ := hS.vert i (hne.mono inter_subset_left)
          exact sliceArea_le_of_subset_tube hS.δ_pos hS.θ_pos hS.θ_le (hS.v_unit i) hvθ
            (inter_subset_left.trans (hS.sub_tube i)) z
      _ = (T.card : ℝ≥0∞) * ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal N * ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) := by
          gcongr
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hT
      _ = ENNReal.ofReal (N * (24 * δ ^ 2 / θ ^ 2)) := by
          rw [← ENNReal.ofReal_mul (le_trans (Nat.cast_nonneg _) hT)]
  calc ∑ i ∈ Sk, sliceArea (Y i ∩ PR) z
      ≤ ∑ i ∈ Sk, ∑ k ∈ KF, sliceArea (Y i ∩ Coarse.gridCube s k) z :=
        Finset.sum_le_sum h1
    _ = ∑ k ∈ KF, ∑ i ∈ Sk, sliceArea (Y i ∩ Coarse.gridCube s k) z := Finset.sum_comm
    _ ≤ ∑ _k ∈ KF, ENNReal.ofReal (N * (24 * δ ^ 2 / θ ^ 2)) := Finset.sum_le_sum fun k _ => h2 k
    _ = (KF.card : ℝ≥0∞) * ENNReal.ofReal (N * (24 * δ ^ 2 / θ ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- A representative height of a row carrying at least half the average slice mass. -/
theorem exists_rep_height (hS : FineSetup σ δ s θ K N x v Y Eo f P) (Sk : Finset (Fin n))
    {PR : Set Space} (hPR : MeasurableSet PR) (m : ℤ) :
    ∃ z ∈ row s m, ENNReal.ofReal (1 / (2 * s)) * ∑ i ∈ Sk,
        volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' row s m) ≤
      ∑ i ∈ Sk, sliceArea (Y i ∩ PR) z := by
  have hs := s_pos hS
  set M := ∑ i ∈ Sk, volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' row s m)
  have hM : M = ∑ i ∈ Sk, ∫⁻ z in row s m, sliceArea (Y i ∩ PR) z := by
    apply Finset.sum_congr rfl
    intro i _
    exact volume_inter_height_eq ((hS.meas i).inter hPR) (measurableSet_row s m)
  have hMle : M ≤ ∫⁻ z in row s m, ∑ i ∈ Sk, sliceArea (Y i ∩ PR) z := by
    rw [hM]; exact sum_lintegral_le_lintegral_sum Sk _ _
  by_cases hM0 : M = 0
  · refine ⟨s * m, ⟨le_rfl, by nlinarith⟩, ?_⟩
    rw [hM0, mul_zero]; exact zero_le
  have hMt : M ≠ ∞ := by
    apply ne_of_lt
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact (measure_mono (inter_subset_left.trans (inter_subset_left.trans
      ((hS.sub_Eo i).trans hS.Eo_ball)))).trans_lt measure_ball_lt_top
  have hmain : ENNReal.ofReal (1 / (2 * s)) * M * volume (row s m) <
      ∫⁻ z in row s m, ∑ i ∈ Sk, sliceArea (Y i ∩ PR) z := by
    rw [volume_row hs]
    calc ENNReal.ofReal (1 / (2 * s)) * M * ENNReal.ofReal s
        = ENNReal.ofReal (1 / (2 * s) * s) * M := by
          rw [mul_comm _ M, mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm]
      _ = ENNReal.ofReal (1 / 2) * M := by
          congr 2; field_simp
      _ < M := by
          have h12 : ENNReal.ofReal (1 / 2) < 1 := by
            rw [ENNReal.ofReal_lt_one]; norm_num
          calc ENNReal.ofReal (1 / 2) * M < 1 * M :=
                ENNReal.mul_lt_mul_left hM0 hMt h12
            _ = M := one_mul M
      _ ≤ _ := hMle
  obtain ⟨z, hz, hlt⟩ := exists_gt_of_mul_lt (measurableSet_row s m)
    (fun z => ∑ i ∈ Sk, sliceArea (Y i ∩ PR) z) hmain
  exact ⟨z, hz, hlt.le⟩

lemma row_disjoint {s : ℝ} (hs : 0 < s) {m m' : ℤ} (h : m ≠ m') :
    Disjoint (row s m) (row s m') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact h (row_eq_of_mem hs hz hz')

/-- The cubes reached by the fine slice at a height of row `m` lie in row `m`. -/
lemma reached_row {s : ℝ} (hs : 0 < s) {n : ℕ} {Y : Fin n → Set Space} {Sk : Finset (Fin n)}
    {PR : Set Space} {Kb : ℕ} {z : ℝ} {m : ℤ} (hz : z ∈ row s m) {k : Fin 3 → ℤ}
    (hk : k ∈ Coarse.reachedF s Kb (fineSlice Y Sk PR z)) : k 2 = m := by
  classical
  unfold Coarse.reachedF at hk
  obtain ⟨-, q, hqk, -, hq2⟩ := Finset.mem_filter.mp hk
  have h1 := height_mem_row hqk
  rw [show q 2 = z from hq2] at h1
  exact row_eq_of_mem hs h1 hz

/-- The cube set of a configuration with representative heights. -/
noncomputable def cubeSet {n : ℕ} (s : ℝ) (Kb : ℕ) (Y : Fin n → Set Space) (Sk : Finset (Fin n))
    (PR : Set Space) (R : Finset ℤ) (zrep : ℤ → ℝ) : Finset (Fin 3 → ℤ) :=
  R.biUnion fun m => Coarse.reachedF s Kb (fineSlice Y Sk PR (zrep m))

lemma volume_cubeUnion {s : ℝ} (hs : 0 < s) (Kc : Finset (Fin 3 → ℤ)) :
    volume (cubeUnion s Kc) = (Kc.card : ℝ≥0∞) * ENNReal.ofReal s ^ 3 := by
  unfold cubeUnion
  rw [measure_biUnion_finset (fun k _ k' _ hkk => Coarse.gridCube_disjoint hs hkk)
    (fun k _ => Coarse.measurableSet_gridCube s k)]
  simp only [Coarse.volume_gridCube hs, Finset.sum_const, nsmul_eq_mul]

/-- The fine mass of the kept shadings in the plank region and the rows is controlled by the
number of cubes of the configuration. -/
theorem mass_le_card_cubeSet (hS : FineSetup σ δ s θ K N x v Y Eo f P) (Sk : Finset (Fin n))
    {PR : Set Space} (hPR : MeasurableSet PR) {R : Finset ℤ} {zrep : ℤ → ℝ}
    (hzrep : ∀ m ∈ R, zrep m ∈ row s m ∧
      ENNReal.ofReal (1 / (2 * s)) * ∑ i ∈ Sk,
        volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' row s m) ≤
      ∑ i ∈ Sk, sliceArea (Y i ∩ PR) (zrep m))
    {Kb : ℕ} (hKb : 2 / s + 1 ≤ Kb) :
    ENNReal.ofReal (1 / (2 * s)) * ∑ i ∈ Sk,
        volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' rowUnion s R) ≤
      ((cubeSet s Kb Y Sk PR R zrep).card : ℝ≥0∞) * ENNReal.ofReal (N * (24 * δ ^ 2 / θ ^ 2)) := by
  classical
  have hs := s_pos hS
  have hsplit : ∀ i ∈ Sk, volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' rowUnion s R) =
      ∑ m ∈ R, volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' row s m) := by
    intro i _
    rw [rowUnion, preimage_iUnion₂, inter_iUnion₂]
    exact measure_biUnion_finset
      (fun m _ m' _ hmm => (Disjoint.preimage _ (row_disjoint hs hmm)).mono
        inter_subset_right inter_subset_right)
      (fun m _ => ((hS.meas i).inter hPR).inter
        ((by fun_prop : Continuous fun p : Space => p 2).measurable (measurableSet_row s m)))
  have hdisj : (R : Set ℤ).PairwiseDisjoint
      (fun m => Coarse.reachedF s Kb (fineSlice Y Sk PR (zrep m))) := by
    intro m hm m' hm' hmm
    rw [Function.onFun, Finset.disjoint_left]
    intro k hk hk'
    exact hmm ((reached_row hs (hzrep m hm).1 hk).symm.trans (reached_row hs (hzrep m' hm').1 hk'))
  calc ENNReal.ofReal (1 / (2 * s)) * ∑ i ∈ Sk,
        volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' rowUnion s R)
      = ∑ m ∈ R, ENNReal.ofReal (1 / (2 * s)) * ∑ i ∈ Sk,
          volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' row s m) := by
        rw [Finset.sum_congr rfl hsplit, Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ m ∈ R, ∑ i ∈ Sk, sliceArea (Y i ∩ PR) (zrep m) :=
        Finset.sum_le_sum fun m hm => (hzrep m hm).2
    _ ≤ ∑ m ∈ R, ((Coarse.reachedF s Kb (fineSlice Y Sk PR (zrep m))).card : ℝ≥0∞) *
          ENNReal.ofReal (N * (24 * δ ^ 2 / θ ^ 2)) :=
        Finset.sum_le_sum fun m _ => slice_mass_le_card hS Sk PR hKb (zrep m)
    _ = ((cubeSet s Kb Y Sk PR R zrep).card : ℝ≥0∞) * ENNReal.ofReal (N * (24 * δ ^ 2 / θ ^ 2)) := by
        rw [← Finset.sum_mul, cubeSet, Finset.card_biUnion hdisj]
        push_cast
        rfl

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
