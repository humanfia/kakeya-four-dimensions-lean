-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.Dyadic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Seed.Kakeya
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate

noncomputable def dyadic (k : ℕ) : ℝ := (1 / 2) ^ k

theorem dyadic_pos (k : ℕ) : 0 < dyadic k := by
  exact pow_pos (by norm_num) k

theorem dyadic_le_one (k : ℕ) : dyadic k ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem dyadic_succ (k : ℕ) : dyadic (k + 1) = dyadic k / 2 := by
  simp [dyadic, pow_succ, div_eq_mul_inv]

theorem dyadic_antitone : Antitone dyadic := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij

noncomputable def scaleIndices (F : Finset ℕ) (ρ : ℕ → ℝ) (k : ℕ) : Finset ℕ :=
  F.filter fun m => dyadic (k + 1) < ρ m ∧ ρ m ≤ dyadic k

noncomputable def scaleCover (F : Finset ℕ)
    (c : ℕ → LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℕ → ℝ) (k : ℕ) :
    Set LeanEval.Analysis.WangZahlKakeya.Space :=
  ⋃ m ∈ scaleIndices F ρ k, ball (c m) (ρ m)

noncomputable def scaleEnlargement (F : Finset ℕ)
    (c : ℕ → LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℕ → ℝ) (k : ℕ) :
    Set LeanEval.Analysis.WangZahlKakeya.Space :=
  ⋃ m ∈ scaleIndices F ρ k, ball (c m) (2 * ρ m)

theorem subset_iUnion_scaleCover (F : Finset ℕ)
    (c : ℕ → LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℕ → ℝ)
    (hρ : ∀ m ∈ F, 0 < ρ m ∧ ρ m ≤ 1) :
    (⋃ m ∈ F, ball (c m) (ρ m)) ⊆ ⋃ k, scaleCover F c ρ k := by
  intro x hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  obtain ⟨hmF, hxball⟩ := mem_iUnion.mp hm
  obtain ⟨k, hk⟩ := exists_nat_pow_near_of_lt_one
    (hρ m hmF).1 (hρ m hmF).2 (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨m,
    mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hmF, hk⟩, hxball⟩⟩⟩

theorem scaleCover_eq_empty_of_lt {F : Finset ℕ}
    {c : ℕ → LeanEval.Analysis.WangZahlKakeya.Space} {ρ : ℕ → ℝ} {N k : ℕ}
    (hρ : ∀ m ∈ F, ρ m ≤ dyadic N) (hk : k < N) : scaleCover F c ρ k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  obtain ⟨hmF, _⟩ := mem_iUnion.mp hm
  obtain ⟨hmF, hmlo, _⟩ := Finset.mem_filter.mp hmF
  exact (not_lt_of_ge ((hρ m hmF).trans (dyadic_antitone (by omega)))) hmlo

theorem thickening_scaleCover_subset (F : Finset ℕ)
    (c : ℕ → LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℕ → ℝ) (k : ℕ) :
    thickening (dyadic k / 2) (scaleCover F c ρ k) ⊆ scaleEnlargement F c ρ k := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hy
  obtain ⟨hmF, hym⟩ := mem_iUnion.mp hm
  refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmF, ?_⟩⟩
  have hlo := (Finset.mem_filter.mp hmF).2.1
  rw [dyadic_succ] at hlo
  have := dist_triangle x y (c m)
  change dist y (c m) < ρ m at hym
  change dist x (c m) < 2 * ρ m
  linarith

/-- A finite ball cover of a unit segment has one scale with polynomially large
one-dimensional mass. -/
theorem exists_scale_mass (F : Finset ℕ)
    (c : ℕ → LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℕ → ℝ)
    (hρ : ∀ m ∈ F, 0 < ρ m ∧ ρ m ≤ 1)
    (x v : LeanEval.Analysis.WangZahlKakeya.Space)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ ⋃ m ∈ F, ball (c m) (ρ m)) :
    ∃ k : ℕ, ENNReal.ofReal (1 / (4 * ((k : ℝ) + 1) ^ 2)) ≤
      volume {t : ℝ | t ∈ Icc 0 1 ∧ x + t • v ∈ scaleCover F c ρ k} := by
  have h : (1 : ℝ≥0∞) ≤ ∑' k : ℕ,
      volume {t : ℝ | t ∈ Icc 0 1 ∧ x + t • v ∈ scaleCover F c ρ k} := by
    calc
      (1 : ℝ≥0∞) = volume (Icc (0 : ℝ) 1) := by simp
      _ ≤ volume (⋃ k : ℕ, {t : ℝ | t ∈ Icc 0 1 ∧
          x + t • v ∈ scaleCover F c ρ k}) := by
        apply measure_mono
        intro t ht
        obtain ⟨k, hk⟩ := mem_iUnion.mp (subset_iUnion_scaleCover F c ρ hρ (hcover t ht))
        exact mem_iUnion.mpr ⟨k, ht, hk⟩
      _ ≤ _ := measure_iUnion_le _
  obtain ⟨k, hk⟩ := WangZahlLot.Seed.Kakeya.exists_le_of_le_tsum
    (by norm_num : (1 : ℝ≥0∞) ≠ 0) (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) h
  refine ⟨k, ?_⟩
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  exact hk


/-- Geometric weights allow an arbitrarily small power loss in the scale. -/
theorem exists_geometric_mass {f : ℕ → ℝ≥0∞} {w q : ℝ}
    (hw : 0 < w) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h : ENNReal.ofReal w ≤ ∑' k, f k) :
    ∃ k : ℕ, ENNReal.ofReal (w * ((1 - q) / 2) * q ^ k) ≤ f k := by
  by_contra! H
  have hsum : (∑' k : ℕ, ENNReal.ofReal (w * ((1 - q) / 2) * q ^ k)) =
      ENNReal.ofReal (w / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left _),
      tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr hq1)]
  have hle := h.trans (ENNReal.tsum_le_tsum (fun k => (H k).le))
  rw [hsum] at hle
  have hlt : ENNReal.ofReal (w / 2) < ENNReal.ofReal w :=
    (ENNReal.ofReal_lt_ofReal_iff hw).mpr (by linarith)
  exact (not_le_of_gt hlt) hle

theorem exists_scale_mass_geometric (F : Finset ℕ)
    (c : ℕ → LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℕ → ℝ)
    (hρ : ∀ m ∈ F, 0 < ρ m ∧ ρ m ≤ 1)
    (x v : LeanEval.Analysis.WangZahlKakeya.Space) {γ : ℝ} (hγ : 0 < γ)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ ⋃ m ∈ F, ball (c m) (ρ m)) :
    ∃ k : ℕ, ENNReal.ofReal (((1 - (1 / 2 : ℝ) ^ γ) / 2) * dyadic k ^ γ) ≤
      volume {t : ℝ | t ∈ Icc 0 1 ∧ x + t • v ∈ scaleCover F c ρ k} := by
  have h : (1 : ℝ≥0∞) ≤ ∑' k : ℕ,
      volume {t : ℝ | t ∈ Icc 0 1 ∧ x + t • v ∈ scaleCover F c ρ k} := by
    calc
      (1 : ℝ≥0∞) = volume (Icc (0 : ℝ) 1) := by simp
      _ ≤ volume (⋃ k : ℕ, {t : ℝ | t ∈ Icc 0 1 ∧
          x + t • v ∈ scaleCover F c ρ k}) := by
        apply measure_mono
        intro t ht
        obtain ⟨k, hk⟩ := mem_iUnion.mp (subset_iUnion_scaleCover F c ρ hρ (hcover t ht))
        exact mem_iUnion.mpr ⟨k, ht, hk⟩
      _ ≤ _ := measure_iUnion_le _
  obtain ⟨k, hk⟩ := exists_geometric_mass (w := 1) (q := (1 / 2 : ℝ) ^ γ)
    (by norm_num) (by positivity) (Real.rpow_lt_one (by norm_num) (by norm_num) hγ)
    (by simpa using h)
  refine ⟨k, ?_⟩
  simpa only [Set.mem_Icc, one_mul, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2), dyadic] using hk


/-- The enlarged balls at one scale have small volume when the cover has small
`s`-dimensional cost. -/
theorem volume_scaleEnlargement_le (F : Finset ℕ)
    (c : ℕ → LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℕ → ℝ)
    {s η : ℝ} (_hs : 0 ≤ s) (hs3 : s ≤ 3)
    (hρ : ∀ m ∈ F, 0 < ρ m) (hcost : ∑ m ∈ F, ρ m ^ s ≤ η) (k : ℕ) :
    volume (scaleEnlargement F c ρ k) ≤
      ENNReal.ofReal (64 * η * dyadic k ^ (3 - s)) := by
  classical
  have hrpos := dyadic_pos k
  have hterm : ∀ m ∈ scaleIndices F ρ k,
      volume (ball (c m) (2 * ρ m)) ≤
        ENNReal.ofReal (64 * (ρ m ^ s) * dyadic k ^ (3 - s)) := by
    intro m hm
    have hmF := (Finset.mem_filter.mp hm).1
    have hmr := (Finset.mem_filter.mp hm).2.2
    have hmpos := hρ m hmF
    rw [EuclideanSpace.volume_ball_fin_three,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hid : ρ m ^ (3 : ℕ) = ρ m ^ s * ρ m ^ (3 - s) := by
      rw [← Real.rpow_add hmpos]
      norm_num
    calc
      (2 * ρ m) ^ 3 * (Real.pi * 4 / 3) ≤ 64 * ρ m ^ 3 := by
        calc
          (2 * ρ m) ^ 3 * (Real.pi * 4 / 3) ≤ (2 * ρ m) ^ 3 * 8 := by
            gcongr
            linarith [Real.pi_lt_four]
          _ = _ := by ring
      _ = 64 * ρ m ^ s * ρ m ^ (3 - s) := by rw [hid]; ring
      _ ≤ _ := by
        gcongr
  have hsum : ∑ m ∈ scaleIndices F ρ k, ρ m ^ s ≤ η := by
    apply le_trans _ hcost
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun m hm _ => Real.rpow_nonneg (hρ m hm).le s)
  calc
    volume (scaleEnlargement F c ρ k) ≤
        ∑ m ∈ scaleIndices F ρ k, volume (ball (c m) (2 * ρ m)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ scaleIndices F ρ k,
        ENNReal.ofReal (64 * ρ m ^ s * dyadic k ^ (3 - s)) :=
      Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (64 * (∑ m ∈ scaleIndices F ρ k, ρ m ^ s) *
        dyadic k ^ (3 - s)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m hm => by
        have := hρ m (Finset.mem_filter.mp hm).1
        positivity), ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr

end WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate
