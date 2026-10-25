-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.DyadicCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The half-open dyadic cell containing a point, recorded by integer coordinates. -/
def dyadicLabel {d : ℕ} (k : ℕ) (p : EuclideanSpace ℝ (Fin d)) : Fin d → ℤ :=
  fun i => ⌊(2 : ℝ) ^ k * p i⌋

lemma dyadicLabel_coarse {d : ℕ} {j k : ℕ} (hjk : j ≤ k)
    (p : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    dyadicLabel j p i = dyadicLabel k p i / (2 : ℤ) ^ (k - j) := by
  have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ j * (2 : ℝ) ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjk]
  have hcast : (((2 : ℕ) ^ (k - j) : ℕ) : ℝ) = (2 : ℝ) ^ (k - j) := by simp
  have he := Int.mul_natCast_floor_div_cancel
    (n := (2 : ℕ) ^ (k - j)) (by positivity) ((2 : ℝ) ^ j * p i)
  simp only [hcast, Nat.cast_pow, Nat.cast_ofNat] at he
  dsimp [dyadicLabel]
  rw [hpow]
  convert he.symm using 1
  congr 2
  ring

lemma dyadicLabel_eq_of_finer_eq {d : ℕ} {j k : ℕ} (hjk : j ≤ k)
    {p q : EuclideanSpace ℝ (Fin d)} (hpq : dyadicLabel k p = dyadicLabel k q) :
    dyadicLabel j p = dyadicLabel j q := by
  funext i
  rw [dyadicLabel_coarse hjk, dyadicLabel_coarse hjk, hpq]

lemma abs_coordinate_sub_lt_of_dyadicLabel_eq {d : ℕ} {k : ℕ}
    {p q : EuclideanSpace ℝ (Fin d)} (hpq : dyadicLabel k p = dyadicLabel k q)
    (i : Fin d) : |p i - q i| < ((2 : ℝ) ^ k)⁻¹ := by
  have h := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hpq i)
  change |(2 : ℝ) ^ k * p i - (2 : ℝ) ^ k * q i| < 1 at h
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ k)] at h
  rw [← one_div]
  apply (lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mpr
  simpa only [mul_comm] using h

/-- A dyadic cell has diameter at most `sqrt(d)` times its side length. -/
lemma dist_le_of_dyadicLabel_eq {d : ℕ} {k : ℕ} {p q : EuclideanSpace ℝ (Fin d)}
    (hpq : dyadicLabel k p = dyadicLabel k q) :
    dist p q ≤ Real.sqrt d * ((2 : ℝ) ^ k)⁻¹ := by
  have hsq : ‖p - q‖ ^ 2 ≤ (d : ℝ) * (((2 : ℝ) ^ k)⁻¹) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d, (((2 : ℝ) ^ k)⁻¹) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hb := (abs_coordinate_sub_lt_of_dyadicLabel_eq hpq i).le
        have hs := mul_self_le_mul_self (abs_nonneg _) hb
        simpa only [PiLp.sub_apply, ← sq, sq_abs] using hs
      _ = _ := by simp
  rw [dist_eq_norm]
  have hroot := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hprod : (Real.sqrt d * ((2 : ℝ) ^ k)⁻¹) ^ 2 =
      (d : ℝ) * (((2 : ℝ) ^ k)⁻¹) ^ 2 := by rw [mul_pow, hroot]
  have hpos : 0 ≤ Real.sqrt d * ((2 : ℝ) ^ k)⁻¹ := by positivity
  nlinarith [norm_nonneg (p - q)]

lemma measurable_dyadicLabel {d : ℕ} (k : ℕ) : Measurable (@dyadicLabel d k) := by
  apply Measurable.of_eval
  intro i
  exact Int.measurable_floor.comp (by fun_prop : Measurable
    (fun p : EuclideanSpace ℝ (Fin d) => (2 : ℝ) ^ k * p i))

lemma floor_mem_three_cells {a b : ℝ} (hab : |a - b| ≤ 1) :
    ⌊a⌋ ∈ Finset.Icc (⌊b⌋ - 1) (⌊b⌋ + 1) := by
  obtain ⟨hab₁, hab₂⟩ := abs_le.mp hab
  have h₁ := Int.floor_mono (show b - 1 ≤ a by linarith)
  have h₂ := Int.floor_mono (show a ≤ b + 1 by linarith)
  exact Finset.mem_Icc.mpr ⟨by simpa using h₁, by simpa using h₂⟩

/-- A ball no larger than a grid cell meets at most three cells per coordinate. -/
lemma dyadicLabel_mem_nearby {d k : ℕ} {p q : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hpq : dist p q < r) (hr : r ≤ ((2 : ℝ) ^ k)⁻¹) :
    dyadicLabel k p ∈ Fintype.piFinset (fun i =>
      Finset.Icc (dyadicLabel k q i - 1) (dyadicLabel k q i + 1)) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply floor_mem_three_cells
  have hc : |p i - q i| ≤ ((2 : ℝ) ^ k)⁻¹ := by
    have hh := PiLp.dist_apply_le p q i
    rw [Real.dist_eq] at hh
    exact hh.trans (hpq.le.trans hr)
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ k)]
  have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (2 : ℝ) ^ k)
  simpa using hm

lemma nearby_dyadicLabels_card {d k : ℕ} (q : EuclideanSpace ℝ (Fin d)) :
    (Fintype.piFinset (fun i =>
      Finset.Icc (dyadicLabel k q i - 1) (dyadicLabel k q i + 1))).card = 3 ^ d := by
  have hc (i : Fin d) :
      (Finset.Icc (dyadicLabel k q i - 1) (dyadicLabel k q i + 1)).card = 3 := by
    rw [Int.card_Icc]
    omega
  simp [Fintype.card_piFinset, hc]

/-- Uniform dyadic cell quotas imply the corresponding metric-ball count. -/
theorem ball_count_le_of_dyadic_cells {α : Type*} [DecidableEq α] {d k : ℕ}
    (U : Finset α) (q : α → EuclideanSpace ℝ (Fin d)) {M r : ℝ}
    (hcell : ∀ l : Fin d → ℤ,
      ((U.filter (fun a => dyadicLabel k (q a) = l)).card : ℝ) ≤ M)
    (q₀ : EuclideanSpace ℝ (Fin d)) (hr : r ≤ ((2 : ℝ) ^ k)⁻¹) :
    ((U.filter (fun a => q a ∈ Metric.ball q₀ r)).card : ℝ) ≤ (3 : ℝ) ^ d * M := by
  classical
  let L := Fintype.piFinset (fun i =>
    Finset.Icc (dyadicLabel k q₀ i - 1) (dyadicLabel k q₀ i + 1))
  have hsub : U.filter (fun a => q a ∈ Metric.ball q₀ r) ⊆
      L.biUnion (fun l => U.filter (fun a => dyadicLabel k (q a) = l)) := by
    intro a ha
    obtain ⟨haU, haq⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_biUnion.mpr ⟨dyadicLabel k (q a), dyadicLabel_mem_nearby haq hr,
      Finset.mem_filter.mpr ⟨haU, rfl⟩⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ l ∈ L, ((U.filter (fun a => dyadicLabel k (q a) = l)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _l ∈ L, M := Finset.sum_le_sum fun l _ => hcell l
    _ = (3 : ℝ) ^ d * M := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [nearby_dyadicLabels_card]
      simp

/-- Fibers of nested partitions form a laminar family. -/
lemma nested_partition_cells_laminar {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (p : ℕ → α → β)
    (hnest : ∀ j k, j ≤ k → ∀ a b, p k a = p k b → p j a = p j b)
    (j k : ℕ) (u v : β) :
    U.filter (fun a => p j a = u) ⊆ U.filter (fun a => p k a = v) ∨
    U.filter (fun a => p k a = v) ⊆ U.filter (fun a => p j a = u) ∨
    Disjoint (U.filter (fun a => p j a = u)) (U.filter (fun a => p k a = v)) := by
  classical
  by_cases hd : Disjoint (U.filter (fun a => p j a = u)) (U.filter (fun a => p k a = v))
  · exact Or.inr (Or.inr hd)
  obtain ⟨a, ha, ha'⟩ := Finset.not_disjoint_iff.mp hd
  have haj := (Finset.mem_filter.mp ha).2
  have hak := (Finset.mem_filter.mp ha').2
  rcases le_total j k with hjk | hkj
  · right; left
    intro b hb
    obtain ⟨hbU, hbk⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hbU, (hnest j k hjk b a (hbk.trans hak.symm)).trans haj⟩
  · left
    intro b hb
    obtain ⟨hbU, hbj⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hbU, (hnest k j hkj b a (hbj.trans haj.symm)).trans hak⟩

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
