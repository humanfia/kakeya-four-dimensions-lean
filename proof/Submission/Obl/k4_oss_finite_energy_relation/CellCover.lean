import Mathlib
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealSeparatedCounts

/-!
# Counting the `δ`-cells met by popular points

`cell_cover_card`: if every point `p` of `H` has at least `lam` points `p'` of `P` with
`|φ p - φ p'| ≤ 16δ`, then the left ends `δ * ⌊φ p / δ⌋` of the `δ`-cells of the points of `H` number
at most `36 |P| / lam`. Each `φ p` lies within `δ` of the left end of its cell.
-/

namespace Submission.Obl.k4_oss_finite_energy_relation

open WangZahlLot.Obl.wz_square_frostman_graph_projection.SP in
/-- Points of the lattice `δℤ` in a closed ball of radius `r`. -/
theorem lattice_ball_card {δ r c : ℝ} (hδ : 0 < δ) (hr : 0 ≤ r) (S : Finset ℝ)
    (hS : ∀ z ∈ S, ∃ k : ℤ, z = δ * k) (hball : ∀ z ∈ S, dist z c ≤ r) :
    (S.card : ℝ) * δ ≤ 2 * r + 2 * δ := by
  apply real_separated_ball_card hδ hr S _ hball
  intro x hx y hy hxy
  obtain ⟨k, rfl⟩ := hS x hx
  obtain ⟨l, rfl⟩ := hS y hy
  have hkl : k ≠ l := by
    rintro rfl
    exact hxy rfl
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hδ]
  have h1 : (1 : ℝ) ≤ |(k : ℝ) - l| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkl)
  nlinarith

/-- The left end `δ * ⌊x / δ⌋` of the `δ`-cell of `x`. -/
theorem cell_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : δ * (⌊x / δ⌋ : ℝ) ≤ x := by
  have h := mul_le_mul_of_nonneg_left (Int.floor_le (x / δ)) hδ.le
  rwa [mul_div_cancel₀ _ hδ.ne'] at h

theorem lt_cell_add {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : x < δ * (⌊x / δ⌋ : ℝ) + δ := by
  have h := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x / δ)) hδ
  rw [mul_div_cancel₀ _ hδ.ne'] at h
  linarith

/-- Every real number lies within `δ` of the left end of its `δ`-cell. -/
theorem dist_cell_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : dist x (δ * (⌊x / δ⌋ : ℝ)) ≤ δ := by
  have h1 := cell_le hδ x
  have h2 := lt_cell_add hδ x
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- The `δ`-cells met by points that are each `16δ`-close to at least `lam` points of `P`
number at most `36 |P| / lam`. -/
theorem cell_cover_card {δ lam : ℝ} (hδ : 0 < δ) (φ : ℝ × ℝ → ℝ)
    (P H : Finset (ℝ × ℝ))
    (hpop : ∀ p ∈ H, lam ≤ ((P.filter (fun p' => |φ p - φ p'| ≤ 16 * δ)).card : ℝ)) :
    ((H.image (fun p => δ * (⌊φ p / δ⌋ : ℝ))).card : ℝ) * lam ≤ 36 * (P.card : ℝ) := by
  classical
  set Z := H.image (fun p => δ * (⌊φ p / δ⌋ : ℝ)) with hZ
  have hz : ∀ z ∈ Z, lam ≤ ((P.filter (fun p' => |z - φ p'| ≤ 17 * δ)).card : ℝ) := by
    intro z hzZ
    obtain ⟨p, hpH, rfl⟩ := Finset.mem_image.mp hzZ
    refine (hpop p hpH).trans ?_
    have h1 := cell_le hδ (φ p)
    have h2 := lt_cell_add hδ (φ p)
    exact_mod_cast Finset.card_le_card (by
      intro p' hp'
      simp only [Finset.mem_filter] at hp' ⊢
      refine ⟨hp'.1, ?_⟩
      have h3 := abs_le.mp hp'.2
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2])
  have hcount : ∀ p' ∈ P, ((Z.filter (fun z => |z - φ p'| ≤ 17 * δ)).card : ℝ) ≤ 36 := by
    intro p' _
    have h := lattice_ball_card hδ (by positivity : (0 : ℝ) ≤ 17 * δ)
      (Z.filter (fun z => |z - φ p'| ≤ 17 * δ)) (c := φ p') ?_ ?_
    · have h' : ((Z.filter (fun z => |z - φ p'| ≤ 17 * δ)).card : ℝ) * δ ≤ 36 * δ := by
        linarith
      exact le_of_mul_le_mul_right h' hδ
    · intro z hz
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz).1
      exact ⟨_, rfl⟩
    · intro z hz
      rw [Real.dist_eq]
      exact (Finset.mem_filter.mp hz).2
  have hdouble : ∑ z ∈ Z, (P.filter (fun p' => |z - φ p'| ≤ 17 * δ)).card =
      ∑ p' ∈ P, (Z.filter (fun z => |z - φ p'| ≤ 17 * δ)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun z p' => |z - φ p'| ≤ 17 * δ)
  calc (Z.card : ℝ) * lam = ∑ z ∈ Z, lam := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ Z, ((P.filter (fun p' => |z - φ p'| ≤ 17 * δ)).card : ℝ) :=
        Finset.sum_le_sum hz
    _ = ∑ p' ∈ P, ((Z.filter (fun z => |z - φ p'| ≤ 17 * δ)).card : ℝ) := by
        exact_mod_cast hdouble
    _ ≤ ∑ p' ∈ P, (36 : ℝ) := Finset.sum_le_sum hcount
    _ = 36 * P.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Submission.Obl.k4_oss_finite_energy_relation
