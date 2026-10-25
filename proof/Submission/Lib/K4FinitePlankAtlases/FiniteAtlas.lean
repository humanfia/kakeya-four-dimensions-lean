import Submission.Lib.K4FinitePlankAtlases.FiniteCover
import Submission.Lib.K4FinitePlankAtlases.Recenter

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set
open scoped BigOperators

/-- The finite heavy-plank cover in actual matrix chart coordinates, with the
entry budgets, bounded affine centers, and unnormalized Jacobian floor explicit. -/
theorem finite_matrix_atlas (hweighted : WeightedPlankEstimate) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → Plane)
      (ω : Fin n → ℝ) (J : Fin n → Finset (Fin D)),
    (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i, 0 < ω i) →
    (∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) →
    ∀ A : ℝ, 0 < A → ∃ m : ℕ, ∃ c w : Fin m → Plane,
      ∃ Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ, ∃ S : Fin m → Finset (Fin n),
      m ≤ n ∧ (m : ℝ) * A ≤ ∑ i, ω i ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (∀ j,
        Matrix.det (Q j) ≠ 0 ∧ ‖c j‖ + ‖w j‖ ≤ 2 ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, (|Q j e e'| + |(Q j)⁻¹ e e'|)) ≤ 16 * (D : ℝ) ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, |Q j e e'|) ≤ 8 ∧
        (∀ i ∈ S j, ∀ t ∈ Icc (0 : ℝ) 1,
          ‖Matrix.toEuclideanLin ((Q j)⁻¹) (b i + t • u i - c j - t • w j)‖ ≤ 2) ∧
        (A * (D : ℝ) ^ 2 / 4) * |Matrix.det (Q j)| ≤ ∑ i ∈ S j, ω i) ∧
      ∑ i ∈ Finset.univ.filter (fun i => ∀ j, i ∉ S j), ω i * ((J i).card : ℝ) ≤
        C * A * (D : ℝ) ^ ε * ((visitedCells b u J).card : ℝ) := by
  intro ε hε
  obtain ⟨η, hη, C, hC, hcover⟩ := finite_plank_cover hweighted ε hε
  refine ⟨η, hη, C, hC, ?_⟩
  intro D hD n b u ω J hbu hω hmarks A hA
  obtain ⟨m, p, S, hm, hcount, hdisj, hpack, hres⟩ := hcover D hD n b u ω J hbu hω hmarks A hA
  have hD₁ : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD₀ : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD₁
  let a : Fin m → ℝ := fun j => (p j).narrow / (D : ℝ)
  let β : Fin m → ℝ := fun j => (p j).wide / (D : ℝ)
  have ha (j : Fin m) : 0 < a j :=
    div_pos (zero_lt_one.trans_le (p j).narrow_ge_one) hD₀
  have hb (j : Fin m) : 0 < β j :=
    div_pos (zero_lt_one.trans_le ((p j).narrow_ge_one.trans (p j).narrow_le_wide)) hD₀
  have hb₁ (j : Fin m) : β j ≤ 1 := (div_le_one hD₀).mpr (p j).wide_le_D
  have ha₁ (j : Fin m) : a j ≤ 1 :=
    (div_le_div_of_nonneg_right (p j).narrow_le_wide hD₀.le).trans (hb₁ j)
  have haD (j : Fin m) : a j * (D : ℝ) = (p j).narrow := by dsimp [a]; field_simp
  have hbD (j : Fin m) : β j * (D : ℝ) = (p j).wide := by dsimp [β]; field_simp
  have hinva (j : Fin m) : (2 * a j)⁻¹ ≤ (D : ℝ) / 2 := by
    rw [← one_div (2 * a j)]
    apply (div_le_iff₀ (mul_pos (by norm_num) (ha j))).mpr
    nlinarith [haD j, (p j).narrow_ge_one]
  have hinvb (j : Fin m) : (2 * β j)⁻¹ ≤ (D : ℝ) / 2 := by
    rw [← one_div (2 * β j)]
    apply (div_le_iff₀ (mul_pos (by norm_num) (hb j))).mpr
    nlinarith [hbD j, (p j).narrow_ge_one.trans (p j).narrow_le_wide]
  have hgeometry (j : Fin m) : ∃ c w : Plane, ‖c‖ ≤ 1 ∧ ‖w‖ ≤ 1 ∧
      ∀ i ∈ S j, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin ((plankFrame (2 * a j) (2 * β j) (p j).axis₁ (p j).axis₂)⁻¹)
        (b i + t • u i - c - t • w)‖ ≤ 2 := by
    have hne : (S j).Nonempty := by
      by_contra he
      have hemp := Finset.not_nonempty_iff_eq_empty.mp he
      have hf := (hpack j).2
      rw [hemp, Finset.sum_empty] at hf
      have hpos : 0 < A * (p j).narrow * (p j).wide :=
        mul_pos (mul_pos hA (zero_lt_one.trans_le (p j).narrow_ge_one))
          (zero_lt_one.trans_le ((p j).narrow_ge_one.trans (p j).narrow_le_wide))
      exact (not_le_of_gt hpos) hf
    exact recenter_full_plank b u (S j) hne (fun i hi => hbu i) (ha j) (hb j)
      (p j).unit₁ (p j).unit₂ (p j).orthogonal (hpack j).1
  choose c w hc hw hfit using hgeometry
  let Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ :=
    fun j => plankFrame (2 * a j) (2 * β j) (p j).axis₁ (p j).axis₂
  have hdet (j : Fin m) : |Matrix.det (Q j)| = 4 * a j * β j :=
    recentered_plank_jacobian (ha j) (hb j) (p j).unit₁ (p j).unit₂ (p j).orthogonal
  refine ⟨m, c, w, Q, S, hm, hcount, hdisj, ?_, hres⟩
  intro j
  refine ⟨abs_pos.mp (by rw [hdet]; exact mul_pos (mul_pos (by norm_num) (ha j)) (hb j)),
    by linarith [hc j, hw j], ?_, ?_, hfit j, ?_⟩
  · apply (plankFrame_entry_budget (mul_pos (by norm_num) (ha j)) (mul_pos (by norm_num) (hb j))
      (p j).unit₁ (p j).unit₂ (p j).orthogonal).trans
    nlinarith [ha₁ j, hb₁ j, hinva j, hinvb j]
  · apply (plankFrame_entries (mul_pos (by norm_num) (ha j)) (mul_pos (by norm_num) (hb j)) (p j).unit₁ (p j).unit₂).trans
    nlinarith [ha₁ j, hb₁ j]
  · have heq : (A * (D : ℝ) ^ 2 / 4) * |Matrix.det (Q j)| =
        A * (p j).narrow * (p j).wide := by
      rw [hdet]
      dsimp [a, β]
      field_simp
    rw [heq]
    exact (hpack j).2

end Submission.Lib.K4FinitePlankAtlases
