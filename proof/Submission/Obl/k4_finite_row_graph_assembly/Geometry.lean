import Submission.Obl.k4_scalar_coefficient_clustering.Grid

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Geometry.lean.
import Submission.Obl.k4_oss_collision_cauchy_schwarz.Cells
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

open scoped BigOperators

namespace Submission.Obl.k4_finite_row_graph_assembly

-- The following inversion and lattice-counting lemmas are adapted from this LOT
-- tree, o063, session x0213, Recovery.lean and CellGeometry.lean (e15ca2d).

theorem row_error_of_two_evaluations
    {K R v₁ v₂ x₀ x₁ : ℝ} (hK : 1 ≤ K)
    (hv₁ : |v₁| ≤ K) (_hv₂ : |v₂| ≤ K) (hsep : 1 / K ≤ |v₂ - v₁|)
    (h₁ : |x₀ + v₁ * x₁| ≤ R) (h₂ : |x₀ + v₂ * x₁| ≤ R) :
    |x₀| ≤ 3 * K ^ 2 * R ∧ |x₁| ≤ 2 * K * R := by
  have hKpos : 0 < K := by linarith
  have hR : 0 ≤ R := (abs_nonneg _).trans h₁
  have hd : |(v₂ - v₁) * x₁| ≤ 2 * R := by
    calc
      _ = |(x₀ + v₂ * x₁) - (x₀ + v₁ * x₁)| := by congr 1; ring
      _ ≤ |x₀ + v₂ * x₁| + |x₀ + v₁ * x₁| := abs_sub _ _
      _ ≤ 2 * R := by linarith
  rw [abs_mul] at hd
  have hsep' : 1 ≤ K * |v₂ - v₁| := by
    have := (div_le_iff₀ hKpos).mp hsep
    nlinarith
  have hx₁ : |x₁| ≤ 2 * K * R := by
    have := mul_le_mul_of_nonneg_left hd hKpos.le
    have := mul_le_mul_of_nonneg_right hsep' (abs_nonneg x₁)
    nlinarith
  refine ⟨?_, hx₁⟩
  calc
    |x₀| = |(x₀ + v₁ * x₁) - v₁ * x₁| := by ring_nf
    _ ≤ |x₀ + v₁ * x₁| + |v₁ * x₁| := abs_sub _ _
    _ = |x₀ + v₁ * x₁| + |v₁| * |x₁| := by rw [abs_mul]
    _ ≤ R + K * (2 * K * R) := add_le_add h₁ (mul_le_mul hv₁ hx₁
      (abs_nonneg _) hKpos.le)
    _ ≤ 3 * K ^ 2 * R := by
      nlinarith [sq_nonneg K, mul_nonneg (sq_nonneg (K - 1)) hR]

theorem card_pi_grid_of_diameter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset (ι → ℤ)) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, ∀ j, |(p j : ℝ) - (q j : ℝ)| ≤ R) :
    (P.card : ℝ) ≤ (2 * R + 2) ^ Fintype.card ι := by
  classical
  let S : ι → Finset ℤ := fun j => P.image (fun p => p j)
  have hS : ∀ j, ((S j).card : ℝ) ≤ 2 * R + 2 := by
    intro j
    apply Submission.Obl.k4_scalar_coefficient_clustering.card_int_grid_of_diameter
      (S j) hR
    rintro _ hi _ hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    exact hdiam p hp q hq j
  have hsub : P ⊆ Fintype.piFinset S := by
    intro p hp
    exact Fintype.mem_piFinset.mpr fun j => Finset.mem_image.mpr ⟨p, hp, rfl⟩
  calc
    (P.card : ℝ) ≤ ((Fintype.piFinset S).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ∏ j, ((S j).card : ℝ) := by rw [Fintype.card_piFinset, Nat.cast_prod]
    _ ≤ ∏ _j : ι, (2 * R + 2) :=
      Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hS j)
    _ = (2 * R + 2) ^ Fintype.card ι := by simp

abbrev Point := Fin 4 → ℤ
abbrev Vertex := ℤ × ℤ
abbrev Edge := Vertex × Vertex

/-- Projections in units of the mesh; row coordinates have already been rescaled. -/
def pointProjection (v : ℝ) (p : Point) : ℝ × ℝ :=
  ((p 1 : ℝ) - v * (p 0 : ℝ), (p 2 : ℝ) + v * (p 3 : ℝ))

noncomputable def roundedProjection (v : ℝ) (p : Point) : Vertex :=
  (⌊(pointProjection v p).1⌋, ⌊(pointProjection v p).2⌋)

noncomputable def projectionPair (v₁ v₂ : ℝ) (p : Point) : Edge :=
  (roundedProjection v₁ p, roundedProjection v₂ p)

theorem projectionPair_diameter {K v₁ v₂ : ℝ} (hK : 1 ≤ K)
    (hv₁ : |v₁| ≤ K) (hv₂ : |v₂| ≤ K) (hsep : 1 / K ≤ |v₂ - v₁|)
    {p q : Point} (heq : projectionPair v₁ v₂ p = projectionPair v₁ v₂ q) :
    ∀ j, |(p j : ℝ) - (q j : ℝ)| ≤ 3 * K ^ 2 := by
  have hproj (v : ℝ) (h : roundedProjection v p = roundedProjection v q) :
      |(pointProjection v p).1 - (pointProjection v q).1| ≤ 1 ∧
      |(pointProjection v p).2 - (pointProjection v q).2| ≤ 1 := by
    constructor
    · apply Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell
        (r := 1) (by norm_num)
      simpa only [div_one, roundedProjection] using congrArg Prod.fst h
    · apply Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell
        (r := 1) (by norm_num)
      simpa only [div_one, roundedProjection] using congrArg Prod.snd h
  obtain ⟨h₁z, h₁V⟩ := hproj v₁ (congrArg Prod.fst heq)
  obtain ⟨h₂z, h₂V⟩ := hproj v₂ (congrArg Prod.snd heq)
  have hz := row_error_of_two_evaluations hK hv₁ hv₂ hsep
    (x₀ := (p 1 : ℝ) - (q 1 : ℝ)) (x₁ := -((p 0 : ℝ) - (q 0 : ℝ)))
    (R := 1) (by convert h₁z using 1; congr 1; dsimp [pointProjection]; ring)
    (by convert h₂z using 1; congr 1; dsimp [pointProjection]; ring)
  have hV := row_error_of_two_evaluations hK hv₁ hv₂ hsep
    (x₀ := (p 2 : ℝ) - (q 2 : ℝ)) (x₁ := (p 3 : ℝ) - (q 3 : ℝ))
    (R := 1) (by convert h₁V using 1; congr 1; dsimp [pointProjection]; ring)
    (by convert h₂V using 1; congr 1; dsimp [pointProjection]; ring)
  have hsmall : 2 * K ≤ 3 * K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  intro j
  fin_cases j
  · exact (by simpa only [abs_neg, mul_one] using hz.2 :
      |(p 0 : ℝ) - (q 0 : ℝ)| ≤ 2 * K).trans hsmall
  · simpa using hz.1
  · simpa using hV.1
  · exact (by simpa only [mul_one] using hV.2 :
      |(p 3 : ℝ) - (q 3 : ℝ)| ≤ 2 * K).trans hsmall

theorem projectionPair_fiber_card (P : Finset Point)
    {K v₁ v₂ : ℝ} (hK : 1 ≤ K)
    (hv₁ : |v₁| ≤ K) (hv₂ : |v₂| ≤ K) (hsep : 1 / K ≤ |v₂ - v₁|)
    (e : Edge) :
    ((P.filter (fun p => projectionPair v₁ v₂ p = e)).card : ℝ) ≤
      (6 * K ^ 2 + 2) ^ 4 := by
  classical
  apply (card_pi_grid_of_diameter _ (show 0 ≤ 3 * K ^ 2 by positivity) ?_).trans_eq
    (by congr 2; ring)
  intro p hp q hq j
  apply projectionPair_diameter hK hv₁ hv₂ hsep
  exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm

end Submission.Obl.k4_finite_row_graph_assembly
