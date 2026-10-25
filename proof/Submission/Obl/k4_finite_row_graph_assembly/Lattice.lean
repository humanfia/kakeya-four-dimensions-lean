import Submission.Obl.k4_finite_row_graph_assembly.Projection

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Lattice.lean.
import Submission.Obl.k4_finite_row_graph_assembly.Interfaces

namespace Submission.Obl.k4_finite_row_graph_assembly

def meshVertex (h : ℝ) (a : Vertex) : ℝ × ℝ := (h * a.1, h * a.2)

def meshEdge (h : ℝ) (e : Edge) : RealEdge := (meshVertex h e.1, meshVertex h e.2)

theorem meshVertex_injective {h : ℝ} (hh : h ≠ 0) : Function.Injective (meshVertex h) := by
  intro a b hab
  have h₁ := congrArg Prod.fst hab
  have h₂ := congrArg Prod.snd hab
  apply Prod.ext
  · exact_mod_cast mul_left_cancel₀ hh h₁
  · exact_mod_cast mul_left_cancel₀ hh h₂

theorem meshEdge_injective {h : ℝ} (hh : h ≠ 0) : Function.Injective (meshEdge h) := by
  intro a b hab
  exact Prod.ext (meshVertex_injective hh (congrArg Prod.fst hab))
    (meshVertex_injective hh (congrArg Prod.snd hab))

theorem projection_bound {h K u : ℝ} (hh : 0 ≤ h) (hu : |u| ≤ K)
    {p : Point} (hp : ∀ j, |h * (p j : ℝ)| ≤ K) :
    |(meshVertex h (roundedProjection u p)).1| ≤ K + K ^ 2 + h ∧
    |(meshVertex h (roundedProjection u p)).2| ≤ K + K ^ 2 + h := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hu
  have hb (a b : Fin 4) (sgn : ℝ) (hs : |sgn| ≤ K) :
      |h * (⌊(p a : ℝ) + sgn * (p b : ℝ)⌋ : ℝ)| ≤ K + K ^ 2 + h := by
    have he := mul_le_mul_of_nonneg_left
      (floor_abs_error ((p a : ℝ) + sgn * p b)) hh
    rw [← abs_of_nonneg hh, ← abs_mul] at he
    calc
      _ ≤ |h * ((p a : ℝ) + sgn * p b)| +
          |h * ((⌊(p a : ℝ) + sgn * (p b : ℝ)⌋ : ℝ) -
            ((p a : ℝ) + sgn * p b))| := by
        convert abs_add_le (h * ((p a : ℝ) + sgn * p b))
          (h * ((⌊(p a : ℝ) + sgn * (p b : ℝ)⌋ : ℝ) -
            ((p a : ℝ) + sgn * p b))) using 1 <;> congr 1 <;> ring
      _ ≤ K + K ^ 2 + h := by
        have hprod : |h * ((p a : ℝ) + sgn * p b)| ≤ K + K ^ 2 := by
          calc
            _ = |h * (p a : ℝ) + sgn * (h * (p b : ℝ))| := by congr 1; ring
            _ ≤ |h * (p a : ℝ)| + |sgn * (h * (p b : ℝ))| := abs_add_le _ _
            _ ≤ K + K * K := by
              rw [abs_mul sgn (h * (p b : ℝ))]
              exact add_le_add (hp a) (mul_le_mul hs (hp b) (abs_nonneg _) hK)
            _ = _ := by ring
        exact add_le_add hprod (by simpa only [mul_one, abs_of_nonneg hh] using he)
  constructor
  · simpa only [meshVertex, roundedProjection, pointProjection, sub_eq_add_neg, neg_mul]
      using hb 1 0 (-u) (by simpa using hu)
  · exact hb 2 3 u hu

theorem mesh_index_eq_of_same_interval {h x : ℝ} (hh : 0 < h) {a b : ℤ}
    (ha : h * (a : ℝ) ∈ Set.Ico x (x + h))
    (hb : h * (b : ℝ) ∈ Set.Ico x (x + h)) : a = b := by
  have hd : |h * ((a : ℝ) - b)| < h := by
    rw [abs_lt]
    constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]
  rw [abs_mul, abs_of_pos hh] at hd
  have hi : |(a : ℝ) - b| < 1 := by nlinarith
  have hi' : |a - b| < (1 : ℤ) := by exact_mod_cast hi
  rw [abs_lt] at hi'
  omega

theorem position_diameter {R u₁ u₂ : ℝ} (hR : 1 ≤ R)
    (h₁ : |u₁| ≤ R) (h₂ : |u₂| ≤ R) (hs : 1 / R ≤ |u₂ - u₁|)
    {p q : Point}
    (hp₁ : (roundedProjection u₁ p).1 = (roundedProjection u₁ q).1)
    (hp₂ : (roundedProjection u₂ p).1 = (roundedProjection u₂ q).1) :
    |(p 0 : ℝ) - q 0| ≤ 3 * R ^ 2 ∧ |(p 1 : ℝ) - q 1| ≤ 3 * R ^ 2 := by
  have he (u : ℝ) (heq : (roundedProjection u p).1 = (roundedProjection u q).1) :
      |((p 1 : ℝ) - (q 1 : ℝ)) + u * (-((p 0 : ℝ) - (q 0 : ℝ)))| ≤ 1 := by
    have he := Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell
      (r := 1) (by norm_num)
      (x := (pointProjection u p).1) (y := (pointProjection u q).1)
      (by simpa only [roundedProjection, div_one] using heq)
    convert he using 1
    congr 1
    dsimp [pointProjection]
    ring
  have hh := row_error_of_two_evaluations hR h₁ h₂ hs (he u₁ hp₁) (he u₂ hp₂)
  constructor
  · have hl : 2 * R ≤ 3 * R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    exact (by simpa only [abs_neg, mul_one] using hh.2 :
      |(p 0 : ℝ) - q 0| ≤ 2 * R).trans hl
  · simpa only [mul_one] using hh.1

theorem rectangle_points_card (P : Finset Point) {h K R u₁ u₂ : ℝ}
    (hh : 0 < h) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (h₁ : |u₁| ≤ R) (h₂ : |u₂| ≤ R) (hs : 1 / R ≤ |u₂ - u₁|)
    (hfiber : ∀ q : ℤ × ℤ, ((P.filter (fun p => (p 0, p 1) = q)).card : ℝ) ≤ K)
    (x y : ℝ) :
    ((P.filter (fun p =>
      (meshVertex h (roundedProjection u₁ p)).1 ∈ Set.Ico x (x + h) ∧
      (meshVertex h (roundedProjection u₂ p)).1 ∈ Set.Ico y (y + h))).card : ℝ) ≤
      (6 * R ^ 2 + 2) ^ 2 * K := by
  classical
  let Q := P.filter (fun p =>
    (meshVertex h (roundedProjection u₁ p)).1 ∈ Set.Ico x (x + h) ∧
    (meshVertex h (roundedProjection u₂ p)).1 ∈ Set.Ico y (y + h))
  have hqsub : Q ⊆ P := Finset.filter_subset _ _
  have hcard : ((Q.image (fun p => (p 0, p 1))).card : ℝ) ≤ (6 * R ^ 2 + 2) ^ 2 := by
    apply (card_pair_grid_of_diameter _ (show 0 ≤ 3 * R ^ 2 by positivity) ?_).trans_eq
      (by congr 2; ring)
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨_, hp₁, hp₂⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hq₁, hq₂⟩ := Finset.mem_filter.mp hq
    exact position_diameter hR h₁ h₂ hs (mesh_index_eq_of_same_interval hh hp₁ hq₁)
      (mesh_index_eq_of_same_interval hh hp₂ hq₂)
  calc
    (Q.card : ℝ) ≤ ((Q.image (fun p => (p 0, p 1))).card : ℝ) * K := by
      apply Submission.Obl.k4_scalar_coefficient_clustering.card_le_image_mul_fiber
      intro q hq
      exact (Nat.cast_le.mpr (Finset.card_le_card (by
        intro p hp
        exact Finset.mem_filter.mpr ⟨hqsub (Finset.mem_filter.mp hp).1,
          (Finset.mem_filter.mp hp).2⟩))).trans (hfiber q)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hK

end Submission.Obl.k4_finite_row_graph_assembly
