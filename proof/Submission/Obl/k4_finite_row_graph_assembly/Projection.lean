import Submission.Obl.k4_finite_row_graph_assembly.Geometry

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Projection.lean.

open scoped BigOperators

namespace Submission.Obl.k4_finite_row_graph_assembly

theorem card_pair_grid_of_diameter (P : Finset (ℤ × ℤ)) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P,
      |(p.1 : ℝ) - q.1| ≤ R ∧ |(p.2 : ℝ) - q.2| ≤ R) :
    (P.card : ℝ) ≤ (2 * R + 2) ^ 2 := by
  classical
  have hfst : ((P.image Prod.fst).card : ℝ) ≤ 2 * R + 2 := by
    apply Submission.Obl.k4_scalar_coefficient_clustering.card_int_grid_of_diameter _ hR
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact (hdiam p hp q hq).1
  have hsnd : ((P.image Prod.snd).card : ℝ) ≤ 2 * R + 2 := by
    apply Submission.Obl.k4_scalar_coefficient_clustering.card_int_grid_of_diameter _ hR
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact (hdiam p hp q hq).2
  have hsub : P ⊆ (P.image Prod.fst) ×ˢ (P.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  calc
    (P.card : ℝ) ≤ (((P.image Prod.fst) ×ˢ (P.image Prod.snd)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ((P.image Prod.fst).card : ℝ) * (P.image Prod.snd).card := by simp
    _ ≤ (2 * R + 2) * (2 * R + 2) :=
      mul_le_mul hfst hsnd (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem card_image_le_of_fiber_images {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (P : Finset α) (f : α → β) (g : α → γ) {C : ℝ}
    (hc : ∀ q ∈ P.image f, (((P.filter (fun p => f p = q)).image g).card : ℝ) ≤ C) :
    ((P.image g).card : ℝ) ≤ ((P.image f).card : ℝ) * C := by
  classical
  have hsub : P.image g ⊆ (P.image f).biUnion
      (fun q => (P.filter (fun p => f p = q)).image g) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_biUnion.mpr ⟨f p, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩⟩
  calc
    ((P.image g).card : ℝ) ≤
        (((P.image f).biUnion (fun q => (P.filter (fun p => f p = q)).image g)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ q ∈ P.image f, (((P.filter (fun p => f p = q)).image g).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ P.image f, C := Finset.sum_le_sum hc
    _ = _ := by simp

noncomputable def ratio (u₁ u₂ u : ℝ) : ℝ := (u - u₁) / (u₂ - u)

noncomputable def projectionFactor (u₁ u₂ u : ℝ) : ℝ := (u₂ - u₁) / (u₂ - u)

theorem projection_relation {u₁ u₂ u : ℝ} (hu : u₂ - u ≠ 0) (p : Point) :
    (pointProjection u₁ p).1 + ratio u₁ u₂ u * (pointProjection u₂ p).1 =
      projectionFactor u₁ u₂ u * (pointProjection u p).1 ∧
    (pointProjection u₁ p).2 + ratio u₁ u₂ u * (pointProjection u₂ p).2 =
      projectionFactor u₁ u₂ u * (pointProjection u p).2 := by
  constructor <;> dsimp [pointProjection, ratio, projectionFactor] <;> field_simp <;> ring

noncomputable def sumIndex (u₁ u₂ u : ℝ) (p : Point) : Vertex :=
  (⌊((roundedProjection u₁ p).1 : ℝ) + ratio u₁ u₂ u * (roundedProjection u₂ p).1⌋,
    ⌊((roundedProjection u₁ p).2 : ℝ) + ratio u₁ u₂ u * (roundedProjection u₂ p).2⌋)

theorem floor_abs_error (x : ℝ) : |(⌊x⌋ : ℝ) - x| ≤ 1 := by
  simpa only [one_mul, div_one, abs_sub_comm] using
    Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error
      (p := 1) (by norm_num) x

theorem abs_sub_floor_le (x y : ℝ) :
    |(⌊x⌋ : ℝ) - (⌊y⌋ : ℝ)| ≤ |x - y| + 2 := by
  calc
    _ = |((⌊x⌋ : ℝ) - x) + (x - y) + (y - (⌊y⌋ : ℝ))| := by congr 1; ring
    _ ≤ |(⌊x⌋ : ℝ) - x| + |x - y| + |y - (⌊y⌋ : ℝ)| := abs_add_three _ _ _
    _ ≤ 1 + |x - y| + 1 := by
      exact add_le_add (add_le_add (floor_abs_error x) le_rfl)
        (by simpa only [abs_sub_comm] using floor_abs_error y)
    _ = _ := by ring

theorem rounded_linear_error (a b k : ℝ) :
    |((⌊a⌋ : ℝ) + k * (⌊b⌋ : ℝ)) - (a + k * b)| ≤ 1 + |k| := by
  calc
    _ = |((⌊a⌋ : ℝ) - a) + k * ((⌊b⌋ : ℝ) - b)| := by congr 1; ring
    _ ≤ |(⌊a⌋ : ℝ) - a| + |k * ((⌊b⌋ : ℝ) - b)| := abs_add_le _ _
    _ = |(⌊a⌋ : ℝ) - a| + |k| * |(⌊b⌋ : ℝ) - b| := by rw [abs_mul]
    _ ≤ 1 + |k| * 1 := add_le_add (floor_abs_error a)
      (mul_le_mul_of_nonneg_left (floor_abs_error b) (abs_nonneg k))
    _ = _ := by ring

theorem linear_rounding_diameter {a b c a' b' c' k l : ℝ}
    (he : a + k * b = l * c) (he' : a' + k * b' = l * c')
    (hc : ⌊c⌋ = ⌊c'⌋) :
    |(⌊(⌊a⌋ : ℝ) + k * (⌊b⌋ : ℝ)⌋ : ℝ) -
      (⌊(⌊a'⌋ : ℝ) + k * (⌊b'⌋ : ℝ)⌋ : ℝ)| ≤ 4 + 2 * |k| + |l| := by
  have hcc : |c - c'| ≤ 1 := by
    apply Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell
      (r := 1) (by norm_num)
    simpa using hc
  have hm : |(a + k * b) - (a' + k * b')| ≤ |l| := by
    rw [he, he', ← mul_sub, abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hcc (abs_nonneg l)
  have hh : |((⌊a⌋ : ℝ) + k * (⌊b⌋ : ℝ)) -
      ((⌊a'⌋ : ℝ) + k * (⌊b'⌋ : ℝ))| ≤ 2 + 2 * |k| + |l| := by
    calc
      _ = |(((⌊a⌋ : ℝ) + k * (⌊b⌋ : ℝ)) - (a + k * b)) +
          ((a + k * b) - (a' + k * b')) +
          ((a' + k * b') - ((⌊a'⌋ : ℝ) + k * (⌊b'⌋ : ℝ)))| := by congr 1; ring
      _ ≤ |((⌊a⌋ : ℝ) + k * (⌊b⌋ : ℝ)) - (a + k * b)| +
          |(a + k * b) - (a' + k * b')| +
          |(a' + k * b') - ((⌊a'⌋ : ℝ) + k * (⌊b'⌋ : ℝ))| := abs_add_three _ _ _
      _ ≤ (1 + |k|) + |l| + (1 + |k|) := by
        exact add_le_add (add_le_add (rounded_linear_error a b k) hm)
          (by simpa only [abs_sub_comm] using rounded_linear_error a' b' k)
      _ = _ := by ring
  exact (abs_sub_floor_le _ _).trans (by linarith)

theorem sumIndex_diameter {u₁ u₂ u : ℝ} (hu : u₂ - u ≠ 0) {p q : Point}
    (heq : roundedProjection u p = roundedProjection u q) :
    |((sumIndex u₁ u₂ u p).1 : ℝ) - (sumIndex u₁ u₂ u q).1| ≤
      4 + 2 * |ratio u₁ u₂ u| + |projectionFactor u₁ u₂ u| ∧
    |((sumIndex u₁ u₂ u p).2 : ℝ) - (sumIndex u₁ u₂ u q).2| ≤
      4 + 2 * |ratio u₁ u₂ u| + |projectionFactor u₁ u₂ u| := by
  obtain ⟨hp₁, hp₂⟩ := projection_relation hu p
  obtain ⟨hq₁, hq₂⟩ := projection_relation hu q
  constructor
  · exact linear_rounding_diameter hp₁ hq₁ (congrArg Prod.fst heq)
  · exact linear_rounding_diameter hp₂ hq₂ (congrArg Prod.snd heq)

theorem sumIndex_card (P : Finset Point) {u₁ u₂ u : ℝ} (hu : u₂ - u ≠ 0) :
    ((P.image (sumIndex u₁ u₂ u)).card : ℝ) ≤
      ((P.image (roundedProjection u)).card : ℝ) *
        (2 * (4 + 2 * |ratio u₁ u₂ u| + |projectionFactor u₁ u₂ u|) + 2) ^ 2 := by
  classical
  apply card_image_le_of_fiber_images P (roundedProjection u) (sumIndex u₁ u₂ u)
  intro v hv
  apply card_pair_grid_of_diameter _ (by positivity)
  intro a ha b hb
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  exact sumIndex_diameter hu
    ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)

end Submission.Obl.k4_finite_row_graph_assembly
