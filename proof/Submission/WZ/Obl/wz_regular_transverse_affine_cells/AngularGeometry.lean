-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.AngularGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Slab
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open WangZahlLot.Obl.wz_balanced_cluster_cover

/-- A direction close to the normal of a thin set controls its projected diameter. -/
lemma thin_set_projected_diameter {U : Set E} {u ν c : E} {a R θ : ℝ}
    (hθ : 0 ≤ θ)
    (hbound : U ⊆ Metric.closedBall (0 : E) R)
    (hthin : ∀ q ∈ U, |inner ℝ u (q - c)| ≤ a)
    (hangle : min ‖u - ν‖ ‖u + ν‖ ≤ θ) {p q : E} (hp : p ∈ U) (hq : q ∈ U) :
    |inner ℝ ν (q - p)| ≤ 2 * a + 2 * R * θ := by
  have hqp : ‖q - p‖ ≤ 2 * R := by
    have hp' : ‖p‖ ≤ R := by simpa using hbound hp
    have hq' : ‖q‖ ≤ R := by simpa using hbound hq
    exact (norm_sub_le q p).trans (by linarith)
  have hinner : |inner ℝ u (q - p)| ≤ 2 * a := by
    calc |inner ℝ u (q - p)| = |inner ℝ u (q - c) - inner ℝ u (p - c)| := by
          congr 1
          simp only [inner_sub_right]
          ring
      _ ≤ |inner ℝ u (q - c)| + |inner ℝ u (p - c)| := abs_sub _ _
      _ ≤ 2 * a := by linarith [hthin q hq, hthin p hp]
  rcases min_le_iff.mp hangle with h | h
  · have herror : |inner ℝ (ν - u) (q - p)| ≤ θ * (2 * R) := by
      apply (abs_real_inner_le_norm _ _).trans
      rw [norm_sub_rev] at h
      exact mul_le_mul h hqp (norm_nonneg _) hθ
    calc |inner ℝ ν (q - p)| =
        |inner ℝ (ν - u) (q - p) + inner ℝ u (q - p)| := by simp [inner_sub_left]
      _ ≤ |inner ℝ (ν - u) (q - p)| + |inner ℝ u (q - p)| := abs_add_le _ _
      _ ≤ _ := by linarith
  · have herror : |inner ℝ (ν + u) (q - p)| ≤ θ * (2 * R) := by
      apply (abs_real_inner_le_norm _ _).trans
      rw [add_comm] at h
      exact mul_le_mul h hqp (norm_nonneg _) hθ
    calc |inner ℝ ν (q - p)| =
        |inner ℝ (ν + u) (q - p) - inner ℝ u (q - p)| := by simp [inner_add_left]
      _ ≤ |inner ℝ (ν + u) (q - p)| + |inner ℝ u (q - p)| := abs_sub _ _
      _ ≤ _ := by linarith

namespace Angular

abbrev Label := Σ _ : (Fin 3 → ℤ), ℤ

/-- The point label determined by an incident normal. -/
noncomputable def label (θ : ℝ) (v p : E) : Label :=
  ⟨cell θ v, ⌊inner ℝ (W θ (cell θ v)) p / θ⌋⟩

/-- Every possible label of one thin set lies in this uniformly bounded set. -/
noncomputable def possibleLabels (θ : ℝ) (u p₀ : E) : Finset Label :=
  ((box θ u θ) ∪ (box θ (-u) θ)).sigma fun L =>
    Finset.Icc ⌊(inner ℝ (W θ L) p₀ - 8 * θ) / θ⌋
      ⌊(inner ℝ (W θ L) p₀ + 8 * θ) / θ⌋

lemma card_possibleLabels {θ : ℝ} (hθ : 0 < θ) (u p₀ : E) :
    (possibleLabels θ u p₀).card ≤ 2304 := by
  have hbox (v : E) : (box θ v θ).card ≤ 64 := by
    have h := card_box_le hθ v hθ.le
    have he : 2 * θ / θ + 2 = (4 : ℝ) := by field_simp; ring
    rw [he] at h
    norm_num at h
    exact_mod_cast h
  have hc : ((box θ u θ) ∪ (box θ (-u) θ)).card ≤ 128 := by
    have h := Finset.card_union_le (box θ u θ) (box θ (-u) θ)
    have h₁ := hbox u
    have h₂ := hbox (-u)
    omega
  have hoff (L : Fin 3 → ℤ) :
      (Finset.Icc ⌊(inner ℝ (W θ L) p₀ - 8 * θ) / θ⌋
        ⌊(inner ℝ (W θ L) p₀ + 8 * θ) / θ⌋).card ≤ 18 := by
    have h := card_Icc_floor_le hθ (inner ℝ (W θ L) p₀) (8 * θ) (by positivity)
    have he : 2 * (8 * θ) / θ + 2 = (18 : ℝ) := by field_simp; ring
    rw [he] at h
    exact_mod_cast h
  unfold possibleLabels
  rw [Finset.card_sigma]
  calc (∑ L ∈ box θ u θ ∪ box θ (-u) θ,
        (Finset.Icc ⌊(inner ℝ (W θ L) p₀ - 8 * θ) / θ⌋
          ⌊(inner ℝ (W θ L) p₀ + 8 * θ) / θ⌋).card)
      ≤ ∑ _L ∈ box θ u θ ∪ box θ (-u) θ, 18 := Finset.sum_le_sum fun L _ => hoff L
    _ = ((box θ u θ) ∪ (box θ (-u) θ)).card * 18 := by simp
    _ ≤ 128 * 18 := Nat.mul_le_mul_right 18 hc
    _ = 2304 := rfl

lemma label_mem_possible {U : Set E} {u c p₀ p v : E} {a θ : ℝ}
    (hθ : 0 < θ) (ha : a ≤ θ) (hv : ‖v‖ = 1)
    (hbound : U ⊆ Metric.closedBall (0 : E) 1)
    (hthin : ∀ q ∈ U, |inner ℝ u (q - c)| ≤ a)
    (hp₀ : p₀ ∈ U) (hp : p ∈ U) (hangle : min ‖u - v‖ ‖u + v‖ ≤ θ) :
    label θ v p ∈ possibleLabels θ u p₀ := by
  have hcell : cell θ v ∈ box θ u θ ∪ box θ (-u) θ := by
    rcases min_le_iff.mp hangle with h | h
    · exact Finset.mem_union_left _ (cell_mem_box hθ (by rwa [norm_sub_rev]))
    · exact Finset.mem_union_right _ (cell_mem_box hθ (by simpa [sub_neg_eq_add, add_comm] using h))
  have hW := W_spec hv (rfl : cell θ v = cell θ v)
  have hclose : min ‖u - W θ (cell θ v)‖ ‖u + W θ (cell θ v)‖ ≤ 3 * θ := by
    calc _ ≤ min ‖u - v‖ ‖u + v‖ + ‖v - W θ (cell θ v)‖ := min_norm_triangle _ _ _
      _ ≤ θ + 2 * θ := add_le_add hangle (norm_sub_le_of_cell_eq hθ hW.2.symm)
      _ = _ := by ring
  have hproj := thin_set_projected_diameter
    (show 0 ≤ 3 * θ by positivity) hbound hthin hclose hp₀ hp
  have hproj' : |inner ℝ (W θ (cell θ v)) p - inner ℝ (W θ (cell θ v)) p₀| ≤ 8 * θ := by
    rw [inner_sub_right] at hproj
    linarith
  refine Finset.mem_sigma.mpr ⟨hcell, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
  · dsimp only [label]
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hθ.le
    linarith [(abs_le.mp hproj').1]
  · dsimp only [label]
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hθ.le
    linarith [(abs_le.mp hproj').2]

/-- A label met by the shading of a thin set gives a slab containing that whole set. -/
lemma label_slab_contains {U : Set E} {u c p v : E} {a θ : ℝ}
    (hθ : 0 < θ) (ha : a ≤ θ) (hv : ‖v‖ = 1)
    (hbound : U ⊆ Metric.closedBall (0 : E) 1)
    (hthin : ∀ q ∈ U, |inner ℝ u (q - c)| ≤ a)
    (hp : p ∈ U) (hangle : min ‖u - v‖ ‖u + v‖ ≤ θ) :
    U ⊆ slab (innerSL ℝ (W θ (label θ v p).1))
      (θ * (label θ v p).2) (9 * θ) := by
  have hW := W_spec hv (rfl : cell θ v = cell θ v)
  have hclose : min ‖u - W θ (cell θ v)‖ ‖u + W θ (cell θ v)‖ ≤ 3 * θ := by
    calc _ ≤ min ‖u - v‖ ‖u + v‖ + ‖v - W θ (cell θ v)‖ := min_norm_triangle _ _ _
      _ ≤ θ + 2 * θ := add_le_add hangle (norm_sub_le_of_cell_eq hθ hW.2.symm)
      _ = _ := by ring
  intro q hq
  have hproj := thin_set_projected_diameter
    (show 0 ≤ 3 * θ by positivity) hbound hthin hclose hp hq
  let z := inner ℝ (W θ (cell θ v)) p
  have hfloor : |z - θ * ⌊z / θ⌋| ≤ θ := by
    have hlo := Int.floor_le (z / θ)
    have hhi := Int.lt_floor_add_one (z / θ)
    rw [le_div_iff₀ hθ] at hlo
    rw [div_lt_iff₀ hθ] at hhi
    rw [abs_le]
    constructor <;> nlinarith
  change |inner ℝ (W θ (cell θ v)) q - θ * ⌊z / θ⌋| ≤ 9 * θ
  calc |inner ℝ (W θ (cell θ v)) q - θ * ⌊z / θ⌋| =
        |inner ℝ (W θ (cell θ v)) (q - p) + (z - θ * ⌊z / θ⌋)| := by
          dsimp [z]
          rw [inner_sub_right]
          congr 1
          ring
    _ ≤ |inner ℝ (W θ (cell θ v)) (q - p)| + |z - θ * ⌊z / θ⌋| := abs_add_le _ _
    _ ≤ 9 * θ := by linarith

end Angular
end WangZahlLot.Obl.wz_regular_transverse_affine_cells
