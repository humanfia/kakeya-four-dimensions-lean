-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

/-!
# Basic definitions and frame geometry

Prisms, tubes, the projective distance `pd`, and volume estimates for boxes written in an
orthonormal frame `u : Fin 3 → Space`.
-/

namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- The closed rectangular prism of the frozen statement. -/
def prism (a b : ℝ) (c : Space) (u : Fin 3 → Space) : Set Space :=
  {p | |inner ℝ (u 0) (p - c)| ≤ a ∧ |inner ℝ (u 1) (p - c)| ≤ b ∧
    |inner ℝ (u 2) (p - c)| ≤ (1 / 1000 : ℝ)}

/-- The tube of the frozen statement. -/
def tube (r : ℝ) (x v : Space) : Set Space := thickening r (segment ℝ x (x + v))

/-- Distance between unoriented directions. -/
def pd (u v : Space) : ℝ := min ‖u - v‖ ‖u + v‖

/-- The orthonormal basis given by an orthonormal triple. -/
def onb {u : Fin 3 → Space} (hu : Orthonormal ℝ u) : OrthonormalBasis (Fin 3) ℝ Space :=
  (basisOfOrthonormalOfCardEqFinrank hu (by simp)).toOrthonormalBasis (by simpa using hu)

theorem onb_apply {u : Fin 3 → Space} (hu : Orthonormal ℝ u) (k : Fin 3) : onb hu k = u k := by
  simp [onb]

/-- Expansion of a vector in an orthonormal frame. -/
theorem eq_sum_frame {u : Fin 3 → Space} (hu : Orthonormal ℝ u) (q : Space) :
    q = inner ℝ (u 0) q • u 0 + inner ℝ (u 1) q • u 1 + inner ℝ (u 2) q • u 2 := by
  have h := (onb hu).sum_repr' q
  simp only [onb_apply, Fin.sum_univ_three] at h
  exact h.symm

/-- Parseval in an orthonormal frame. -/
theorem norm_sq_frame {u : Fin 3 → Space} (hu : Orthonormal ℝ u) (q : Space) :
    ‖q‖ ^ 2 = inner ℝ (u 0) q ^ 2 + inner ℝ (u 1) q ^ 2 + inner ℝ (u 2) q ^ 2 := by
  have h := (onb hu).sum_sq_inner_right q
  simp only [onb_apply, Fin.sum_univ_three] at h
  exact h.symm

/-- The frame coordinates of a combination of the frame vectors. -/
private theorem basic_inner_sum {u : Fin 3 → Space} (hu : Orthonormal ℝ u) (s : Fin 3 → ℝ)
    (k : Fin 3) : inner ℝ (u k) (∑ j, s j • u j) = s k := by
  rw [inner_sum]
  simp_rw [inner_smul_right, orthonormal_iff_ite.mp hu]
  simp

/-- The volume of a box written in an orthonormal frame, with half-widths `h`. -/
private theorem basic_box_volume {u : Fin 3 → Space} (hu : Orthonormal ℝ u) (z : Space)
    (h : Fin 3 → ℝ) (hh : ∀ k, 0 ≤ h k) :
    volume {q : Space | ∀ k, |inner ℝ (u k) (q - z)| ≤ h k} =
      ENNReal.ofReal (8 * (h 0 * h 1 * h 2)) := by
  have hset : {q : Space | ∀ k, |inner ℝ (u k) (q - z)| ≤ h k} =
      {q : Space | ∀ k, (fun k => -h k) k ≤ (onb hu).repr (q - z) k ∧
        (onb hu).repr (q - z) k ≤ h k} := by
    ext q
    simp only [mem_ofPred_eq, OrthonormalBasis.repr_apply_apply, onb_apply, abs_le]
  rw [hset, WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
  simp only [Fin.prod_univ_three, sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by linarith [hh 0]),
    ← ENNReal.ofReal_mul (by nlinarith [hh 0, hh 1])]
  congr 1
  ring

/-- The prism as a box with half-widths `![a, b, 1 / 1000]`. -/
private theorem basic_prism_eq (a b : ℝ) (c : Space) (u : Fin 3 → Space) :
    prism a b c u =
      {q : Space | ∀ k, |inner ℝ (u k) (q - c)| ≤ (![a, b, 1 / 1000] : Fin 3 → ℝ) k} := by
  ext q
  simp only [prism, mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1, h2⟩ k
    fin_cases k
    · simpa using h0
    · simpa using h1
    · simpa using h2
  · intro h
    exact ⟨h 0, h 1, h 2⟩

/-- A set whose frame coordinates, measured from possibly different base points, are bounded
has volume at most that of the corresponding box. -/
theorem volume_le_of_coords {u : Fin 3 → Space} (hu : Orthonormal ℝ u) (p : Fin 3 → Space)
    (d : Fin 3 → ℝ) (S : Set Space)
    (hS : ∀ q ∈ S, ∀ k, |inner ℝ (u k) (q - p k)| ≤ d k) :
    volume S ≤ ENNReal.ofReal (8 * (d 0 * d 1 * d 2)) := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨q₀, hq₀⟩
  · simp [hSe]
  have hd : ∀ k, 0 ≤ d k := fun k => (abs_nonneg _).trans (hS q₀ hq₀ k)
  have key : ∀ q k, inner ℝ (u k) (q - ∑ j, inner ℝ (u j) (p j) • u j) =
      inner ℝ (u k) (q - p k) := by
    intro q k
    rw [inner_sub_right, inner_sub_right, basic_inner_sum hu]
  calc volume S ≤ volume {q : Space | ∀ k,
        |inner ℝ (u k) (q - ∑ j, inner ℝ (u j) (p j) • u j)| ≤ d k} := by
        apply measure_mono
        intro q hq k
        rw [key]
        exact hS q hq k
    _ = ENNReal.ofReal (8 * (d 0 * d 1 * d 2)) := basic_box_volume hu _ d hd

/-- The volume of a prism. -/
theorem volume_prism {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c : Space) {u : Fin 3 → Space}
    (hu : Orthonormal ℝ u) :
    volume (prism a b c u) = ENNReal.ofReal (8 * (a * b * (1 / 1000))) := by
  rw [basic_prism_eq, basic_box_volume hu c _ ?_]
  · rfl
  · intro k
    fin_cases k
    · simpa using ha
    · simpa using hb
    · norm_num

/-- A prism around one of its points contains a sub-box of the ball. -/
theorem volume_prism_inter_ball_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {c : Space}
    {u : Fin 3 → Space} (hu : Orthonormal ℝ u) {p : Space} (hp : p ∈ prism a b c u)
    {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (min a (r / 2) * min b (r / 2) * min (1 / 1000) (r / 2)) ≤
      volume (prism a b c u ∩ ball p r) := by
  set d : Fin 3 → ℝ := ![a, b, 1 / 1000] with hd_def
  have hd0 : ∀ k, 0 ≤ d k := by
    intro k
    fin_cases k
    · simpa [d] using ha
    · simpa [d] using hb
    · simp [d]
  have hprism : prism a b c u = {q : Space | ∀ k, |inner ℝ (u k) (q - c)| ≤ d k} :=
    basic_prism_eq a b c u
  -- the frame coordinates of `p` relative to `c`
  set t : Fin 3 → ℝ := fun k => inner ℝ (u k) (p - c) with ht_def
  have ht : ∀ k, |t k| ≤ d k := by
    rw [hprism] at hp
    exact hp
  -- side lengths of the sub-box
  set l : Fin 3 → ℝ := fun k => min (d k) (r / 2) with hl_def
  have hl0 : ∀ k, 0 ≤ l k := fun k => le_min (hd0 k) (by linarith)
  have hld : ∀ k, l k ≤ d k := fun k => min_le_left _ _
  have hlr : ∀ k, l k ≤ r / 2 := fun k => min_le_right _ _
  -- the center of the sub-box, moved from `p` towards `c`
  set s : Fin 3 → ℝ := fun k => if 0 ≤ t k then t k - l k / 2 else t k + l k / 2 with hs_def
  set c' : Space := c + ∑ k, s k • u k with hc'_def
  have hinner_c' : ∀ q k, inner ℝ (u k) (q - c) = inner ℝ (u k) (q - c') + s k := by
    intro q k
    have e : q - c = (q - c') + ∑ j, s j • u j := by
      rw [hc'_def]
      abel
    rw [e, inner_add_right, basic_inner_sum hu]
  have hcoord : ∀ q : Space, (∀ k, |inner ℝ (u k) (q - c')| ≤ l k / 2) →
      ∀ k, |inner ℝ (u k) (q - c)| ≤ d k ∧ |inner ℝ (u k) (q - p)| ≤ l k := by
    intro q hq k
    have e1 := hinner_c' q k
    have e2 : inner ℝ (u k) (q - p) = inner ℝ (u k) (q - c) - t k := by
      simp only [t]
      rw [← inner_sub_right]
      congr 1
      abel
    have hx := abs_le.mp (hq k)
    have htk := abs_le.mp (ht k)
    have hlk0 := hl0 k
    have hlkd := hld k
    rw [e2, e1]
    by_cases h : 0 ≤ t k
    · have hs : s k = t k - l k / 2 := by simp only [s, h, ↓reduceIte]
      rw [hs]
      constructor <;> rw [abs_le] <;> constructor <;> linarith
    · have hs : s k = t k + l k / 2 := by simp only [s, h, ↓reduceIte]
      have h' : t k < 0 := not_le.mp h
      rw [hs]
      constructor <;> rw [abs_le] <;> constructor <;> linarith
  have hsub : {q : Space | ∀ k, |inner ℝ (u k) (q - c')| ≤ l k / 2} ⊆
      prism a b c u ∩ ball p r := by
    intro q hq
    have hq' : ∀ k, |inner ℝ (u k) (q - c')| ≤ l k / 2 := hq
    refine ⟨?_, ?_⟩
    · rw [hprism]
      exact fun k => (hcoord q hq' k).1
    · rw [mem_ball, dist_eq_norm]
      have hn := norm_sq_frame hu (q - p)
      have sq : ∀ k, inner ℝ (u k) (q - p) ^ 2 ≤ (r / 2) ^ 2 := by
        intro k
        have h := abs_le.mp ((hcoord q hq' k).2.trans (hlr k))
        nlinarith [h.1, h.2]
      have hlt : ‖q - p‖ ^ 2 < r ^ 2 := by
        rw [hn]
        nlinarith [sq 0, sq 1, sq 2]
      exact lt_of_pow_lt_pow_left₀ 2 hr.le hlt
  calc ENNReal.ofReal (min a (r / 2) * min b (r / 2) * min (1 / 1000) (r / 2))
      = volume {q : Space | ∀ k, |inner ℝ (u k) (q - c')| ≤ l k / 2} := by
        rw [basic_box_volume hu c' (fun k => l k / 2) (fun k => by linarith [hl0 k])]
        congr 1
        simp only [l, d]
        simp
        ring
    _ ≤ volume (prism a b c u ∩ ball p r) := measure_mono hsub

/-- Completing an orthonormal pair `(e, v)` to an orthonormal frame `(e, w, v)`. -/
theorem exists_frame {e v : Space} (he : ‖e‖ = 1) (hv : ‖v‖ = 1) (hev : inner ℝ e v = 0) :
    ∃ w : Space, Orthonormal ℝ ![e, w, v] := by
  have hve : inner ℝ v e = 0 := by rw [real_inner_comm]; exact hev
  have ho : Orthonormal ℝ (({0, 2} : Set (Fin 3)).domRestrict ![e, 0, v]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.domRestrict, he, hv, hev, hve]
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨b 1, ?_⟩
  have hb0 : b 0 = e := hb 0 (by simp)
  have hb2 : b 2 = v := hb 2 (by simp)
  have hfun : ![e, b 1, v] = ⇑b := by
    funext k
    fin_cases k
    · simp [hb0]
    · rfl
    · simp [hb2]
  rw [hfun]
  exact b.orthonormal

/-- The triangle inequality for `pd`. -/
theorem pd_triangle (u v w : Space) : pd u w ≤ pd u v + pd v w := by
  unfold pd
  have e1 : u - w = (u - v) + (v - w) := by abel
  have e2 : u + w = (u - v) + (v + w) := by abel
  have e3 : u + w = (u + v) - (v - w) := by abel
  have e4 : u - w = (u + v) - (v + w) := by abel
  rcases min_choice ‖u - v‖ ‖u + v‖ with h1 | h1 <;>
    rcases min_choice ‖v - w‖ ‖v + w‖ with h2 | h2 <;> rw [h1, h2]
  · calc min ‖u - w‖ ‖u + w‖ ≤ ‖u - w‖ := min_le_left _ _
      _ ≤ ‖u - v‖ + ‖v - w‖ := by rw [e1]; exact norm_add_le _ _
  · calc min ‖u - w‖ ‖u + w‖ ≤ ‖u + w‖ := min_le_right _ _
      _ ≤ ‖u - v‖ + ‖v + w‖ := by rw [e2]; exact norm_add_le _ _
  · calc min ‖u - w‖ ‖u + w‖ ≤ ‖u + w‖ := min_le_right _ _
      _ ≤ ‖u + v‖ + ‖v - w‖ := by rw [e3]; exact norm_sub_le _ _
  · calc min ‖u - w‖ ‖u + w‖ ≤ ‖u - w‖ := min_le_left _ _
      _ ≤ ‖u + v‖ + ‖v + w‖ := by rw [e4]; exact norm_sub_le _ _

theorem pd_symm (u v : Space) : pd u v = pd v u := by
  unfold pd
  rw [norm_sub_rev, add_comm]

theorem pd_neg_left (u v : Space) : pd (-u) v = pd u v := by
  unfold pd
  have h1 : ‖-u - v‖ = ‖u + v‖ := by
    rw [← norm_neg]
    congr 1
    abel
  have h2 : ‖-u + v‖ = ‖u - v‖ := by
    rw [← norm_neg]
    congr 1
    abel
  rw [h1, h2, min_comm]

end

end WangZahlLot.Obl.wz_transverse_cell_weighted_cover
