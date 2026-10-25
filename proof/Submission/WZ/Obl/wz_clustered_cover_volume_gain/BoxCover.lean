-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.BoxCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FiniteCells

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set

theorem norm_le_coord_sum (p : V) : ‖p‖ ≤ |p 0| + |p 1| + |p 2| := by
  have he : p = EuclideanSpace.single 0 (p 0) + EuclideanSpace.single 1 (p 1) +
      EuclideanSpace.single 2 (p 2) := by
    ext i
    fin_cases i <;> simp
  calc
    ‖p‖ = ‖EuclideanSpace.single 0 (p 0) + EuclideanSpace.single 1 (p 1) +
        EuclideanSpace.single 2 (p 2)‖ := congrArg norm he
    _ ≤ (‖EuclideanSpace.single 0 (p 0)‖ + ‖EuclideanSpace.single 1 (p 1)‖) +
        ‖EuclideanSpace.single 2 (p 2)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by simp

theorem projective_le_oriented {u v u' v' : V}
    (hu : u' = u ∨ u' = -u) (hv : v' = v ∨ v' = -v) :
    min ‖u - v‖ ‖u + v‖ ≤ ‖u' - v'‖ := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv]
    exact min_le_left _ _
  · rw [hu, hv, sub_neg_eq_add]
    exact min_le_right _ _
  · rw [hu, hv, show -u - v = -(u + v) by abel, norm_neg]
    exact min_le_right _ _
  · rw [hu, hv, show -u - -v = -(u - v) by abel, norm_neg]
    exact min_le_left _ _

theorem scaled_coord_difference {s t : ℝ} (ht : 0 < t)
    (e : V ≃ₗᵢ[ℝ] V) (z z' z₀ : V) (j : Fin 3)
    (h : |e (z - z₀) j / t - e (z' - z₀) j / t| < s) :
    |e (z - z') j| ≤ s * t := by
  have he : e (z - z₀) j / t - e (z' - z₀) j / t = e (z - z') j / t := by
    simp only [map_sub, PiLp.sub_apply]
    ring
  rw [he, abs_div, abs_of_pos ht] at h
  exact ((div_lt_iff₀ ht).mp h).le

/-- A family of square prisms confined in a moderately enlarged slab with
moderately clustered normals is covered by polynomially many doubled members.
The count is independent of the small aspect ratio `a/c`. -/
theorem confined_prism_anchor_cover {n A : ℕ} (hn : 0 < n) (hA : 1 ≤ A)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a ≤ c)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (u : Fin n → V)
    (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hu : ∀ i, u i = boxAxis (e i) 0 ∨ u i = -boxAxis (e i) 0)
    (hcenter : ∀ i, ‖z i - z₀‖ ≤ A * c)
    (hshort : ∀ i, |e₀ (z i - z₀) 0| ≤ A * a)
    (hnormal : ∀ i, ‖u i - boxAxis e₀ 0‖ ≤ A * (a / c)) :
    ∃ K : ℕ, K = (128 * A ^ 2 + 1) ^ 6 ∧ ∃ ref : Fin K → Fin n,
      ∀ i, ∃ k, P a c c (z i) (e i) ⊆
        P (2 * a) (2 * c) (2 * c) (z (ref k)) (e (ref k)) := by
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hAp : (0 : ℝ) < A := by linarith
  let s : ℝ := 1 / (64 * A)
  have hs : 0 < s := by dsimp [s]; positivity
  have hAs : (A : ℝ) * s = 1 / 64 := by dsimp [s]; field_simp
  have hs64 : s ≤ 1 / 64 := by
    dsimp [s]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have hs3 : 3 * s ≤ 1 / 8 := by linarith
  have hsA : s + 3 * A * s ≤ 1 / 8 := by nlinarith [hAs]
  let d : ℝ := a / c
  have hd : 0 < d := div_pos ha hc
  let u₀ := boxAxis e₀ 0
  let p : Fin n → Fin 6 → ℝ := fun i =>
    ![e₀ (z i - z₀) 0 / a, e₀ (z i - z₀) 1 / c, e₀ (z i - z₀) 2 / c,
      e₀ (u i - u₀) 0 / d, e₀ (u i - u₀) 1 / d, e₀ (u i - u₀) 2 / d]
  have hcoord (v : V) (j : Fin 3) : |e₀ v j| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs, e₀.norm_map] using PiLp.norm_apply_le (e₀ v) j
  have hpc (i : Fin n) : |e₀ (z i - z₀) 0 / a| ≤ A := by
    rw [abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr (hshort i)
  have hpb (i : Fin n) (j : Fin 3) : |e₀ (z i - z₀) j / c| ≤ A := by
    rw [abs_div, abs_of_pos hc]
    exact (div_le_iff₀ hc).mpr ((hcoord _ _).trans (hcenter i))
  have hpn (i : Fin n) (j : Fin 3) : |e₀ (u i - u₀) j / d| ≤ A := by
    rw [abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).mpr ((hcoord _ _).trans (hnormal i))
  have hb : ∀ i j, |p i j| ≤ (64 * A ^ 2 : ℕ) * s := by
    have he : ((64 * A ^ 2 : ℕ) : ℝ) * s = A := by
      push_cast
      dsimp [s]
      field_simp
    rw [he]
    intro i j
    fin_cases j
    · exact hpc i
    · exact hpb i 1
    · exact hpb i 2
    · exact hpn i 0
    · exact hpn i 1
    · exact hpn i 2
  obtain ⟨K, hK, ref, hcover⟩ := finite_grid_representatives hn p hs hb
  refine ⟨K, ?_, ref, ?_⟩
  · rw [hK]
    congr 1
    ring
  intro i
  obtain ⟨k, hk⟩ := hcover i
  refine ⟨k, ?_⟩
  have hz0 := scaled_coord_difference ha e₀ (z i) (z (ref k)) z₀ 0 (hk 0)
  have hz1 := scaled_coord_difference hc e₀ (z i) (z (ref k)) z₀ 1 (hk 1)
  have hz2 := scaled_coord_difference hc e₀ (z i) (z (ref k)) z₀ 2 (hk 2)
  have hu0 := scaled_coord_difference hd e₀ (u i) (u (ref k)) u₀ 0 (hk 3)
  have hu1 := scaled_coord_difference hd e₀ (u i) (u (ref k)) u₀ 1 (hk 4)
  have hu2 := scaled_coord_difference hd e₀ (u i) (u (ref k)) u₀ 2 (hk 5)
  have hzn : ‖z i - z (ref k)‖ ≤ 3 * s * c := by
    have hh := norm_le_coord_sum (e₀ (z i - z (ref k)))
    rw [e₀.norm_map] at hh
    have hhac := mul_le_mul_of_nonneg_left hac hs.le
    linarith
  have hun : ‖u i - u (ref k)‖ ≤ 3 * s * d := by
    have hh := norm_le_coord_sum (e₀ (u i - u (ref k)))
    rw [e₀.norm_map] at hh
    linarith
  apply prism_subset_doubled_of_close ha.le hc hac (z i) (z (ref k)) (e i) (e (ref k))
  · exact hzn.trans (by nlinarith [mul_le_mul_of_nonneg_right hs3 hc.le])
  · have hinner := abs_inner_le_projective (u (ref k)) u₀ (z i - z (ref k))
    have hnref : min ‖u (ref k) - u₀‖ ‖u (ref k) + u₀‖ ≤ A * d :=
      (min_le_left _ _).trans (hnormal (ref k))
    have hm := mul_le_mul hnref hzn (norm_nonneg _) (by positivity : 0 ≤ A * d)
    have heq : (A : ℝ) * d * (3 * s * c) = 3 * A * s * a := by
      dsimp [d]
      field_simp
    rw [heq] at hm
    have hinner0 : |inner ℝ u₀ (z i - z (ref k))| ≤ s * a := by
      rw [show u₀ = boxAxis e₀ 0 from rfl, inner_boxAxis]
      exact hz0
    have hh : |inner ℝ (u (ref k)) (z i - z (ref k))| ≤ a / 8 := by
      nlinarith [mul_le_mul_of_nonneg_right hsA ha.le]
    rcases hu (ref k) with hu' | hu'
    · simpa only [hu', inner_boxAxis] using hh
    · simpa only [hu', inner_neg_left, abs_neg, inner_boxAxis] using hh
  · have hp := projective_le_oriented (hu (ref k)) (hu i)
    rw [norm_sub_rev (u (ref k)) (u i)] at hp
    apply (hp.trans hun).trans
    have hm := mul_le_mul_of_nonneg_right hs3 hd.le
    dsimp [d] at hm ⊢
    convert hm using 1 <;> ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
