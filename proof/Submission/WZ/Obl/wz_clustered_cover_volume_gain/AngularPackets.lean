-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AngularPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GridPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd)

/-- Fine angular grid cells have bounded overlap on a projective cap. -/
theorem angular_grid_partition {n : ℕ} {s : ℝ} (hs : 0 < s) (ν : Fin n → V) :
    ∃ N : ℕ, ∃ f : Fin n → Fin N, ∃ ref : Fin N → Fin n,
      (∀ k, f (ref k) = k) ∧
      (∀ i j, f i = f j → ‖ν i - ν j‖ ≤ s / 100) ∧
      (∀ S : Finset (Fin n),
        (∀ i ∈ S, ∀ j ∈ S, pd (ν i) (ν j) ≤ s) →
        (S.image f).card ≤ 2 * 2003 ^ 3) ∧
      (∀ S : Finset (Fin n), (∀ i ∈ S, ‖ν i‖ ≤ s) →
        (S.image f).card ≤ 2003 ^ 3) := by
  classical
  let code : Fin n → Fin 3 → ℤ := fun i j => ⌊ν i j / (s / 1000)⌋
  obtain ⟨N, f, ref, href, heq⟩ := finite_code_partition code
  have hs' : 0 < s / 1000 := by positivity
  refine ⟨N, f, ref, href, ?_, ?_, ?_⟩
  · intro i j hij
    have hcoord (k : Fin 3) : |ν i k - ν j k| < s / 1000 :=
      abs_sub_lt_of_floor_eq hs' (congrFun ((heq i j).mp hij) k)
    have hn := norm_le_coord_sum (ν i - ν j)
    simp only [PiLp.sub_apply] at hn
    linarith [hcoord 0, hcoord 1, hcoord 2]
  · intro S hS
    rw [partition_image_card code f ref href heq]
    by_cases hS₀ : S.Nonempty
    · obtain ⟨j₀, hj₀⟩ := hS₀
      have hcaps : ∀ i ∈ S, (∀ j, |ν i j - ν j₀ j| ≤ (1000 : ℕ) * (s / 1000)) ∨
          (∀ j, |ν i j + ν j₀ j| ≤ (1000 : ℕ) * (s / 1000)) := by
        intro i hi
        have hh := hS i hi j₀ hj₀
        change min ‖ν i - ν j₀‖ ‖ν i + ν j₀‖ ≤ s at hh
        by_cases hmin : ‖ν i - ν j₀‖ ≤ ‖ν i + ν j₀‖
        · rw [min_eq_left hmin] at hh
          left
          intro j
          have hc := PiLp.norm_apply_le (ν i - ν j₀) j
          simp only [Real.norm_eq_abs, PiLp.sub_apply] at hc
          norm_num
          linarith
        · rw [min_eq_right (le_of_not_ge hmin)] at hh
          right
          intro j
          have hc := PiLp.norm_apply_le (ν i + ν j₀) j
          simp only [Real.norm_eq_abs, PiLp.add_apply] at hc
          norm_num
          linarith
      simpa only [code, show 2 * (1000 + 1) + 1 = 2003 by norm_num] using
        grid_image_card_le_two S (fun i j => ν i j) (fun j => ν j₀ j)
          (fun _ => s / 1000) (fun _ => hs') hcaps
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS₀
      simp [he]
  · intro S hS
    rw [partition_image_card code f ref href heq]
    have hb : ∀ i ∈ S, ∀ j, |ν i j - 0| ≤ (1000 : ℕ) * (s / 1000) := by
      intro i hi j
      have hh := PiLp.norm_apply_le (ν i) j
      simp only [Real.norm_eq_abs] at hh
      norm_num
      linarith [hS i hi]
    simpa only [code, show 2 * (1000 + 1) + 1 = 2003 by norm_num] using
      grid_image_card_le S (fun i j => ν i j) (fun _ => 0)
        (fun _ => s / 1000) (fun _ => hs') hb

lemma inner_ge_half_of_close {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hclose : ‖u - v‖ ≤ 1 / 2) : 1 / 2 ≤ |inner ℝ u v| := by
  have hh := abs_real_inner_le_norm u (u - v)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hu, one_pow, one_mul] at hh
  have hh' := (abs_le.mp (hh.trans hclose)).2
  exact (by linarith : (1 / 2 : ℝ) ≤ inner ℝ u v).trans (le_abs_self _)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
