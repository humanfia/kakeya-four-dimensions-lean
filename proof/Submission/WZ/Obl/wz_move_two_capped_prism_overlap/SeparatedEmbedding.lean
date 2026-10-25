-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.SeparatedEmbedding.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainRotation
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketContainment

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, SeparatedEmbedding.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V P coarseLinear rotatedFrame rotatedFrame_apply)

def fiberShift {N : ℕ} (k : Fin N) : V :=
  (10 * (k.val : ℝ)) • (EuclideanSpace.basisFun (Fin 3) ℝ 2)

def fiberEmbed {N : ℕ} (R : Fin N → V ≃ₗᵢ[ℝ] V) (k : Fin N) (p : V) : V :=
  R k p + fiberShift k

theorem fiberEmbed_sub {N : ℕ} (R : Fin N → V ≃ₗᵢ[ℝ] V) (k : Fin N) (p q : V) :
    fiberEmbed R k p - fiberEmbed R k q = R k (p - q) := by
  simp only [fiberEmbed, map_sub]
  abel

theorem fiberEmbed_injective {N : ℕ} (R : Fin N → V ≃ₗᵢ[ℝ] V) (k : Fin N) :
    Function.Injective (fiberEmbed R k) := by
  intro p q he
  exact (R k).injective (add_right_cancel he)

/-- Small balls from different coarse labels are separated by their
vertical translations, even after each label receives its own rotation. -/
theorem fiberEmbed_label_eq {N : ℕ} (R : Fin N → V ≃ₗᵢ[ℝ] V)
    {k k' : Fin N} {p q : V} (hp : ‖p‖ ≤ 2) (hq : ‖q‖ ≤ 2)
    (hclose : ‖fiberEmbed R k p - fiberEmbed R k' q‖ ≤ 1) : k = k' := by
  have hs : fiberShift k - fiberShift k' =
      (fiberEmbed R k p - fiberEmbed R k' q) - R k p + R k' q := by
    dsimp only [fiberEmbed]
    abel
  have hnorm : ‖fiberShift k - fiberShift k'‖ ≤ 5 := by
    rw [hs]
    have h1 := norm_add_le (fiberEmbed R k p - fiberEmbed R k' q - R k p) (R k' q)
    have h2 := norm_sub_le (fiberEmbed R k p - fiberEmbed R k' q) (R k p)
    rw [(R k).norm_map] at h2
    rw [(R k').norm_map] at h1
    linarith
  have he : ‖fiberShift k - fiberShift k'‖ = 10 * |(k.val : ℝ) - k'.val| := by
    rw [fiberShift, fiberShift, ← sub_smul, norm_smul, Real.norm_eq_abs,
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one, mul_one,
      show 10 * (k.val : ℝ) - 10 * (k'.val : ℝ) = 10 * ((k.val : ℝ) - k'.val) by ring,
      abs_mul]
    norm_num
  rw [he] at hnorm
  have hdiff : |(k.val : ℝ) - k'.val| < 1 := by linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hdiff
  have h₁ : (k.val : ℝ) < (k'.val : ℝ) + 1 := by linarith
  have h₂ : (k'.val : ℝ) < (k.val : ℝ) + 1 := by linarith
  have h₁' : k.val < k'.val + 1 := by exact_mod_cast h₁
  have h₂' : k'.val < k.val + 1 := by exact_mod_cast h₂
  exact Fin.ext (by omega)

theorem fiberEmbed_mem_prism {N : ℕ} (R : Fin N → V ≃ₗᵢ[ℝ] V) (k : Fin N)
    (e : V ≃ₗᵢ[ℝ] V) (a b c : ℝ) (z p : V) :
    fiberEmbed R k p ∈ P a b c (fiberEmbed R k z) (rotatedFrame (R k) e) ↔
      p ∈ P a b c z e := by
  simp only [P, WangZahlLot.Obl.wz_clustered_cover_volume_gain.ι, Set.mem_ofPred_eq,
    fiberEmbed_sub, rotatedFrame_apply]

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
