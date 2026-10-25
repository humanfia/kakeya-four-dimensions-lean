-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AngularDensityScalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AngularDensityScalar.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NonflatPowers

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- Saturation replaces the surviving body mass by the original container
volume while retaining the positive concentration power. -/
theorem concentration_count_factor {M C N w V₀ σ : ℝ}
    (hM : 0 < M) (hC : 0 < C) (hsat : M * V₀ ≤ C * N * w) :
    (M ^ (σ / 2) / C) * V₀ ≤ M ^ (-1 + σ / 2) * (N * w) := by
  have hratio : (M / C) * V₀ ≤ N * w := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    nlinarith only [hsat]
  have hmexp : M ^ (-1 + σ / 2) * M = M ^ (σ / 2) := by
    calc
      _ = M ^ (-1 + σ / 2) * M ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = M ^ (σ / 2) := by rw [← Real.rpow_add hM]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hM.le (-1 + σ / 2))
  calc
    _ = M ^ (-1 + σ / 2) * ((M / C) * V₀) := by rw [← hmexp]; ring
    _ ≤ _ := hh

/-- The sharp normalized geometry separates into the ball-density scale
and the sigma-only aspect penalty. -/
theorem sharp_packet_geometry_factor {ρ a b σ ω : ℝ}
    (hρ : 0 < ρ) (ha : 0 < a) (hb : 0 < b) :
    ((ρ / 100) / (8192 * a)) ^ ω * ((ρ ^ 2 / 64) / (4 * a * b)) ^ (σ / 2) =
      (16 : ℝ) ^ (-σ) * (819200 : ℝ) ^ (-ω) *
        (ρ / a) ^ (σ + ω) * (a / b) ^ (σ / 2) := by
  have he : (ρ / 100) / (8192 * a) = ρ / (819200 * a) := by ring
  rw [he]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; norm_num
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
  rw [h4, h16, h64]
  ring

/-- Saturation of the original block can be used with the sharper geometry
of each angular packet. -/
theorem saturated_packet_density_factor {A C δ ρ a b M P N V₀ σ ω e l : ℝ}
    (hA : 0 ≤ A) (hC : 0 < C) (hδ : 0 < δ) (hρ : 0 < ρ)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hP : 0 ≤ P)
    (hsat : M * V₀ ≤ C * N * (ρ ^ 2 / 64)) :
    (A / C * (16 : ℝ) ^ (-σ) * (819200 : ℝ) ^ (-ω)) * δ ^ (2 * e + l) *
        M ^ (σ / 2) * P ^ (-σ) * (a / b) ^ (σ / 2) *
        ((ρ / a) ^ (σ + ω) * V₀) ≤
      A * (δ ^ (2 : ℕ)) ^ e * ((ρ / 100) / (8192 * a)) ^ ω *
        M ^ (-1 + σ / 2) * P ^ (-σ) *
        ((ρ ^ 2 / 64) / (4 * a * b)) ^ (σ / 2) * δ ^ l * N * (ρ ^ 2 / 64) := by
  have hc := concentration_count_factor (σ := σ) hM hC hsat
  let F := A * (δ ^ (2 : ℕ)) ^ e *
    (((ρ / 100) / (8192 * a)) ^ ω * ((ρ ^ 2 / 64) / (4 * a * b)) ^ (σ / 2)) *
    P ^ (-σ) * δ ^ l
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hh := mul_le_mul_of_nonneg_left hc hF
  have hp : (δ ^ (2 : ℕ)) ^ e * δ ^ l = δ ^ (2 * e + l) := by
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    norm_num
  have heq : F * (M ^ (σ / 2) / C * V₀) =
      (A / C * (16 : ℝ) ^ (-σ) * (819200 : ℝ) ^ (-ω)) * δ ^ (2 * e + l) *
        M ^ (σ / 2) * P ^ (-σ) * (a / b) ^ (σ / 2) *
        ((ρ / a) ^ (σ + ω) * V₀) := by
    dsimp [F]
    rw [sharp_packet_geometry_factor hρ ha hb, ← hp]
    ring
  rw [heq] at hh
  convert hh using 1 <;> dsimp [F] <;> ring

/-- Flatness of the packet intersection forces its angular scale above the
old short side, by a power independent of sigma. -/
theorem angular_scale_of_prism_aspect {δ ζ a θ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 < ζ) (ha : 0 < a) (hθ : 0 < θ)
    (hsmall : 80 * δ ^ (ζ / 8) ≤ 36)
    (haspect : min (36 * a) (min (80 * θ) 4) / min (80 * θ) 4 < δ ^ (ζ / 4)) :
    δ ^ (-(ζ / 8)) * a ≤ θ := by
  let B := min (80 * θ) 4
  have hB : 0 < B := lt_min (by positivity) (by norm_num)
  have hratio : min (36 * a) B / B < 1 := haspect.trans_le
    (Real.rpow_le_one hδ.le hδ1 (by positivity))
  have hlt : min (36 * a) B < B := (div_lt_one hB).mp hratio
  have hshort : 36 * a < B := (min_lt_iff.mp hlt).resolve_right (lt_irrefl _)
  change min (36 * a) B / B < _ at haspect
  rw [min_eq_left hshort.le] at haspect
  have hmain : 36 * a < δ ^ (ζ / 4) * B := (div_lt_iff₀ hB).mp haspect
  have hBθ : B ≤ 80 * θ := min_le_left _ _
  have hpow : δ ^ (ζ / 4) = δ ^ (ζ / 8) * δ ^ (ζ / 8) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hbound : δ ^ (ζ / 4) * B ≤ 36 * δ ^ (ζ / 8) * θ := by
    calc
      _ ≤ δ ^ (ζ / 4) * (80 * θ) := mul_le_mul_of_nonneg_left hBθ (by positivity)
      _ = (80 * δ ^ (ζ / 8)) * (δ ^ (ζ / 8) * θ) := by rw [hpow]; ring
      _ ≤ 36 * (δ ^ (ζ / 8) * θ) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = _ := by ring
  have haθ : a ≤ δ ^ (ζ / 8) * θ := by linarith [hmain.trans_le hbound]
  have hh := mul_le_mul_of_nonneg_left haθ (Real.rpow_nonneg hδ.le (-(ζ / 8)))
  have hcancel : δ ^ (-(ζ / 8)) * δ ^ (ζ / 8) = 1 := by rw [← Real.rpow_add hδ]; simp
  simpa only [← mul_assoc, hcancel, one_mul] using hh

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
