-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Schedule, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit c3fccb87c, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/Schedule.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- The same-N virtual schedule for returning candidates from an ancestor packet (x1078, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.DirectReturn

/-!
# Virtual packets below an ancestor, at the same `N`

A packet `b` (depth `rb`, clock `Tb`, block `jb`) lies below an ancestor `A` (depth `rA`, clock
`TA`, block `jA`). The virtual instance uses the same `N`, the remaining depth `Lt = L - rA`,
the gain `gain * L / Lt`, the relative depth `rb - rA`, clock `Tb - TA` and block
`jb - jA * 2^(Tb - TA)`. Its depth gain `agt` returns as `ag = agt * Lt / L`, with the same final
depth. The dyadic thickness `δ` is multiplicative up to a factor two (`δ_add_le`, `δ_le_two_mul`),
and the slack `N^(ε - εt) ≥ 2` pays for it. `hpar_virtual` is exactly the hypothesis `hpar` of
`directAt_return`; `block_iff_virtual` gives its block hypotheses.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split

noncomputable section

lemma δ_eq (N x : ℝ) : Split.δ N x = (2:ℝ) ^ (-(⌊x * Real.log N / Real.log 2⌋ : ℤ)) := rfl

lemma δ_pos (N x : ℝ) : 0 < Split.δ N x := by rw [δ_eq]; positivity

/-- Dyadic thickness is super-multiplicative: `δ(x + y) ≤ δ(x) δ(y)`. -/
lemma δ_add_le (N x y : ℝ) : Split.δ N (x + y) ≤ Split.δ N x * Split.δ N y := by
  rw [δ_eq, δ_eq, δ_eq, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
  have h : x * Real.log N / Real.log 2 + y * Real.log N / Real.log 2 =
      (x + y) * Real.log N / Real.log 2 := by ring
  have := Int.le_floor_add (x * Real.log N / Real.log 2) (y * Real.log N / Real.log 2)
  rw [h] at this
  omega

/-- and multiplicative up to a factor two. -/
lemma δ_le_two_mul (N x y : ℝ) : Split.δ N x * Split.δ N y ≤ 2 * Split.δ N (x + y) := by
  rw [δ_eq, δ_eq, δ_eq, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  have h : x * Real.log N / Real.log 2 + y * Real.log N / Real.log 2 =
      (x + y) * Real.log N / Real.log 2 := by ring
  have hf : ⌊(x + y) * Real.log N / Real.log 2⌋ ≤
      ⌊x * Real.log N / Real.log 2⌋ + ⌊y * Real.log N / Real.log 2⌋ + 1 := by
    have h1 := Int.floor_le ((x + y) * Real.log N / Real.log 2)
    have h2 := Int.lt_floor_add_one (x * Real.log N / Real.log 2)
    have h3 := Int.lt_floor_add_one (y * Real.log N / Real.log 2)
    have h4 : ((⌊(x + y) * Real.log N / Real.log 2⌋ : ℤ) : ℝ) <
        ((⌊x * Real.log N / Real.log 2⌋ + ⌊y * Real.log N / Real.log 2⌋ + 2 : ℤ) : ℝ) := by
      push_cast; linarith
    have h5 := Int.cast_lt.mp h4
    omega
  calc (2:ℝ) ^ (-(⌊x * Real.log N / Real.log 2⌋ : ℤ) + -(⌊y * Real.log N / Real.log 2⌋ : ℤ))
      ≤ (2:ℝ) ^ ((1:ℤ) + -(⌊(x + y) * Real.log N / Real.log 2⌋ : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 2 * (2:ℝ) ^ (-(⌊(x + y) * Real.log N / Real.log 2⌋ : ℤ)) := by
        rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]

/-- The exponent and thickness bookkeeping of `directAt_return` for the same-`N` schedule. -/
theorem hpar_virtual (N L d₁ ρ gain ε εt rA rb : ℝ) (Tb TA : ℕ)
    (hN : 1 ≤ N) (hgain : 0 ≤ gain) (hrA : 0 ≤ rA) (hrAL : rA < L) (hεt : εt ≤ ε)
    (htwo : 2 ≤ N ^ (ε - εt)) (hT : TA ≤ Tb) :
    ∀ agt : ℝ, gain * L / (L - rA) ≤ agt → agt ≤ 1/8 →
      (rb - rA) + 2*agt*(L - rA) ≤ L - rA → ∃ ag : ℝ,
      gain ≤ ag ∧ ag ≤ 1/8 ∧ rb + 2*ag*L ≤ L ∧
      Split.δ N rA * (N^(ρ*(gain * L / (L - rA))*(L - rA)+εt) *
          Split.δ N ((rb - rA) + agt*(L - rA))) ≤ N^(ρ*gain*L+ε) * Split.δ N (rb + ag*L) ∧
      N^(ρ*(gain * L / (L - rA))*(L - rA)+εt) ≤ N^(ρ*gain*L+ε) ∧
      N^(ρ*(gain * L / (L - rA))*(L - rA)+εt) * Split.δ N (rb + ag*L) ≤
        N^(ρ*gain*L+ε) * Split.δ N rA * Split.δ N ((rb - rA) + agt*(L - rA)) ∧
      ENNReal.ofReal (N^(-((d₁*ag+ρ*gain)*L) - ε)/(2:ℝ)^Tb) ≤
        ENNReal.ofReal ((2:ℝ)^TA)⁻¹ * ENNReal.ofReal
          (N^(-((d₁*agt+ρ*(gain * L / (L - rA)))*(L - rA)) - εt)/(2:ℝ)^(Tb - TA)) := by
  intro agt hgt hgt8 hrt
  have hLt : 0 < L - rA := sub_pos.mpr hrAL
  have hL : 0 < L := hrA.trans_lt hrAL
  refine ⟨agt * (L - rA) / L, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hL]
    have := (div_le_iff₀ hLt).mp hgt
    linarith
  · have hagt0 : 0 ≤ agt := le_trans (by positivity) hgt
    calc agt * (L - rA) / L ≤ agt * L / L := by gcongr; linarith
      _ = agt := by field_simp
      _ ≤ 1/8 := hgt8
  · have : agt * (L - rA) / L * L = agt * (L - rA) := by field_simp
    nlinarith
  · have hdepth : rb + agt * (L - rA) / L * L = rA + ((rb - rA) + agt * (L - rA)) := by
      field_simp; ring
    have hslack : ρ*(gain * L / (L - rA))*(L - rA)+εt = ρ*gain*L+εt := by field_simp
    rw [hdepth, hslack]
    have h2 := δ_le_two_mul N rA ((rb - rA) + agt * (L - rA))
    have hpow : 2 * N ^ (ρ*gain*L+εt) ≤ N ^ (ρ*gain*L+ε) := by
      calc 2 * N ^ (ρ*gain*L+εt) ≤ N ^ (ε - εt) * N ^ (ρ*gain*L+εt) := by
            gcongr
        _ = N ^ (ρ*gain*L+ε) := by
            rw [← Real.rpow_add (by linarith)]; ring_nf
    have hN0 : 0 ≤ N ^ (ρ*gain*L+εt) := by positivity
    calc Split.δ N rA * (N ^ (ρ*gain*L+εt) * Split.δ N ((rb - rA) + agt * (L - rA)))
        = N ^ (ρ*gain*L+εt) * (Split.δ N rA * Split.δ N ((rb - rA) + agt * (L - rA))) := by ring
      _ ≤ N ^ (ρ*gain*L+εt) * (2 * Split.δ N (rA + ((rb - rA) + agt * (L - rA)))) := by gcongr
      _ = (2 * N ^ (ρ*gain*L+εt)) * Split.δ N (rA + ((rb - rA) + agt * (L - rA))) := by ring
      _ ≤ N ^ (ρ*gain*L+ε) * Split.δ N (rA + ((rb - rA) + agt * (L - rA))) := by
          gcongr; exact (δ_pos _ _).le
  · have hslack : ρ*(gain * L / (L - rA))*(L - rA)+εt = ρ*gain*L+εt := by field_simp
    rw [hslack]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · have hdepth : rb + agt * (L - rA) / L * L = rA + ((rb - rA) + agt * (L - rA)) := by
      field_simp; ring
    have hslack : ρ*(gain * L / (L - rA))*(L - rA)+εt = ρ*gain*L+εt := by field_simp
    rw [hdepth, hslack]
    have h1 := δ_add_le N rA ((rb - rA) + agt * (L - rA))
    have hle : N ^ (ρ*gain*L+εt) ≤ N ^ (ρ*gain*L+ε) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    calc N ^ (ρ*gain*L+εt) * Split.δ N (rA + ((rb - rA) + agt * (L - rA)))
        ≤ N ^ (ρ*gain*L+ε) * (Split.δ N rA * Split.δ N ((rb - rA) + agt * (L - rA))) :=
          mul_le_mul hle h1 (δ_pos _ _).le (by positivity)
      _ = _ := by ring
  · have hexp : (d₁*(agt * (L - rA) / L)+ρ*gain)*L =
        (d₁*agt+ρ*(gain * L / (L - rA)))*(L - rA) := by field_simp
    rw [hexp, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h2 : (2:ℝ) ^ Tb = (2:ℝ) ^ TA * (2:ℝ) ^ (Tb - TA) := by
      rw [← pow_add, Nat.add_sub_cancel' hT]
    rw [h2]
    have hN0 : 0 < N := by linarith
    have hle : N ^ (-((d₁*agt+ρ*(gain * L / (L - rA)))*(L - rA)) - ε) ≤
        N ^ (-((d₁*agt+ρ*(gain * L / (L - rA)))*(L - rA)) - εt) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    calc N ^ (-((d₁*agt+ρ*(gain * L / (L - rA)))*(L - rA)) - ε) / ((2:ℝ)^TA * (2:ℝ)^(Tb - TA))
        ≤ N ^ (-((d₁*agt+ρ*(gain * L / (L - rA)))*(L - rA)) - εt) /
            ((2:ℝ)^TA * (2:ℝ)^(Tb - TA)) := by gcongr
      _ = ((2:ℝ)^TA)⁻¹ * (N ^ (-((d₁*agt+ρ*(gain * L / (L - rA)))*(L - rA)) - εt) /
            (2:ℝ)^(Tb - TA)) := by field_simp

/-- Dyadic blocks: the packet's block is the ancestor's block rescaled. -/
theorem block_iff_virtual (TA Tb jA jb : ℕ) (hT : TA ≤ Tb)
    (hj : jA * 2 ^ (Tb - TA) ≤ jb) (t : ℝ) :
    t ∈ Set.Icc ((jb:ℝ)/(2:ℝ)^Tb) (((jb:ℝ)+1)/(2:ℝ)^Tb) ↔
      (t - (jA:ℝ)/(2:ℝ)^TA) / ((2:ℝ)^TA)⁻¹ ∈
        Set.Icc (((jb - jA * 2 ^ (Tb - TA) : ℕ):ℝ)/(2:ℝ)^(Tb - TA))
          ((((jb - jA * 2 ^ (Tb - TA) : ℕ):ℝ)+1)/(2:ℝ)^(Tb - TA)) := by
  have h2 : (2:ℝ) ^ Tb = (2:ℝ) ^ TA * (2:ℝ) ^ (Tb - TA) := by
    rw [← pow_add, Nat.add_sub_cancel' hT]
  have hcast : (((jb - jA * 2 ^ (Tb - TA) : ℕ)):ℝ) = (jb:ℝ) - (jA:ℝ) * (2:ℝ)^(Tb - TA) := by
    rw [Nat.cast_sub hj]; push_cast; ring
  rw [hcast]
  have hA : (0:ℝ) < (2:ℝ)^TA := by positivity
  have hB : (0:ℝ) < (2:ℝ)^(Tb - TA) := by positivity
  simp only [Set.mem_Icc, div_inv_eq_mul, h2]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · rw [div_le_iff₀ hB]
      have := (div_le_iff₀ (mul_pos hA hB)).mp h0
      have e : (t - (jA:ℝ) / (2:ℝ)^TA) * (2:ℝ)^TA = t * (2:ℝ)^TA - jA := by field_simp
      rw [e]; nlinarith
    · rw [le_div_iff₀ hB]
      have := (le_div_iff₀ (mul_pos hA hB)).mp h1
      have e : (t - (jA:ℝ) / (2:ℝ)^TA) * (2:ℝ)^TA = t * (2:ℝ)^TA - jA := by field_simp
      rw [e]; nlinarith
  · rintro ⟨h0, h1⟩
    have e : (t - (jA:ℝ) / (2:ℝ)^TA) * (2:ℝ)^TA = t * (2:ℝ)^TA - jA := by field_simp
    rw [e] at h0 h1
    constructor
    · rw [div_le_iff₀ (mul_pos hA hB)]
      have := (div_le_iff₀ hB).mp h0
      nlinarith
    · rw [le_div_iff₀ (mul_pos hA hB)]
      have := (le_div_iff₀ hB).mp h1
      nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
