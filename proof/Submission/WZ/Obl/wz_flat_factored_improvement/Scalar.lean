-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Scalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_flat_factored_improvement

/-- The real-valued expression in the general tube estimate. -/
noncomputable def profile (σ w ε A δ m l N : ℝ) : ℝ :=
  A * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) *
    (m ^ (-(3 / 2 : ℝ)) * l * (N * δ)) ^ (-σ)

/-- Separating the positive variables exposes both monotonicities needed for restriction. -/
theorem profile_eq {σ w ε A δ m l N : ℝ}
    (hδ : 0 < δ) (hm : 0 < m) (hl : 0 < l) (hN : 0 < N) :
    profile σ w ε A δ m l N =
      A * δ ^ (w + ε + 2 - σ) * m ^ (-1 + 3 / 2 * σ) *
        l ^ (-σ) * N ^ (1 - σ) := by
  unfold profile
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hm.le _) hl.le)
      (mul_nonneg hN.le hδ.le),
    Real.mul_rpow (Real.rpow_nonneg hm.le _) hl.le,
    Real.mul_rpow hN.le hδ.le, ← Real.rpow_mul hm.le]
  rw [show -(3 / 2 : ℝ) * -σ = 3 / 2 * σ by ring]
  rw [show w + ε + 2 - σ = (w + ε) + 2 + -σ by ring,
    Real.rpow_add hδ (w + ε + 2) (-σ),
    Real.rpow_add hδ (w + ε) 2, Real.rpow_two,
    Real.rpow_add hm, Real.rpow_neg_one, sub_eq_add_neg,
    Real.rpow_add hN, Real.rpow_one]
  ring

/-- Flatness provides the full aspect-ratio gain. -/
theorem aspect_gain {δ a b β u : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hb : 0 < b) (hu : 0 ≤ u) (hflat : a ≤ δ ^ β * b) :
    δ ^ (-(β * u)) ≤ (b / a) ^ u := by
  have hratio : δ ^ (-β) ≤ b / a := by
    rw [Real.rpow_neg hδ.le]
    apply (le_div_iff₀ ha).mpr
    apply (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hδ β)).mpr
    simpa only [mul_comm] using hflat
  calc
    δ ^ (-(β * u)) = (δ ^ (-β)) ^ u := by
      rw [← Real.rpow_mul hδ.le]
      congr 1
      ring
    _ ≤ (b / a) ^ u := Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hratio hu

/-- The flatness gain absorbs retention and the inherited slab loss. -/
theorem flat_profile_transfer {σ u ε A δ ν β a b c m k n : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hu : 0 < u) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hβ : 0 < β)
    (hνsmall : ν ≤ β * u / 4)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcm : c ≤ m)
    (hn : 0 < n) (hkn : δ ^ ν * n ≤ k) (hflat : a ≤ δ ^ β * b) :
    profile σ (u - β * u / 2) ε A δ m 1 n ≤
      (b / a) ^ u * profile σ u ε A δ c (δ ^ (-2 * ν)) k := by
  have hm : 0 < m := hc.trans_le hcm
  have hk : 0 < k := (mul_pos (Real.rpow_pos_of_pos hδ _) hn).trans_le hkn
  have hp : 0 ≤ 1 - σ := by linarith
  have hmexp : -1 + 3 / 2 * σ ≤ 0 := by linarith
  rw [profile_eq hδ hm (by norm_num) hn, profile_eq hδ hc (Real.rpow_pos_of_pos hδ _) hk,
    Real.one_rpow, mul_one]
  have hcount : δ ^ (ν * (1 - σ)) * n ^ (1 - σ) ≤ k ^ (1 - σ) := by
    rw [Real.rpow_mul hδ.le, ← Real.mul_rpow (Real.rpow_nonneg hδ.le _) hn.le]
    exact Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hδ.le _) hn.le) hkn hp
  have hcoeff : m ^ (-1 + 3 / 2 * σ) ≤ c ^ (-1 + 3 / 2 * σ) :=
    Real.rpow_le_rpow_of_nonpos hc hcm hmexp
  have hexp : u + ε - β * u + ν * (1 + σ) ≤ u - β * u / 2 + ε := by
    have hprod : ν * (1 + σ) ≤ β * u / 2 := by
      have hnonneg : 0 ≤ β * u := (mul_pos hβ hu).le
      nlinarith
    linarith
  have hδexp : δ ^ (u - β * u / 2 + ε + 2 - σ) ≤
      δ ^ (u + ε + 2 - σ - β * u + ν * (1 + σ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  calc
    A * δ ^ (u - β * u / 2 + ε + 2 - σ) * m ^ (-1 + 3 / 2 * σ) *
        n ^ (1 - σ) ≤
      A * δ ^ (u + ε + 2 - σ - β * u + ν * (1 + σ)) *
        c ^ (-1 + 3 / 2 * σ) * n ^ (1 - σ) := by
      gcongr
    _ = δ ^ (-(β * u)) *
        (A * δ ^ (u + ε + 2 - σ) * c ^ (-1 + 3 / 2 * σ) *
          (δ ^ (-2 * ν)) ^ (-σ) * (δ ^ (ν * (1 - σ)) * n ^ (1 - σ))) := by
      rw [← Real.rpow_mul hδ.le,
        show u + ε + 2 - σ - β * u + ν * (1 + σ) =
          -(β * u) + (u + ε + 2 - σ) + (-2 * ν) * (-σ) + ν * (1 - σ) by ring,
        Real.rpow_add hδ, Real.rpow_add hδ, Real.rpow_add hδ]
      ring
    _ ≤ (b / a) ^ u *
        (A * δ ^ (u + ε + 2 - σ) * c ^ (-1 + 3 / 2 * σ) *
          (δ ^ (-2 * ν)) ^ (-σ) * k ^ (1 - σ)) := by
      apply mul_le_mul (aspect_gain hδ ha hb hu.le hflat) _
        (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hcount (by positivity)

end WangZahlLot.Obl.wz_flat_factored_improvement
