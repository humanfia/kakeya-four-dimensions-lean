/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, FrozenGroupBand.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.PolynomialGroupBand
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.JointScales

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- One eventual set supports ALL hidden exponents in a fixed compact
range. A physical radius may then be chosen after the sample index. -/
theorem Valid.eventually_native_fine_joint_cap_range (h : cfg.Valid)
    (s r a : ℝ) (hs : 0 ≤ s) (hr : 0 < r) (ha : 0 < a) :
    ∀ᶠ k in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ s →
      cfg.NativeFineJointCap k u (cfg.N k ^ (-r)) (cfg.N k ^ (-a)) := by
  let R := 2 + r + s + a + r⁻¹ + a⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr ha]
  have hRpos : 0 < R := by linarith
  have hrR : r ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr ha]
  have hsR : s ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr ha]
  have haR : a ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr ha]
  have hRr : R⁻¹ ≤ r := by
    apply (inv_le_comm₀ hRpos hr).mpr
    dsimp [R]
    linarith [inv_pos.mpr ha]
  have hRa : R⁻¹ ≤ a := by
    apply (inv_le_comm₀ hRpos ha).mpr
    dsimp [R]
    linarith [inv_pos.mpr hr]
  filter_upwards [h.caps R hR] with k hk
  intro u hu hus q b j
  have hn : 0 < cfg.N k := by linarith [h.scale k]
  have hscale : cfg.N k ^ (-3 * r - cfg.d * u) =
      (cfg.N k ^ (-r)) ^ 3 * (cfg.N k ^ (-u)) ^ cfg.d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    congr 1
    ring
  have hh := (hk r u a hRr hrR hu (hus.trans hsR) hRa haR).2.2 false q b j
  rw [hscale] at hh
  have hzeq : cfg.z k (cfg.N k) r = fun (p : α × ℝ) (e : Fin 3) =>
      ⌊(![p.2, cfg.b k p.1 0 + p.2 * cfg.b k p.1 3,
        cfg.b k p.1 1 + p.2 * cfg.b k p.1 4] : Fin 3 → ℝ) e / (cfg.N k ^ (-r))⌋ := rfl
  rw [hzeq] at hh
  simpa [Data.x, mul_assoc] using hh

/-- Uniform physical-radius polynomial-band bound on the original dense
residual. The reference palette bin is unchanged by group restriction. -/
theorem original_group_polynomial_band_cap (h : cfg.Valid) {k : ℕ} {s r v : ℝ}
    (caps : ∀ u : ℝ, 0 ≤ u → u ≤ s →
      cfg.NativeFineJointCap k u (cfg.N k ^ (-r)) (cfg.N k ^ (-v)))
    (U : Set (α × ℝ)) (p : Fin 3 → ℝ) (j : ℤ)
    (R H m c₀ c₁ c₂ : ℝ) (hR : cfg.N k ^ (-s) ≤ R) (hR1 : R ≤ 1) (hH : 0 ≤ H)
    (hp₀ : |p 0| ≤ cfg.K k) (hp₂ : |p 2| ≤ cfg.K k)
    (hc₁ : |c₁| ≤ 16 * cfg.K k) (hc₂ : |c₂| ≤ R)
    (hδD : 16 * cfg.K k * cfg.N k ^ (-r) ≤ cfg.N k ^ (-s))
    (hδR : 3 * cfg.N k ^ (-r) ≤ cfg.N k ^ (-s))
    (hunit : ∀ y ∈ U, y.2 ∈ Icc (0 : ℝ) 1)
    (htime : ∀ y ∈ U, |y.2 - m| ≤ H / 2)
    (hb₀ : ∀ y ∈ U, |cfg.b k y.1 0 - p 0| ≤ cfg.N k ^ (-s))
    (hb₁ : ∀ y ∈ U, |cfg.b k y.1 1 - p 1| ≤ cfg.N k ^ (-s))
    (hvel : ∀ y ∈ U, |cfg.b k y.1 3 - p 2| ≤ cfg.N k ^ (-s))
    (hdef : ∀ y ∈ U, |cfg.b k y.1 4 + cfg.b k y.1 0| ≤ cfg.N k ^ (-s))
    (hvelocity : ∀ y ∈ U, ⌊cfg.b k y.1 3 / cfg.N k ^ (-v)⌋ = j)
    (hband : ∀ y ∈ U,
      |(cfg.x k y.1 y.2) 3 - (c₀ + c₁ * y.2 + c₂ * y.2 ^ 2)| ≤ 3 * R) :
    cfg.ρ k U ≤ ENNReal.ofReal
      (23040 * cfg.K k ^ 2 * (H + cfg.N k ^ (-r)) * (cfg.N k ^ (-s)) ^ 2 * R ^ cfg.d) *
        cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = j} := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hNgt : 1 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hRp : 0 < R := (Real.rpow_pos_of_pos hN _).trans_le hR
  let u := -Real.logb (cfg.N k) R
  have hu : 0 ≤ u := by
    have hh := (Real.logb_le_iff_le_rpow hNgt hRp).mpr
      (by simpa using hR1 : R ≤ cfg.N k ^ (0 : ℝ))
    dsimp [u]
    linarith
  have hus : u ≤ s := by
    have hh := (Real.le_logb_iff_rpow_le hNgt hRp).mpr hR
    dsimp [u]
    linarith
  have hscale : cfg.N k ^ (-u) = R := by
    dsimp [u]
    simpa only [neg_neg] using Real.rpow_logb hN (ne_of_gt hNgt) hRp
  have hcap := caps u hu hus
  have hKG : cfg.K k ≤ 16 * cfg.K k := by linarith
  have hh := original_native_group_polynomial_band_cap_window (cfg.μ k) U
    (fun y : α × ℝ => cfg.b k y.1) Prod.snd
    (fun y : α × ℝ => ⌊cfg.b k y.1 3 / cfg.N k ^ (-v)⌋) j
    (cfg.N k ^ (-r)) R H (cfg.N k ^ (-s)) (16 * cfg.K k) m (cfg.K k) cfg.d
    c₀ c₁ c₂ (cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = j}) p
    (Real.rpow_pos_of_pos hN _) hRp hH (by linarith) hK0 hδD (hδR.trans hR)
    (hp₀.trans hKG) (hp₂.trans hKG) hc₁ hc₂ htime (by
      intro y hy
      rw [abs_of_nonneg (hunit y hy).1]
      exact (hunit y hy).2) hb₀ hb₁ hvel hdef hband hvelocity (by
      intro q n
      have hh := hcap q n j
      rw [hscale] at hh
      exact hh)
  apply ((h.basic k).2.2.2.2.1 U).trans
  convert hh using 1
  congr 2
  ring


/-- The band cap holds uniformly in every physical radius and time window,
after one fixed original mesh and one sample threshold have been chosen. -/
theorem Valid.eventually_group_polynomial_band_cap (h : cfg.Valid)
    (s v η : ℝ) (hs : 0 ≤ s) (hv : 0 < v) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop,
      ∀ (U : Set (α × ℝ)) (p : Fin 3 → ℝ) (j : ℤ) (R H m c₀ c₁ c₂ : ℝ),
      cfg.N k ^ (-s) ≤ R → R ≤ 1 → 0 ≤ H →
      |p 0| ≤ cfg.K k → |p 2| ≤ cfg.K k →
      |c₁| ≤ 16 * cfg.K k → |c₂| ≤ R →
      (∀ y ∈ U, y.2 ∈ Icc (0 : ℝ) 1) →
      (∀ y ∈ U, |y.2 - m| ≤ H / 2) →
      (∀ y ∈ U, |cfg.b k y.1 0 - p 0| ≤ cfg.N k ^ (-s)) →
      (∀ y ∈ U, |cfg.b k y.1 1 - p 1| ≤ cfg.N k ^ (-s)) →
      (∀ y ∈ U, |cfg.b k y.1 3 - p 2| ≤ cfg.N k ^ (-s)) →
      (∀ y ∈ U, |cfg.b k y.1 4 + cfg.b k y.1 0| ≤ cfg.N k ^ (-s)) →
      (∀ y ∈ U, ⌊cfg.b k y.1 3 / cfg.N k ^ (-v)⌋ = j) →
      (∀ y ∈ U, |(cfg.x k y.1 y.2) 3 -
        (c₀ + c₁ * y.2 + c₂ * y.2 ^ 2)| ≤ 3 * R) →
      cfg.ρ k U ≤ ENNReal.ofReal
        (cfg.N k ^ η * (H + cfg.N k ^ (-r)) * (cfg.N k ^ (-s)) ^ 2 * R ^ cfg.d) *
          cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = j} := by
  let r := 2 * (s + v + 1)
  have hr : 0 < r := by dsimp [r]; linarith
  have hNone : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hmesh₁ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone h.scale_limit h.subpower.1 h.subpower.2 1
    (show -r < -s by dsimp [r]; linarith) (show (0 : ℝ) ≤ 16 by norm_num)
  have hmesh₂ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    h.scale_limit (show -r < -s by dsimp [r]; linarith) (3 : ℝ)
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone h.scale_limit h.subpower.1 h.subpower.2 2 hη
    (show (0 : ℝ) ≤ 23040 by norm_num)
  refine ⟨r, hr, ?_⟩
  filter_upwards [h.eventually_native_fine_joint_cap_range s r v hs hr hv,
    hmesh₁, hmesh₂, hcost] with k caps hk₁ hk₂ hk₃
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hmeshD : 16 * cfg.K k * cfg.N k ^ (-r) ≤ cfg.N k ^ (-s) := by
    simpa only [pow_one] using hk₁.le
  have hcost' : 23040 * cfg.K k ^ 2 ≤ cfg.N k ^ η := by
    simpa only [Real.rpow_zero, mul_one] using hk₃.le
  intro U p j R H m c₀ c₁ c₂ hR hR1 hH hp₀ hp₂ hc₁ hc₂ hunit htime hb₀ hb₁ hvel hdef hvelocity hband
  have hRp : 0 < R := (Real.rpow_pos_of_pos hN _).trans_le hR
  have hh := original_group_polynomial_band_cap h caps U p j R H m c₀ c₁ c₂ hR hR1 hH
    hp₀ hp₂ hc₁ hc₂ hmeshD hk₂.le hunit htime hb₀ hb₁ hvel hdef hvelocity hband
  refine hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  have hfac : 0 ≤ (H + cfg.N k ^ (-r)) * (cfg.N k ^ (-s)) ^ 2 * R ^ cfg.d := by positivity
  have hm := mul_le_mul_of_nonneg_right hcost' hfac
  convert hm using 1 <;> ring

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
