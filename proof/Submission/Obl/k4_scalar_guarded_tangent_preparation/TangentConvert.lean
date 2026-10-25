import Submission.Obl.k4_scalar_guarded_tangent_preparation.CellTangent
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CompletionAux

/-!
# From original chart data to tangent bounds

`pieceFacts_of_chartData` reads the facts of one kept piece off the true chart data with
slack `N₀^ε = H`. `tangent_exponents` converts the original depth `r = sc * dp` and the
original profile value `F` into the tangent depth `s`, given the profile bound
`N₀^{|F - d r|} ≤ B` and the node rounding `N^{|dp - s|} ≤ B` with `N = N₀^sc`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The facts of one kept piece of a true layer. -/
theorem pieceFacts_of_chartData {p : Code} {m : ℕ} {σ ρ : Fin (p.1 m) → Measure Incidence}
    {Bc : ℕ} {r b h H B F : ℝ} {T n : ℕ} {γ : Fin n → Fin (p.1 m)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Coeff} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ} {Λ : Fin (p.1 m) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hCD : Split.ChartData p Bc r b h (Real.log H / Real.log (p.N m)) true m T n γ j A C u v J P Λ)
    (hN : 1 < p.N m) (hH : 2 ≤ H) (hB : 1 ≤ B) (hr : 0 ≤ r) (hF : F = p.profile r)
    (hJ : ∀ i, (H * (2 : ℝ) ^ T)⁻¹ ≤ J i)
    (hceil : ∀ g, (σ g).map (pureObservation (p.N m) r) ≤
      ENNReal.ofReal (B * p.N m ^ (-F)) • (volume.prod Measure.count))
    (hρσ : ∀ g, ρ g ≤ σ g) (i : Fin n)
    (hkept : p.prior m (γ i) (A i) * ENNReal.ofReal ((H ^ 2 * (2 : ℝ) ^ T)⁻¹) ≤
      ρ (γ i) (A i ×ˢ Split.I T (j i))) :
    PieceFacts p m σ ρ r H B F T (γ i) (j i) (A i) (C i) (u i) (v i) (J i) (P i) := by
  have hHpos : 0 < H := by linarith
  have hε : p.N m ^ (Real.log H / Real.log (p.N m)) = H := rpow_log_div_log hN hHpos
  obtain ⟨_, _, _, _, hsub, hpiece, _⟩ := hCD
  obtain ⟨_, hJpos, _, hJle, huv, hdeg, _, hA, _, _, hfit, hfloor⟩ := hpiece i
  refine ⟨hN, hH, hB, hr, hsub i, ?_, hJpos, ?_, hJ i, ?_, hdeg, ?_, ?_, ?_, hρσ (γ i), hkept⟩
  · have h := hfloor rfl
    rw [hF]
    calc ENNReal.ofReal (p.N m ^ (-p.profile r) * J i / (H * 2 ^ T))
        = ENNReal.ofReal (p.N m ^ (-p.profile r) * J i /
            (p.N m ^ (Real.log H / Real.log (p.N m)) * 2 ^ T)) := by rw [hε]
      _ ≤ _ := h
  · calc J i ≤ p.N m ^ (Real.log H / Real.log (p.N m)) / 2 ^ T := hJle
      _ = H / 2 ^ T := by rw [hε]
  · calc |u i| + |v i| ≤ p.N m ^ (Real.log H / Real.log (p.N m)) := huv
      _ = H := hε
  · intro l hl e
    calc |l.2 e| ≤ p.N m ^ (Real.log H / Real.log (p.N m)) := (hA l hl).2 e
      _ = H := hε
  · intro l hl t ht
    obtain ⟨hy, hx⟩ := hfit l hl t ht
    refine ⟨?_, ?_⟩
    · calc |Split.y l t - u i - t * v i| ≤ p.N m ^ (Real.log H / Real.log (p.N m)) * J i := hy
        _ = H * J i := by rw [hε]
    · calc |Split.x l t - MvPolynomial.eval ![t, Split.y l t] (P i)|
          ≤ p.N m ^ (Real.log H / Real.log (p.N m)) * p.N m ^ (-r) := hx
        _ = H * p.N m ^ (-r) := by rw [hε]
  · rw [← pureObservation_eq_obsL]
    exact hceil (γ i)

/-- Original exponents in tangent units. -/
theorem tangent_exponents {N₀ sc dp s r F d B : ℝ} (hN₀ : 1 < N₀) (hsc : 0 < sc)
    (hr : r = sc * dp) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hprof : N₀ ^ |F - d * r| ≤ B) (hround : (N₀ ^ sc) ^ |dp - s| ≤ B) :
    (N₀ ^ sc) ^ (-d * s) ≤ B ^ 2 * N₀ ^ (-F) ∧
      N₀ ^ (-F) ≤ B ^ 2 * (N₀ ^ sc) ^ (-d * s) ∧
      N₀ ^ (-r) ≤ B * (N₀ ^ sc) ^ (-s) := by
  have hN₀pos : 0 < N₀ := by linarith
  set N := N₀ ^ sc with hN
  have hN1 : 1 ≤ N := Real.one_le_rpow hN₀.le hsc.le
  have hB0 : 0 ≤ B := le_trans (Real.rpow_nonneg hN₀pos.le _) hprof
  -- N^(-d dp) = N₀^(-(d r))
  have hscale : N ^ (-d * dp) = N₀ ^ (-(d * r)) := by
    rw [hN, ← Real.rpow_mul hN₀pos.le, hr]; ring_nf
  -- rounding comparisons
  have hr1 : N ^ (d * (-s)) ≤ B * N ^ (d * (-dp)) :=
    rpow_le_mul_of_abs_le hN1 (by rw [show (-s) - (-dp) = dp - s by ring]; exact hround)
      hd0 hd1
  have hr2 : N ^ (d * (-dp)) ≤ B * N ^ (d * (-s)) :=
    rpow_le_mul_of_abs_le hN1 (by
      rw [show (-dp) - (-s) = -(dp - s) by ring, abs_neg]; exact hround) hd0 hd1
  have hr3 : N ^ (1 * (-dp)) ≤ B * N ^ (1 * (-s)) :=
    rpow_le_mul_of_abs_le hN1 (by
      rw [show (-dp) - (-s) = -(dp - s) by ring, abs_neg]; exact hround) zero_le_one le_rfl
  -- profile comparisons
  have hp1 : N₀ ^ (1 * (-(d * r))) ≤ B * N₀ ^ (1 * (-F)) :=
    rpow_le_mul_of_abs_le hN₀.le (by
      rw [show (-(d * r)) - (-F) = F - d * r by ring]; exact hprof) zero_le_one le_rfl
  have hp2 : N₀ ^ (1 * (-F)) ≤ B * N₀ ^ (1 * (-(d * r))) :=
    rpow_le_mul_of_abs_le hN₀.le (by
      rw [show (-F) - (-(d * r)) = -(F - d * r) by ring, abs_neg]; exact hprof)
      zero_le_one le_rfl
  simp only [one_mul] at hr3 hp1 hp2
  have e1 : N ^ (d * (-s)) = N ^ (-d * s) := by ring_nf
  have e2 : N ^ (d * (-dp)) = N ^ (-d * dp) := by ring_nf
  rw [e1, e2] at hr1 hr2
  refine ⟨?_, ?_, ?_⟩
  · calc N ^ (-d * s) ≤ B * N ^ (-d * dp) := hr1
      _ = B * N₀ ^ (-(d * r)) := by rw [hscale]
      _ ≤ B * (B * N₀ ^ (-F)) := by gcongr
      _ = B ^ 2 * N₀ ^ (-F) := by ring
  · calc N₀ ^ (-F) ≤ B * N₀ ^ (-(d * r)) := hp2
      _ = B * N ^ (-d * dp) := by rw [hscale]
      _ ≤ B * (B * N ^ (-d * s)) := by gcongr
      _ = B ^ 2 * N ^ (-d * s) := by ring
  · calc N₀ ^ (-r) = N ^ (-dp) := by rw [hN, ← Real.rpow_mul hN₀pos.le, hr]; ring_nf
      _ ≤ B * N ^ (-s) := hr3

/-- The block-length comparison in tangent units. -/
theorem tangent_time {N B κ dp s T : ℝ} (hN : 1 ≤ N) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hround : N ^ |dp - s| ≤ B) (hT1 : N ^ (κ * dp) / B ≤ T) (hT2 : T ≤ B * N ^ (κ * dp))
    (hB : 1 ≤ B) {K : ℝ} (hK : B ^ 2 ≤ K) :
    N ^ (κ * s) / K ≤ T ∧ T ≤ K * N ^ (κ * s) := by
  have hBpos : 0 < B := by linarith
  have h1 : N ^ (κ * s) ≤ B * N ^ (κ * dp) :=
    rpow_le_mul_of_abs_le hN (by rw [abs_sub_comm]; exact hround) hκ0 hκ1
  have h2 : N ^ (κ * dp) ≤ B * N ^ (κ * s) := rpow_le_mul_of_abs_le hN hround hκ0 hκ1
  have hNs : 0 ≤ N ^ (κ * s) := Real.rpow_nonneg (by linarith) _
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK
  constructor
  · calc N ^ (κ * s) / K ≤ B * N ^ (κ * dp) / K := by gcongr
      _ ≤ B * N ^ (κ * dp) / B ^ 2 := by
          gcongr
      _ = N ^ (κ * dp) / B := by field_simp
      _ ≤ T := hT1
  · calc T ≤ B * N ^ (κ * dp) := hT2
      _ ≤ B * (B * N ^ (κ * s)) := by gcongr
      _ = B ^ 2 * N ^ (κ * s) := by ring
      _ ≤ K * N ^ (κ * s) := by gcongr

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
