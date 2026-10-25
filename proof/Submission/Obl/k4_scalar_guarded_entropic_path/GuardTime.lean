/- Adapted from same-tree o168/x0569-o196port, commit c22aeb8a. -/
/-
Adapted from: here:o168 (session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/GuardTime.lean), renamed into the o196
namespace. Its own provenance comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Guard

/-!
# Layer block counts from the guard

A true layer at original depth `sc * dp` is in particular a false-flag chart at the time
exponent `log 2^T / log N₀` given by its own block count, with any larger complexity budget
and slack. If the stage guard forbids false charts with time at most
`sc * (κ * dp - buffer)`, the layer therefore has `2^T > N^{κ dp - buffer}` blocks.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

/-- Semialgebraic formats are monotone in their bounds. -/
theorem Format.mono' {n : ℕ} {B B' : ℝ} {D D' : ℕ} {A : Set (Fin n → ℝ)}
    (h : Split.Format n B D A) (hB : B ≤ B') (hD : D ≤ D') : Split.Format n B' D' A := by
  obtain ⟨k, hk, P, hP, S, hS⟩ := h
  exact ⟨k, hk.trans hB, P, fun j => ⟨(hP j).1.trans hD, fun b => ((hP j).2 b).trans hB⟩,
    S, hS⟩

/-- Chart data with any truth flag are false-flag chart data with a larger budget and
slack and any time exponent dominating the block count. -/
theorem ChartData.to_false {p : Code} {B B' : ℕ} {r b h h' ε ε' : ℝ} {truth : Bool}
    {k T n : ℕ} {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Coeff} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ} {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hN : 1 ≤ p.N k) (hBB : B ≤ B') (hε : ε ≤ ε') (hT : (2 : ℝ) ^ T ≤ p.N k ^ h')
    (hc : Split.ChartData p B r b h ε truth k T n γ j A C u v J P Λ) :
    Split.ChartData p B' r b h' ε' false k T n γ j A C u v J P Λ := by
  obtain ⟨_, hn, hmeas, hdisj, hsubset, hcharts, hcard, hmlist, hknown, hmass⟩ := hc
  have hεpow : p.N k ^ ε ≤ p.N k ^ ε' := Real.rpow_le_rpow_of_exponent_le hN hε
  have hBpow : p.N k ^ (B : ℝ) ≤ p.N k ^ (B' : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by exact_mod_cast hBB)
  have hNpos : 0 < p.N k := lt_of_lt_of_le zero_lt_one hN
  refine ⟨hT, hn.trans hBpow, hmeas, hdisj, hsubset, ?_, ?_, hmlist, hknown, ?_⟩
  · intro i
    obtain ⟨hmpos, hJpos, hJinv, hJub, huv, hdeg, hcoeff, hcoord,
      hFA, hFC, happrox, _⟩ := hcharts i
    refine ⟨hmpos, hJpos, hJinv.trans hBpow,
      hJub.trans (div_le_div_of_nonneg_right hεpow (by positivity)),
      huv.trans hεpow, hdeg, fun a => (hcoeff a).trans hBpow, ?_,
      fun z => Format.mono' (hFA z) hBpow hBB, fun z => Format.mono' (hFC z) hBpow hBB, ?_, ?_⟩
    · intro l hl
      exact ⟨(hcoord l hl).1.trans hBpow, fun e => ((hcoord l hl).2 e).trans hεpow⟩
    · intro l hl t ht
      obtain ⟨hy, hx⟩ := happrox l hl t ht
      exact ⟨hy.trans (mul_le_mul_of_nonneg_right hεpow hJpos.le),
        hx.trans (mul_le_mul_of_nonneg_right hεpow (Real.rpow_nonneg hNpos.le _))⟩
    · intro hfalse
      cases hfalse
  · intro a z
    exact (hcard a z).trans hεpow
  · exact (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hε))).trans hmass

/-- **Block counts from the guard.** -/
theorem blocks_of_guard {p : Code} {m B : ℕ} {sc dp tm H κ R buffer loss : ℝ} {M : ℕ}
    {f : Layer (p.1 m)} (hN : 1 < p.N m) (hsc : 0 < sc)
    (hCD : Split.ChartData p M (sc * dp) p.L (sc * tm) (Real.log H / Real.log (p.N m)) true m
      f.T f.n f.world f.block f.assignment f.witness f.u f.v f.width f.graph f.list)
    (hMB : M ≤ B) (hloss : Real.log H / Real.log (p.N m) ≤ loss)
    (hdp1 : R⁻¹ ≤ dp) (hdp2 : dp ≤ R)
    (hguard : ∀ r h : ℝ, R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - buffer →
      ¬Split.Chart p B (sc * r) p.L (sc * h) loss false m) :
    (p.N m ^ sc) ^ (κ * dp - buffer) < (2 : ℝ) ^ f.T := by
  have hNpos : 0 < p.N m := by linarith
  have hlogN : 0 < Real.log (p.N m) := Real.log_pos hN
  set h₀ : ℝ := Real.log ((2 : ℝ) ^ f.T) / (sc * Real.log (p.N m)) with hh₀
  have hT : (2 : ℝ) ^ f.T ≤ p.N m ^ (sc * h₀) := by
    have : sc * h₀ = Real.log ((2 : ℝ) ^ f.T) / Real.log (p.N m) := by
      rw [hh₀]; field_simp
    rw [this, Real.rpow_def_of_pos hNpos, mul_div_cancel₀ _ hlogN.ne',
      Real.exp_log (by positivity)]
  by_contra hle
  rw [not_lt] at hle
  -- the block count gives a time exponent below the guard
  have hh₀le : h₀ ≤ κ * dp - buffer := by
    have h1 : Real.log ((2 : ℝ) ^ f.T) ≤ Real.log ((p.N m ^ sc) ^ (κ * dp - buffer)) :=
      Real.log_le_log (by positivity) hle
    rw [← Real.rpow_mul hNpos.le, Real.log_rpow hNpos] at h1
    rw [hh₀, div_le_iff₀ (by positivity)]
    nlinarith
  exact hguard dp h₀ hdp1 hdp2 hh₀le
    ⟨f.T, f.n, f.world, f.block, f.assignment, f.witness, f.u, f.v, f.width, f.graph, f.list,
      ChartData.to_false hN.le hMB hloss hT hCD⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers

/-- **Two-sided block counts of a guarded true layer.** The upper bound comes from the
layer's own time exponent `sc * tm`, the lower bound from the guard. -/
theorem layer_time_bounds {p : Code} {m B : ℕ} {sc dp tm H κ R buffer loss β Bs : ℝ} {M : ℕ}
    {f : Layer (p.1 m)} (hN : 1 < p.N m) (hsc : 0 < sc)
    (hCD : Split.ChartData p M (sc * dp) p.L (sc * tm) (Real.log H / Real.log (p.N m)) true m
      f.T f.n f.world f.block f.assignment f.witness f.u f.v f.width f.graph f.list)
    (hMB : M ≤ B) (hloss : Real.log H / Real.log (p.N m) ≤ loss)
    (hdp1 : R⁻¹ ≤ dp) (hdp2 : dp ≤ R)
    (hguard : ∀ r h : ℝ, R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - buffer →
      ¬Split.Chart p B (sc * r) p.L (sc * h) loss false m)
    (htm : tm ≤ κ * dp + β) (hβ : (p.N m ^ sc) ^ β ≤ Bs)
    (hbf : (p.N m ^ sc) ^ buffer ≤ Bs) (hbf0 : 0 ≤ buffer) :
    (p.N m ^ sc) ^ (κ * dp) / Bs ≤ (2 : ℝ) ^ f.T ∧
      (2 : ℝ) ^ f.T ≤ Bs * (p.N m ^ sc) ^ (κ * dp) := by
  have hNpos : 0 < p.N m := by linarith
  have hN1 : 1 ≤ p.N m ^ sc := Real.one_le_rpow hN.le hsc.le
  have hNsc : 0 < p.N m ^ sc := by linarith
  have hBs : 0 < Bs := lt_of_lt_of_le (Real.rpow_pos_of_pos hNsc _) hbf
  have hlow := blocks_of_guard hN hsc hCD hMB hloss hdp1 hdp2 hguard
  constructor
  · rw [div_le_iff₀ hBs]
    calc (p.N m ^ sc) ^ (κ * dp) = (p.N m ^ sc) ^ (κ * dp - buffer) *
          (p.N m ^ sc) ^ buffer := by rw [← Real.rpow_add hNsc]; ring_nf
      _ ≤ (2 : ℝ) ^ f.T * Bs := by
          gcongr
  · calc (2 : ℝ) ^ f.T ≤ p.N m ^ (sc * tm) := hCD.1
      _ = (p.N m ^ sc) ^ tm := by rw [← Real.rpow_mul hNpos.le]
      _ ≤ (p.N m ^ sc) ^ (κ * dp + β) := Real.rpow_le_rpow_of_exponent_le hN1 htm
      _ = (p.N m ^ sc) ^ β * (p.N m ^ sc) ^ (κ * dp) := by
          rw [← Real.rpow_add hNsc]; ring_nf
      _ ≤ Bs * (p.N m ^ sc) ^ (κ * dp) := by gcongr

end Submission.Obl.k4_scalar_guarded_entropic_path
