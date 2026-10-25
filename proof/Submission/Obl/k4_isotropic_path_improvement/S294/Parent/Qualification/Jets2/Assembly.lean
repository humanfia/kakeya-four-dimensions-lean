-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Assembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Assembly.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Assembly.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Assembly.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Core
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Restrict
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.PowFacts

set_option autoImplicit false

/-!
# The higher jets from the first jet, version 2

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `38917d30`,
`Jets/Assembly.lean`, for rows in `(ℝ²)^*` (the version-2 statements of `Jets2/FirstJet.lean` and
`Jets2/Interface.lean`; `Qmin` has `10⁷`, see `Jets2/Schedule.lean`).

`higher_jets_of_first_jet : FirstJetStatement → HigherJetsStatement`.

All exponents are fixed before `ε`: for degree `M` put `D = M - 1`, `s = ⌈1/(1-d)⌉`,
`top = 10 s (D+1) + 3 s + 1`, the pair levels `T (ω k + 3)` (`k = 1, …, D`) and the fine level
`T λ₀`, `λ₀ = 32 s (ω 0 + 1)`, where `ω = omegaE D s top`.  The first jet is applied to these
levels (exponents `c_h (ω k + 3)` and `c_h λ₀`), giving its floor exponent `cζ`; the floor
exponent of the higher jets is `c_ζ = λ₀ + 2 cζ / c_h`.

For `ε > 0` put `Q = N^{ε₃}` with `ε₃ = min (ε / (G + 3)) (c_h / (20 s (E + 1)))` (`G`, `E` the
exponents of the schedule), apply the first jet with loss `ε₁ = ε₃ / (2^D + 2)` and constant
`K^{λ₀}`, and feed its output to `jets_core` with `ℓ = h^{1/(10 s)}`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set

noncomputable section

/-- The reciprocal-gap exponent. -/
def sOf (d : ℝ) : ℕ := ⌈1 / (1 - d)⌉₊

/-- The top scalar-width exponent. -/
def topOf (D s : ℕ) : ℕ := 10 * s * (D + 1) + 3 * s + 1

/-- The pair level multipliers. -/
def levOf (D s : ℕ) (k : ℕ) : ℕ := omegaE D s (topOf D s) k + 3

/-- The fine level multiplier. -/
def lam0Of (D s : ℕ) : ℕ := 32 * s * (omegaE D s (topOf D s) 0 + 1)

theorem sOf_spec {d : ℝ} (hd1 : d < 1) : 1 ≤ sOf d ∧ d ≤ 1 - 1 / (sOf d : ℝ) := by
  have h1d : 0 < 1 - d := by linarith
  have hc : 1 / (1 - d) ≤ (sOf d : ℝ) := Nat.le_ceil _
  have hpos : 0 < 1 / (1 - d) := by positivity
  have hs0 : (0 : ℝ) < sOf d := lt_of_lt_of_le hpos hc
  refine ⟨?_, ?_⟩
  · have : 0 < sOf d := by exact_mod_cast hs0
    omega
  · have : 1 / (sOf d : ℝ) ≤ 1 - d := by
      rw [div_le_iff₀ hs0]
      rw [div_le_iff₀ h1d] at hc
      linarith
    linarith

theorem levOf_le_lam0 (D s k : ℕ) (hs : 1 ≤ s) : levOf D s k ≤ lam0Of D s := by
  unfold levOf lam0Of
  have h := omegaE_anti D s (topOf D s) (Nat.zero_le k)
  have : 3 * (omegaE D s (topOf D s) 0 + 1) ≤ 32 * s * (omegaE D s (topOf D s) 0 + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem one_le_lam0 (D s : ℕ) (hs : 1 ≤ s) : 1 ≤ lam0Of D s := by
  unfold lam0Of
  have : 1 ≤ 32 * s := by omega
  have : 1 ≤ omegaE D s (topOf D s) 0 + 1 := by omega
  nlinarith

/-- The size of `Q` needed by the assembly. -/
def Qbig (D : ℕ) : ℝ := max (Qmin D) (2 * 4 ^ (2 ^ D + 2))

theorem Qmin_ge_coeff (D : ℕ) : ((D : ℝ) + 2) * 2 ^ (D + 1) ≤ Qmin D := by
  unfold Qmin
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ (D : ℝ) + 2 := by linarith
  have h2 : (2 : ℝ) ^ (D + 1) ≤ 2 ^ (D + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (0 : ℝ) ≤ 2 ^ (D + 1) := by positivity
  calc ((D : ℝ) + 2) * 2 ^ (D + 1) ≤ ((D : ℝ) + 2) ^ 2 * 2 ^ (D + 2) := by
        gcongr
        nlinarith
    _ ≤ 10 ^ 7 * ((D : ℝ) + 2) ^ 2 * 2 ^ (D + 2) := by
        have : (0 : ℝ) ≤ ((D : ℝ) + 2) ^ 2 * 2 ^ (D + 2) := by positivity
        nlinarith

/-- **Assembly after the first jet.** -/
theorem assemble_from_first_jet {Λ : Type} [MeasurableSpace Λ] {ν : Measure Λ}
    {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ}
    {K ζ d c_h ε N ε₃ : ℝ} {M T D s : ℕ}
    (hSN : ScalarNormal ν c E F piece K ζ d) (hd0 : 0 ≤ d) (hDM : D + 1 = M) (hD1 : 1 ≤ D)
    (hs1 : 1 ≤ s) (hds : d ≤ 1 - 1 / (s : ℝ)) (hch : 0 < c_h) (hε : 0 < ε) (hN1 : 1 ≤ N)
    (hε₃0 : 0 < ε₃) (hε₃ε : ε₃ ≤ ε / (gExp D D + 3))
    (hε₃c : ε₃ ≤ c_h / (20 * s * (bigE D + 1)))
    (hQbig : Qbig D ≤ N ^ ε₃) (hKQ : K ≤ N ^ ε₃) (hhN : ((2 : ℝ) ^ T)⁻¹ ≤ N ^ (-(c_h / 2)))
    (hζq : ζ ≤ ((2 : ℝ) ^ (T * lam0Of D s))⁻¹)
    {E₁ : Set (Λ × ℝ)} (hE₁sub : E₁ ⊆ E) (hE₁m : MeasurableSet E₁)
    (hE₁mass : ENNReal.ofReal (N ^ (-(ε₃ / (2 ^ D + 2)))) ≤ (ν.prod volume) E₁)
    {A : ℝ → Fin 2 → ℝ} (hAbd : ∀ p ∈ E₁, ‖A p.2‖ ≤ N ^ (ε₃ / (2 ^ D + 2)))
    (hTay : ∀ k, 1 ≤ k → k ≤ D → ∀ j : ℤ, ∀ p ∈ E₁, ∀ p' ∈ E₁, p.2 ∈ dI (T * levOf D s k) j →
      p'.2 ∈ dI (T * levOf D s k) j → ‖F p'.2 - F p.2 - (p'.2 - p.2) • A p.2‖ ≤
        N ^ (ε₃ / (2 ^ D + 2)) * (((2 : ℝ) ^ (T * levOf D s k))⁻¹) ^ ((11 : ℝ) / 10))
    (hLists : ∀ t, Determined E₁ (fun l => zS F (c l) t) univ t ((2 : ℝ) ^ (T * lam0Of D s))⁻¹
      (fun l => jet (leafRows F A t) (c l) t 1)
      (N ^ (ε₃ / (2 ^ D + 2)) * (((2 : ℝ) ^ (T * lam0Of D s))⁻¹) ^ ((1 - d) / 32))
      ⌊N ^ (ε₃ / (2 ^ D + 2))⌋₊) :
    ∃ p ∈ E, ∃ P : Fin 2 → Polynomial ℝ, JetFit E F M T (N ^ ε)
      (((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8))
      (((2 : ℝ) ^ T)⁻¹ * N ^ (-ε)) p P := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hQ1 : 1 ≤ N ^ ε₃ := one_le_rpow_of_nonneg hN1 hε₃0.le
  have hQ0 : 0 < N ^ ε₃ := lt_of_lt_of_le one_pos hQ1
  have hε₁ε₃ : ε₃ / (2 ^ D + 2) ≤ ε₃ :=
    div_le_self hε₃0.le (by have : (0 : ℝ) ≤ 2 ^ D := by positivity
                            linarith)
  have hNε₁Q : N ^ (ε₃ / (2 ^ D + 2)) ≤ N ^ ε₃ := rpow_le_rpow_of_le_exp hN1 hε₁ε₃
  have hh0 : (0 : ℝ) < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hh1 : ((2 : ℝ) ^ T)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h10s : (10 * s : ℕ) ≠ 0 := by omega
  -- the schedule
  set ell : ℝ := ((2 : ℝ) ^ T)⁻¹ ^ (((10 * s : ℕ) : ℝ)⁻¹) with hell
  have hell0 : 0 < ell := Real.rpow_pos_of_pos hh0 _
  have hell1 : ell ≤ 1 := Real.rpow_le_one hh0.le hh1 (by positivity)
  have hℓ : ell ^ (10 * s) = ((2 : ℝ) ^ T)⁻¹ := Real.rpow_inv_natCast_pow hh0.le h10s
  have hellQ : ell * (N ^ ε₃) ^ bigE D ≤ 1 :=
    ell_mul_Q_pow_le hN1 hh0 hhN hch hs1 hε₃0.le hε₃c
  have hEb1 : 1 ≤ bigE D := by unfold bigE; omega
  have hellQ1 : ell * N ^ ε₃ ≤ 1 := by
    calc ell * N ^ ε₃ = ell * (N ^ ε₃) ^ 1 := by rw [pow_one]
      _ ≤ ell * (N ^ ε₃) ^ bigE D := by gcongr
      _ ≤ 1 := hellQ
  have hq₁ell : ((2 : ℝ) ^ (T * lam0Of D s))⁻¹ = ell ^ (10 * s * lam0Of D s) := by
    rw [two_pow_mul_inv, ← hℓ, ← pow_mul]
  have hω0 : omegaE D s (topOf D s) 0 ≤ 10 * s * lam0Of D s := by
    unfold lam0Of
    have : 1 * (omegaE D s (topOf D s) 0 + 1) ≤ 320 * s * s * (omegaE D s (topOf D s) 0 + 1) :=
      Nat.mul_le_mul_right _ (by nlinarith)
    have e : 10 * s * (32 * s * (omegaE D s (topOf D s) 0 + 1)) =
        320 * s * s * (omegaE D s (topOf D s) 0 + 1) := by ring
    rw [e]; omega
  let S : Sched := ⟨N ^ ε₃, ell, ((2 : ℝ) ^ (T * lam0Of D s))⁻¹,
    N ^ (ε₃ / (2 ^ D + 2)) * (((2 : ℝ) ^ (T * lam0Of D s))⁻¹) ^ ((1 - d) / 32),
    (N ^ (-(ε₃ / (2 ^ D + 2))) / 4) ^ (2 ^ D + 2) / 2, D, s, topOf D s,
    ⌊N ^ (ε₃ / (2 ^ D + 2))⌋₊⟩
  have hOk : S.Ok ζ := by
    refine ⟨hD1, hs1, by show 1 ≤ topOf D s; unfold topOf; omega, le_trans (le_max_left _ _) hQbig, hell0, hell1,
      hellQ, hζq, ?_, by positivity, ?_, ?_, ?_, by positivity, ?_, ?_⟩
    · show ((2 : ℝ) ^ (T * lam0Of D s))⁻¹ ≤ ell ^ omegaE D s (topOf D s) 0
      rw [hq₁ell]
      exact pow_le_pow_of_le_one hell0.le hell1 hω0
    · exact fine_precision_le hell0 hell1 hellQ1 hNε₁Q hN0 hs1 hds rfl hq₁ell
    · exact Nat.le_floor (by push_cast; exact one_le_rpow_of_nonneg hN1 (by positivity))
    · exact (Nat.floor_le (by positivity)).trans hNε₁Q
    · show (N ^ (-(ε₃ / (2 ^ D + 2))) / 4) ^ (2 ^ D + 2) / 2 ≤ 1
      have h1 : N ^ (-(ε₃ / (2 ^ D + 2))) ≤ 1 := rpow_le_one_of_nonpos hN1 (by
        have : 0 ≤ ε₃ / (2 ^ D + 2) := by positivity
        linarith)
      have h2 : N ^ (-(ε₃ / (2 ^ D + 2))) / 4 ≤ 1 := by
        have : 0 ≤ N ^ (-(ε₃ / (2 ^ D + 2))) := by positivity
        linarith
      have h3 : (N ^ (-(ε₃ / (2 ^ D + 2))) / 4) ^ (2 ^ D + 2) ≤ 1 :=
        pow_le_one₀ (by positivity) h2
      linarith
    · exact one_le_Q_sq_mstar hN0 (le_trans (le_max_right _ _) hQbig)
  have hdense : ENNReal.ofReal (N ^ ε₃)⁻¹ ≤ (ν.prod volume) E₁ := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hE₁mass
    rw [← Real.rpow_neg hN0.le]
    exact rpow_le_rpow_of_le_exp hN1 (by linarith)
  have hSN₁ : ScalarNormal ν c E₁ F piece (N ^ ε₃) ζ d := hSN.restrict hE₁sub hE₁m hKQ hdense
  have hA' : ∀ p ∈ E₁, ‖A p.2‖ ≤ S.Q := fun p hp => (hAbd p hp).trans hNε₁Q
  have htaylor' : ∀ k, 1 ≤ k → k ≤ S.D → ∀ j : ℤ, ∀ p ∈ E₁, ∀ p' ∈ E₁,
      p.2 ∈ dI (T * (S.ω k + 3)) j → p'.2 ∈ dI (T * (S.ω k + 3)) j →
      ‖F p'.2 - F p.2 - (p'.2 - p.2) • A p.2‖ ≤ S.eT k := by
    intro k hk1 hkD j p hp p' hp' h1 h2
    refine (hTay k hk1 hkD j p hp p' hp' h1 h2).trans ?_
    exact taylor_err_le hell0 hell1 hs1 hℓ hNε₁Q hQ0.le
  have hθ : S.ell ^ (10 * S.s * (S.D + 1) + 2 * S.s) ≤ ((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8) := by
    show ell ^ (10 * s * (D + 1) + 2 * s) ≤ ((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8)
    rw [hDM]
    exact theta_ge hell0 hell1 hs1 hℓ
  have hτ : N ^ (-ε) * S.Q ^ 3 ≤ 1 := duration_allow_le hN1 hε₃0.le hε₃ε hε
  obtain ⟨p, hp, P, hdeg, hcoef, hfit, hvol⟩ := jets_core hOk hSN₁ hd0 hds hℓ
    (le_of_eq rfl) hA' htaylor' hLists
    (by positivity) hE₁mass rfl hθ (by positivity) hτ
  have hC : (((S.D + 1 : ℕ) : ℝ) + 1) * (S.BR S.D * 2 ^ (S.D + 1)) ≤ N ^ ε :=
    coeff_allow_le hN1 hε₃0.le ((Qmin_ge_coeff D).trans (le_trans (le_max_left _ _) hQbig))
      (hOk.levels S.D le_rfl).2.2.2.1 hε₃ε hε
  refine ⟨p, hE₁sub hp, P, ?_, fun i k => (hcoef i k).trans hC, hfit, hvol.trans (measure_mono ?_)⟩
  · rw [← hDM]; exact hdeg
  · rintro v ⟨h1, h2, h3⟩
    exact ⟨h1, hE₁sub h2, h3⟩

/-- **The higher jets from the first jet.** -/
theorem higher_jets_of_first_jet (hFJ : FirstJetStatement) : HigherJetsStatement := by
  intro d hd0 hd1 M hM c_h hch
  obtain ⟨hs1, hds⟩ := sOf_spec hd1
  set D := M - 1 with hD
  set s := sOf d with hs
  have hD1 : 1 ≤ D := by omega
  have hDM : D + 1 = M := by omega
  set top := topOf D s with htop
  set lev := levOf D s with hlev
  set lam0 := lam0Of D s with hlam0
  have hlam1 : 1 ≤ lam0 := one_le_lam0 D s hs1
  have hlam0r : (0 : ℝ) < lam0 := by exact_mod_cast hlam1
  set γ : Fin D → ℝ := fun i => c_h * (lev (i + 1) : ℝ) with hγ
  have hγpos : ∀ i, 0 < γ i := fun i => by simp only [hγ, hlev, levOf]; positivity
  have hγle : ∀ i, γ i ≤ c_h * lam0 := fun i => by
    simp only [hγ]
    gcongr
    exact_mod_cast levOf_le_lam0 D s _ hs1
  obtain ⟨cζ, hcζ, hFJε⟩ := hFJ d hd0 hd1 D γ (c_h * lam0) hγpos hγle (by positivity)
  refine ⟨lam0 + 2 * cζ / c_h, by positivity, ?_⟩
  intro ε hε
  set G := gExp D D with hG
  set Eb := bigE D with hEb
  set ε₃ := min (ε / (G + 3)) (c_h / (20 * s * (Eb + 1))) with hε₃
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hε₃0 : 0 < ε₃ := lt_min (by positivity) (by positivity)
  set ε₁ := ε₃ / (2 ^ D + 2) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨αF, hαF, N₀F, hN₀F⟩ := hFJε ε₁ hε₁0
  set α := min (min ε₃ (c_h / 2)) (αF / lam0) with hα
  have hα0 : 0 < α := lt_min (lt_min hε₃0 (by positivity)) (by positivity)
  refine ⟨α, hα0, max (max N₀F 1) (Qbig D ^ (1 / ε₃)), ?_⟩
  intro N hN Λ _ ν c E F piece K ζ T hKα hhlo hhhi hζ hSN
  -- basic facts
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hNF : N₀F ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNQ : Qbig D ^ (1 / ε₃) ≤ N := le_trans (le_max_right _ _) hN
  have hK1 : 1 ≤ K := hSN.one_le_K
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hαε₃ : α ≤ ε₃ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hαch : α ≤ c_h / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hαF : α ≤ αF / lam0 := min_le_right _ _
  have hε₃ε : ε₃ ≤ ε / (G + 3) := min_le_left _ _
  have hε₃c : ε₃ ≤ c_h / (20 * s * (Eb + 1)) := min_le_right _ _
  have hε₁ε₃ : ε₁ ≤ ε₃ := by
    rw [hε₁, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ D + 2 := by have : (0 : ℝ) ≤ 2 ^ D := by positivity
                                     linarith
    nlinarith
  set h : ℝ := ((2 : ℝ) ^ T)⁻¹ with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  set Q := N ^ ε₃ with hQdef
  have hQbig : Qbig D ≤ Q := by
    have hQb0 : 0 ≤ Qbig D := le_trans (by unfold Qmin; positivity) (le_max_left _ _)
    calc Qbig D = (Qbig D ^ (1 / ε₃)) ^ ε₃ := by
          rw [← Real.rpow_mul hQb0, one_div, inv_mul_cancel₀ hε₃0.ne', Real.rpow_one]
      _ ≤ N ^ ε₃ := Real.rpow_le_rpow (by positivity) hNQ hε₃0.le
  have hQmin : Qmin D ≤ Q := le_trans (le_max_left _ _) hQbig
  have hQ4 : 2 * 4 ^ (2 ^ D + 2) ≤ Q := le_trans (le_max_right _ _) hQbig
  have hQ1 : 1 ≤ Q := one_le_rpow_of_nonneg hN1 hε₃0.le
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ1
  have hKQ : K ≤ Q := hKα.trans (rpow_le_rpow_of_le_exp hN1 hαε₃)
  have hNε₁Q : N ^ ε₁ ≤ Q := rpow_le_rpow_of_le_exp hN1 hε₁ε₃
  -- `h` is a negative power of `N`
  have hhN : h ≤ N ^ (-(c_h / 2)) := by
    calc h ≤ K * N ^ (-c_h) := hhhi
      _ ≤ N ^ α * N ^ (-c_h) := by gcongr
      _ = N ^ (α + -c_h) := rpow_add_of_one_le hN1 _ _
      _ ≤ N ^ (-(c_h / 2)) := rpow_le_rpow_of_le_exp hN1 (by linarith)
  -- the constant of the first jet
  set K' := K ^ lam0 with hK'
  have hKK' : K ≤ K' := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ lam0 := pow_le_pow_right₀ hK1 hlam1
  have hK'α : K' ≤ N ^ αF := by
    calc K' = K ^ lam0 := rfl
      _ ≤ (N ^ α) ^ lam0 := pow_le_pow_left₀ hK0.le hKα _
      _ = N ^ (α * lam0) := rpow_pow_eq hN0.le α lam0
      _ ≤ N ^ αF := rpow_le_rpow_of_le_exp hN1 (by
            rw [le_div_iff₀ hlam0r] at hαF; linarith)
  have hζFJ : ζ ≤ N ^ (-cζ) := by
    calc ζ ≤ h ^ ((lam0 : ℝ) + 2 * cζ / c_h) := hζ
      _ ≤ (N ^ (-(c_h / 2))) ^ ((lam0 : ℝ) + 2 * cζ / c_h) :=
          Real.rpow_le_rpow hh0.le hhN (by positivity)
      _ = N ^ (-(c_h / 2) * ((lam0 : ℝ) + 2 * cζ / c_h)) := (Real.rpow_mul hN0.le _ _).symm
      _ ≤ N ^ (-cζ) := rpow_le_rpow_of_le_exp hN1 (by
            have e : -(c_h / 2) * ((lam0 : ℝ) + 2 * cζ / c_h) = -(c_h * lam0 / 2) - cζ := by
              field_simp; ring
            rw [e]
            have : 0 ≤ c_h * lam0 / 2 := by positivity
            linarith)
  have hlevels : ∀ i : Fin D, N ^ (-γ i) / K' ≤ ((2 : ℝ) ^ (T * lev ((i : ℕ) + 1)))⁻¹ ∧
      ((2 : ℝ) ^ (T * lev ((i : ℕ) + 1)))⁻¹ ≤ K' * N ^ (-γ i) := by
    intro i
    have hb := pow_bounds (h := h) (a := N ^ (-c_h)) (K := K) (by positivity) hK1 hhlo hhhi
      (levOf_le_lam0 D s ((i : ℕ) + 1) hs1)
    rw [two_pow_mul_inv]
    have e : N ^ (-γ i) = (N ^ (-c_h)) ^ (lev ((i : ℕ) + 1)) := by
      rw [rpow_pow_eq hN0.le]; congr 1; simp only [hγ]; ring
    rw [e]
    exact hb
  have hT₀ := pow_bounds (h := h) (a := N ^ (-c_h)) (K := K) (by positivity) hK1 hhlo hhhi
    (le_refl lam0)
  have eT₀ : N ^ (-(c_h * lam0)) = (N ^ (-c_h)) ^ lam0 := by
    rw [rpow_pow_eq hN0.le]; congr 1; ring
  have hT₀lo : N ^ (-(c_h * lam0)) / K' ≤ ((2 : ℝ) ^ (T * lam0))⁻¹ := by
    rw [two_pow_mul_inv, eT₀]; exact hT₀.1
  have hT₀hi : ((2 : ℝ) ^ (T * lam0))⁻¹ ≤ K' * N ^ (-(c_h * lam0)) := by
    rw [two_pow_mul_inv, eT₀]; exact hT₀.2
  have hdense' : ENNReal.ofReal K'⁻¹ ≤ (ν.prod volume) E :=
    le_trans (ENNReal.ofReal_le_ofReal (inv_anti₀ hK0 hKK')) hSN.dense
  -- the first jet
  obtain ⟨E₁, hE₁sub, hE₁m, hE₁mass, A, -, hAbd, hTay, hLists⟩ :=
    hN₀F N hNF Λ ν c E F piece K' ζ (fun i => T * lev ((i : ℕ) + 1)) (T * lam0) hK'α hζFJ
      hlevels hT₀lo hT₀hi (fun i => Nat.mul_le_mul_left T (levOf_le_lam0 D s ((i : ℕ) + 1) hs1))
      (hSN.restrict subset_rfl hSN.measurableSet_E hKK' hdense')
  have hTay' : ∀ k, 1 ≤ k → k ≤ D → ∀ j : ℤ, ∀ p ∈ E₁, ∀ p' ∈ E₁,
      p.2 ∈ dI (T * levOf D s k) j → p'.2 ∈ dI (T * levOf D s k) j →
      ‖F p'.2 - F p.2 - (p'.2 - p.2) • A p.2‖ ≤
        N ^ (ε₃ / (2 ^ D + 2)) * (((2 : ℝ) ^ (T * levOf D s k))⁻¹) ^ ((11 : ℝ) / 10) := by
    intro k hk1 hkD j p hp p' hp' h1 h2
    have e : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    have h1' : p.2 ∈ dI (T * lev (k - 1 + 1)) j := by rw [e]; exact h1
    have h2' : p'.2 ∈ dI (T * lev (k - 1 + 1)) j := by rw [e]; exact h2
    have := hTay ⟨k - 1, by omega⟩ j p hp p' hp' h1' h2'
    simp only [e] at this
    exact this
  have hζq : ζ ≤ ((2 : ℝ) ^ (T * lam0))⁻¹ := by
    calc ζ ≤ h ^ ((lam0 : ℝ) + 2 * cζ / c_h) := hζ
      _ ≤ h ^ (lam0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hh0 hh1 (by
          have : 0 ≤ 2 * cζ / c_h := by positivity
          linarith)
      _ = ((2 : ℝ) ^ (T * lam0))⁻¹ := by rw [Real.rpow_natCast, two_pow_mul_inv]
  exact assemble_from_first_jet hSN hd0 hDM hD1 hs1 hds hch hε hN1 hε₃0 hε₃ε hε₃c hQbig hKQ hhN
    hζq hE₁sub hE₁m hE₁mass hAbd hTay' hLists

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
