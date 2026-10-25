-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Schedule, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Schedule.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Schedule.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Schedule.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Budget

set_option autoImplicit false

/-!
# The scale and loss schedule of the jet tree, version 2

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `38917d30`,
`Jets/Schedule.lean`, with the constants of the version-2 budget (`Jets2/Budget.lean`,
`Jets2/Tree.lean`): `Qmin` has `10⁷` in place of `10⁶`, the loss unit is `9600 Q³/Kpop`, the
Lipschitz constants are `CJ k = 3 + 2 (k+4) BR k`, and the pair numbers carry the version-2
factors (`120000 K⁷`, `16000 K⁶ (1 + 2 M K)`, `4000 K⁶`, `errS = H² (K + 2 BR K) + 4 K eT`).
The exponents of x0801's schedule are unchanged.

All scales are natural powers of one small real `ℓ`, all large constants are bounded by natural
powers of one large real `Q` (which also serves as the constant of the scalar-normal world).
For a tree of depth `D`:

* scalar widths `W k = ℓ^{ω k}`, with `ω D = top` and `ω k = 10 s (ω (k+1) + 3) + ω (k+1) + 1`;
* pair scales `H k = ℓ^{10 s (ω k + 3)}` (so `W k = H (k+1) W (k+1) ℓ`);
* Taylor errors `eT k = Q H k ℓ^{ω k + 3}`;
* gap constant `Kg = Q³`, popularity constant `Kpop = Q⁶`;
* list sizes `n k`, row bounds `BR k`, Lipschitz constants `CJ k = 3 + 2 (k+4) BR k`, thresholds
  `Lam`, `δc`, defined recursively by the closed forms of `Budget.lean`.

`Sched.treeBudget`: under `ℓ Q^{bigE D} ≤ 1` (and `Q ≥ Qmin D`, a mass `mstar ≥ Q⁻²`), these
sequences form a `TreeBudget`; every level-`k` quantity is at most `Q^{gExp D k}`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open PairData

noncomputable section

/-- Scalar-width exponents. -/
def omegaE (D s top : ℕ) (k : ℕ) : ℕ :=
  if D ≤ k then top else 10 * s * (omegaE D s top (k + 1) + 3) + omegaE D s top (k + 1) + 1
termination_by D - k

theorem omegaE_of_le {D s top k : ℕ} (hk : D ≤ k) : omegaE D s top k = top := by
  rw [omegaE]; simp [hk]

theorem omegaE_of_lt {D s top k : ℕ} (hk : k < D) :
    omegaE D s top k = 10 * s * (omegaE D s top (k + 1) + 3) + omegaE D s top (k + 1) + 1 := by
  rw [omegaE]; simp [show ¬ D ≤ k by omega]

theorem omegaE_succ_le (D s top k : ℕ) : omegaE D s top (k + 1) ≤ omegaE D s top k := by
  by_cases hk : D ≤ k
  · rw [omegaE_of_le hk, omegaE_of_le (by omega)]
  · rw [omegaE_of_lt (show k < D by omega)]; omega

theorem omegaE_anti (D s top : ℕ) {k k' : ℕ} (h : k ≤ k') :
    omegaE D s top k' ≤ omegaE D s top k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (omegaE_succ_le D s top _).trans ih

theorem top_le_omegaE (D s top k : ℕ) : top ≤ omegaE D s top k := by
  have h1 := omegaE_anti D s top (le_max_left k D)
  rw [omegaE_of_le (le_max_right k D)] at h1
  exact h1

/-- Exponent bounds of the level-`k` quantities. -/
def gExp (D : ℕ) : ℕ → ℕ
  | 0 => 10
  | k + 1 => 4 * (D + 2) * (gExp D k + 12)

theorem gExp_le_succ (D k : ℕ) : gExp D k ≤ gExp D (k + 1) := by
  show gExp D k ≤ 4 * (D + 2) * (gExp D k + 12)
  calc gExp D k ≤ 1 * (gExp D k + 12) := by omega
    _ ≤ 4 * (D + 2) * (gExp D k + 12) := Nat.mul_le_mul_right _ (by omega)

theorem gExp_mono (D : ℕ) {k k' : ℕ} (h : k ≤ k') : gExp D k ≤ gExp D k' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (gExp_le_succ D _)

theorem ten_le_gExp (D k : ℕ) : 10 ≤ gExp D k :=
  (show 10 ≤ gExp D 0 from le_rfl).trans (gExp_mono D (Nat.zero_le k))

/-- `gExp (k+1)` dominates every exponent produced from level `k`. -/
theorem gExp_succ_ge (D k : ℕ) :
    gExp D k + 2 + D * (3 * gExp D k + 11) ≤ gExp D (k + 1) ∧
      D * (4 * gExp D k + 11) ≤ gExp D (k + 1) ∧ 3 * gExp D k + 9 ≤ gExp D (k + 1) := by
  show _ ≤ 4 * (D + 2) * (gExp D k + 12) ∧ _ ≤ 4 * (D + 2) * (gExp D k + 12) ∧
    _ ≤ 4 * (D + 2) * (gExp D k + 12)
  set g := gExp D k
  have e : 4 * (D + 2) * (g + 12) = 4 * D * g + 48 * D + 8 * g + 96 := by ring
  rw [e]
  have h1 : D * (3 * g + 11) = 3 * (D * g) + 11 * D := by ring
  have h2 : D * (4 * g + 11) = 4 * (D * g) + 11 * D := by ring
  have h3 : 4 * D * g = 4 * (D * g) := by ring
  rw [h1, h2, h3]
  omega

/-- The single smallness exponent. -/
def bigE (D : ℕ) : ℕ := (D + 3) * gExp D D + 20

/-- The size of `Q` absorbing all numerical constants. -/
def Qmin (D : ℕ) : ℝ := 10 ^ 7 * ((D : ℝ) + 2) ^ 2 * 2 ^ (D + 2)

/-- The inputs of the schedule. -/
structure Sched where
  Q : ℝ
  ell : ℝ
  q₁ : ℝ
  p₁ : ℝ
  mstar : ℝ
  D : ℕ
  s : ℕ
  top : ℕ
  n₁ : ℕ

namespace Sched

variable (S : Sched)

def ω (k : ℕ) : ℕ := omegaE S.D S.s S.top k
def W (k : ℕ) : ℝ := S.ell ^ S.ω k
def H (k : ℕ) : ℝ := S.ell ^ (10 * S.s * (S.ω k + 3))
def eT (k : ℕ) : ℝ := S.Q * S.H k * S.ell ^ (S.ω k + 3)
def Kg : ℝ := S.Q ^ 3
def Kpop : ℝ := S.Q ^ 6
def loss (k : ℕ) : ℝ := (k + 1) * 2 ^ (k + 1) * (9600 * S.Q ^ 3 / S.Kpop)
def mass (k : ℕ) : ℝ := S.mstar * (k + 1) / (S.D + 1)
def mD (k : ℕ) : ℝ := S.mass (k + 1) - 2 * S.loss k
def CJof (k : ℕ) (B : ℝ) : ℝ := 3 + 2 * (k + 4) * B

/-- The list sizes and row bounds, recursively. -/
def nb : ℕ → ℕ × ℝ
  | 0 => (⌊3 * S.Q * ((S.n₁ * (⌊2 * S.p₁ / (CJof 0 S.Q * S.W 0)⌋₊ + 2) : ℕ) : ℝ) * S.Kpop⌋₊,
      S.Q)
  | k + 1 =>
    (⌊3 * S.Q * ((4 * pairNG S.Q (nb k).2 (S.H (k + 1)) (S.eT (k + 1)) (S.W k)
        (CJof k (nb k).2 * S.W k) (nb k).1 : ℕ) : ℝ) * S.Kpop⌋₊,
      max (nb k).2 (pairLam S.Q (nb k).2 (S.mD k) S.D
        (pairNG S.Q (nb k).2 (S.H (k + 1)) (S.eT (k + 1)) (S.W k) (CJof k (nb k).2 * S.W k)
          (nb k).1) (k + 1)))

def n (k : ℕ) : ℕ := (S.nb k).1
def BR (k : ℕ) : ℝ := (S.nb k).2
def CJ (k : ℕ) : ℝ := CJof k (S.BR k)
def w (k : ℕ) : ℝ := S.CJ k * S.W k
def nG (k : ℕ) : ℕ := pairNG S.Q (S.BR k) (S.H (k + 1)) (S.eT (k + 1)) (S.W k) (S.w k) (S.n k)

def Lam : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | k + 1 => pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k)

def δc : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | k + 1 => pairDc S.Q S.Kg (S.H (k + 1)) (S.eT (k + 1)) (S.w k) (S.BR k) (S.mD k) S.D (S.n k)
      (S.nG k)

theorem n_succ (k : ℕ) : S.n (k + 1) = ⌊3 * S.Q * ((4 * S.nG k : ℕ) : ℝ) * S.Kpop⌋₊ := rfl

theorem BR_succ (k : ℕ) : S.BR (k + 1) = max (S.BR k) (S.Lam (k + 1) (k + 1)) := rfl

theorem n_zero : S.n 0 =
    ⌊3 * S.Q * ((S.n₁ * (⌊2 * S.p₁ / S.w 0⌋₊ + 2) : ℕ) : ℝ) * S.Kpop⌋₊ := rfl

theorem BR_zero : S.BR 0 = S.Q := rfl

/-- The hypotheses of the schedule. -/
structure Ok (ζ : ℝ) : Prop where
  hD : 1 ≤ S.D
  hs : 1 ≤ S.s
  htop : 1 ≤ S.top
  hQ : Qmin S.D ≤ S.Q
  hell0 : 0 < S.ell
  hell1 : S.ell ≤ 1
  hellQ : S.ell * S.Q ^ bigE S.D ≤ 1
  hζq : ζ ≤ S.q₁
  hqW : S.q₁ ≤ S.W 0
  hp0 : 0 ≤ S.p₁
  hpW : S.p₁ ≤ S.W 0
  hn₁ : 1 ≤ S.n₁
  hn₁Q : (S.n₁ : ℝ) ≤ S.Q
  hm0 : 0 < S.mstar
  hm1 : S.mstar ≤ 1
  hmQ : 1 ≤ S.Q ^ 2 * S.mstar

variable {S} {ζ : ℝ}

/-! ### Basic facts about `Q` and `ℓ` -/

theorem Ok.Qmin_ge (hS : S.Ok ζ) : 10 ^ 7 * ((S.D : ℝ) + 2) ^ 2 * 2 ^ (S.D + 2) ≤ S.Q := hS.hQ

theorem Ok.one_le_two_pow (D : ℕ) : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)

/-- `Q` dominates `c (D+2)² 2^(D+2)` for `c ≤ 10⁷`. -/
theorem Ok.const_le (hS : S.Ok ζ) {c : ℝ} (hc : c ≤ 10 ^ 7) (_hc0 : 0 ≤ c) :
    c * ((S.D : ℝ) + 2) ^ 2 * 2 ^ (S.D + 2) ≤ S.Q := by
  refine le_trans ?_ hS.hQ
  unfold Qmin
  have : 0 ≤ ((S.D : ℝ) + 2) ^ 2 * 2 ^ (S.D + 2) := by positivity
  nlinarith

theorem Ok.big (hS : S.Ok ζ) : 10 ^ 7 ≤ S.Q := by
  have h := hS.const_le (c := 10 ^ 7) le_rfl (by norm_num)
  have h1 : (1 : ℝ) ≤ ((S.D : ℝ) + 2) ^ 2 := one_le_pow₀ (by linarith [(Nat.cast_nonneg S.D : (0:ℝ) ≤ S.D)])
  have h2 : (1 : ℝ) ≤ 2 ^ (S.D + 2) := one_le_pow₀ (by norm_num)
  have : (10 : ℝ) ^ 7 ≤ 10 ^ 7 * ((S.D : ℝ) + 2) ^ 2 * 2 ^ (S.D + 2) := by
    have := mul_le_mul h1 h2 zero_le_one (by positivity)
    nlinarith
  linarith

theorem Ok.one_le_Q (hS : S.Ok ζ) : 1 ≤ S.Q := le_trans (by norm_num) hS.big

theorem Ok.Q_pos (hS : S.Ok ζ) : 0 < S.Q := lt_of_lt_of_le one_pos hS.one_le_Q

theorem Ok.D_le (hS : S.Ok ζ) {c : ℝ} (hc : c ≤ 10 ^ 7) (hc0 : 0 ≤ c) :
    c * ((S.D : ℝ) + 2) ≤ S.Q := by
  refine le_trans ?_ (hS.const_le hc hc0)
  have hD2 : (1 : ℝ) ≤ (S.D : ℝ) + 2 := by linarith [(Nat.cast_nonneg S.D : (0:ℝ) ≤ S.D)]
  have h2 : (1 : ℝ) ≤ 2 ^ (S.D + 2) := one_le_pow₀ (by norm_num)
  have : c * ((S.D : ℝ) + 2) ≤ c * ((S.D : ℝ) + 2) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hc0
    nlinarith
  calc c * ((S.D : ℝ) + 2) ≤ c * ((S.D : ℝ) + 2) ^ 2 := this
    _ = c * ((S.D : ℝ) + 2) ^ 2 * 1 := by ring
    _ ≤ c * ((S.D : ℝ) + 2) ^ 2 * 2 ^ (S.D + 2) := by gcongr

theorem Ok.pow_le_pow (hS : S.Ok ζ) {a b : ℕ} (h : a ≤ b) : S.Q ^ a ≤ S.Q ^ b :=
  pow_le_pow_right₀ hS.one_le_Q h

theorem Ok.one_le_pow (hS : S.Ok ζ) (a : ℕ) : 1 ≤ S.Q ^ a := one_le_pow₀ hS.one_le_Q

/-- `ℓ Q^e ≤ 1` for every `e ≤ bigE D`. -/
theorem Ok.ellQ (hS : S.Ok ζ) {e : ℕ} (he : e ≤ bigE S.D) : S.ell * S.Q ^ e ≤ 1 :=
  le_trans (mul_le_mul_of_nonneg_left (hS.pow_le_pow he) hS.hell0.le) hS.hellQ

theorem Ok.ell_pow_le (hS : S.Ok ζ) {a b : ℕ} (h : a ≤ b) : S.ell ^ b ≤ S.ell ^ a :=
  pow_le_pow_of_le_one hS.hell0.le hS.hell1 h

/-! ### Scales -/

theorem Ok.W_pos (hS : S.Ok ζ) (k : ℕ) : 0 < S.W k := pow_pos hS.hell0 _

theorem Ok.H_pos (hS : S.Ok ζ) (k : ℕ) : 0 < S.H k := pow_pos hS.hell0 _

theorem Ok.W_le_one (hS : S.Ok ζ) (k : ℕ) : S.W k ≤ 1 := pow_le_one₀ hS.hell0.le hS.hell1

theorem Ok.W_mono (hS : S.Ok ζ) {k k' : ℕ} (h : k ≤ k') : S.W k ≤ S.W k' :=
  hS.ell_pow_le (omegaE_anti _ _ _ h)

theorem Ok.W_le_ell (hS : S.Ok ζ) (k : ℕ) : S.W k ≤ S.ell := by
  have : 1 ≤ S.ω k := le_trans hS.htop (top_le_omegaE _ _ _ k)
  calc S.W k ≤ S.ell ^ 1 := hS.ell_pow_le this
    _ = S.ell := pow_one _

theorem Ok.W_succ (_hS : S.Ok ζ) {k : ℕ} (hk : k < S.D) :
    S.W k = S.H (k + 1) * S.W (k + 1) * S.ell := by
  have e := omegaE_of_lt (s := S.s) (top := S.top) hk
  simp only [W, H, ω]
  rw [e, ← pow_add, ← pow_succ]

theorem Ok.H_le (hS : S.Ok ζ) (k : ℕ) : S.H k ≤ S.W k * S.ell ^ 30 := by
  simp only [H, W]
  rw [← pow_add]
  apply hS.ell_pow_le
  have := hS.hs
  have : 1 * (S.ω k + 3) ≤ S.s * (S.ω k + 3) := Nat.mul_le_mul_right _ this
  nlinarith

theorem Ok.H_le_one (hS : S.Ok ζ) (k : ℕ) : S.H k ≤ 1 := pow_le_one₀ hS.hell0.le hS.hell1

theorem eT_eq (k : ℕ) : S.eT k = S.Q * S.H k * S.W k * S.ell ^ 3 := by
  simp only [eT, W, pow_add]; ring

theorem Ok.eT_nonneg (hS : S.Ok ζ) (k : ℕ) : 0 ≤ S.eT k := by
  rw [eT_eq]; have := hS.Q_pos; have := hS.H_pos k; have := hS.W_pos k; have := hS.hell0
  positivity

/-! ### Mass and loss -/

theorem Ok.Kpop_pos (hS : S.Ok ζ) : 0 < S.Kpop := pow_pos hS.Q_pos 6

theorem Ok.loss_nonneg (hS : S.Ok ζ) (k : ℕ) : 0 ≤ S.loss k := by
  simp only [loss]; have := hS.Kpop_pos; have := hS.Q_pos; positivity

theorem Ok.loss_le (hS : S.Ok ζ) {k : ℕ} (hk : k ≤ S.D) :
    S.loss k ≤ S.mstar / (2 * (S.D + 1)) := by
  have hQ := hS.Q_pos
  have hD1 : (0 : ℝ) < S.D + 1 := by positivity
  simp only [loss, Kpop]
  have hkD : ((k : ℝ) + 1) * 2 ^ (k + 1) ≤ ((S.D : ℝ) + 1) * 2 ^ (S.D + 1) := by
    have : (k : ℝ) ≤ S.D := by exact_mod_cast hk
    have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (S.D + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    gcongr
  have hc := hS.const_le (c := 2 * 9600) (by norm_num) (by norm_num)
  have e1 : 9600 * S.Q ^ 3 / S.Q ^ 6 = 9600 / S.Q ^ 3 := by
    field_simp
  have e2 : ((k : ℝ) + 1) * 2 ^ (k + 1) * (9600 / S.Q ^ 3) =
      ((k : ℝ) + 1) * 2 ^ (k + 1) * 9600 / S.Q ^ 3 := by ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  -- (k+1) 2^(k+1) 9600 * (2 (D+1)) ≤ mstar Q^3
  have hm := hS.hmQ
  have h2 : ((S.D : ℝ) + 1) * 2 ^ (S.D + 1) * 9600 * (2 * ((S.D : ℝ) + 1)) ≤
      2 * 9600 * ((S.D : ℝ) + 2) ^ 2 * 2 ^ (S.D + 2) := by
    have h3 : ((S.D : ℝ) + 1) * ((S.D : ℝ) + 1) ≤ ((S.D : ℝ) + 2) ^ 2 := by nlinarith
    have h4 : (2 : ℝ) ^ (S.D + 1) ≤ 2 ^ (S.D + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : ((S.D : ℝ) + 1) * 2 ^ (S.D + 1) * 9600 * (2 * ((S.D : ℝ) + 1)) =
        2 * 9600 * (((S.D : ℝ) + 1) * ((S.D : ℝ) + 1)) * 2 ^ (S.D + 1) := by ring
    rw [e]; gcongr
  calc ((k : ℝ) + 1) * 2 ^ (k + 1) * 9600 * (2 * ((S.D : ℝ) + 1))
      ≤ ((S.D : ℝ) + 1) * 2 ^ (S.D + 1) * 9600 * (2 * ((S.D : ℝ) + 1)) := by gcongr
    _ ≤ S.Q := h2.trans hc
    _ = S.Q * 1 := (mul_one _).symm
    _ ≤ S.Q * (S.Q ^ 2 * S.mstar) := by gcongr
    _ = S.mstar * S.Q ^ 3 := by ring

theorem Ok.mass_le_one (hS : S.Ok ζ) {k : ℕ} (hk : k ≤ S.D) : S.mass k ≤ 1 := by
  simp only [mass]
  have hD1 : (0 : ℝ) < S.D + 1 := by positivity
  rw [div_le_one hD1]
  have hk' : (k : ℝ) ≤ S.D := by exact_mod_cast hk
  have : (k : ℝ) + 1 ≤ S.D + 1 := by linarith
  calc S.mstar * ((k : ℝ) + 1) ≤ 1 * ((S.D : ℝ) + 1) :=
        mul_le_mul hS.hm1 this (by positivity) zero_le_one
    _ = S.D + 1 := one_mul _

theorem Ok.mD_ge (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) :
    S.mstar / (S.D + 1) ≤ S.mD k := by
  have hl := hS.loss_le (show k ≤ S.D by omega)
  have hD1 : (0 : ℝ) < S.D + 1 := by positivity
  simp only [mD, mass]
  have e : S.mstar * (((k + 1 : ℕ) : ℝ) + 1) / (S.D + 1) =
      S.mstar / (S.D + 1) + S.mstar * ((k : ℝ) + 1) / (S.D + 1) := by
    push_cast; field_simp; ring
  rw [e]
  have : 2 * S.loss k ≤ S.mstar / (S.D + 1) := by
    calc 2 * S.loss k ≤ 2 * (S.mstar / (2 * (S.D + 1))) := by linarith
      _ = S.mstar / (S.D + 1) := by field_simp
  have : S.mstar / (S.D + 1) ≤ S.mstar * ((k : ℝ) + 1) / (S.D + 1) := by
    apply div_le_div_of_nonneg_right _ hD1.le
    have := hS.hm0
    nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  linarith

theorem Ok.mD_pos (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) : 0 < S.mD k :=
  lt_of_lt_of_le (by have := hS.hm0; positivity) (hS.mD_ge hk)

theorem Ok.mD_le_one (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) : S.mD k ≤ 1 := by
  have := hS.loss_nonneg k
  have := hS.mass_le_one hk
  simp only [mD]; linarith

theorem Ok.one_le_Q3mD (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) : 1 ≤ S.Q ^ 3 * S.mD k := by
  have h := hS.mD_ge hk
  have hD1 : (0 : ℝ) < S.D + 1 := by positivity
  have hDQ : (S.D : ℝ) + 1 ≤ S.Q := by
    have := hS.D_le (c := 1) (by norm_num) (by norm_num); linarith
  have hQ := hS.Q_pos
  calc (1 : ℝ) ≤ S.Q * (S.Q ^ 2 * S.mstar) / (S.D + 1) := by
        rw [le_div_iff₀ hD1]
        calc 1 * ((S.D : ℝ) + 1) ≤ S.Q * 1 := by linarith
          _ ≤ S.Q * (S.Q ^ 2 * S.mstar) := by gcongr; exact hS.hmQ
    _ = S.Q ^ 3 * (S.mstar / (S.D + 1)) := by ring
    _ ≤ S.Q ^ 3 * S.mD k := by gcongr


/-! ### The level bounds -/

/-- The bounds at level `k`: every quantity is at most `Q^{gExp D k}`. -/
def LevelOK (S : Sched) (k : ℕ) : Prop :=
  1 ≤ S.n k ∧ (S.n k : ℝ) ≤ S.Q ^ gExp S.D k ∧ 1 ≤ S.BR k ∧ S.BR k ≤ S.Q ^ gExp S.D k ∧
    S.CJ k ≤ S.Q ^ gExp S.D k

theorem Ok.exp_le_bigE (hS : S.Ok ζ) {k : ℕ} (hk : k ≤ S.D) :
    4 * gExp S.D k + 20 ≤ bigE S.D := by
  have := gExp_mono S.D hk
  unfold bigE
  have : 4 * gExp S.D S.D ≤ (S.D + 3) * gExp S.D S.D :=
    Nat.mul_le_mul_right _ (by have := hS.hD; omega)
  omega

theorem Ok.ellQ_le (hS : S.Ok ζ) {e : ℕ} (he : e ≤ bigE S.D) {c : ℝ} (hc : c ≤ S.Q ^ e) :
    S.ell * c ≤ 1 :=
  le_trans (mul_le_mul_of_nonneg_left hc hS.hell0.le) (hS.ellQ he)

theorem Ok.ell30 (hS : S.Ok ζ) : S.ell ^ 30 ≤ S.ell := by
  simpa using hS.ell_pow_le (show 1 ≤ 30 by norm_num)

theorem Ok.CJ_nonneg {k : ℕ} (hL : LevelOK S k) : 0 ≤ S.CJ k := by
  obtain ⟨-, -, hB1, -, -⟩ := hL
  simp only [CJ, CJof]; positivity

theorem Ok.ratio (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    S.W k + S.H (k + 1) * S.w k + errS S.Q (S.BR k) (S.H (k + 1)) (S.eT (k + 1)) ≤
      4 * S.W k := by
  have hCJ0 := Ok.CJ_nonneg hL
  obtain ⟨-, -, hB1, hBg, hCJg⟩ := hL
  set g := gExp S.D k
  have hg : 4 * g + 20 ≤ bigE S.D := hS.exp_le_bigE (by omega)
  have hQ1 := hS.one_le_Q
  have hQ0 := hS.Q_pos
  have hbig := hS.big
  have hl0 := hS.hell0
  have hl1 := hS.hell1
  have hW := hS.W_succ (show k < S.D by omega)
  have hWk0 := hS.W_pos k
  have hW'0 : 0 < S.W (k + 1) := hS.W_pos _
  have hW'1 : S.W (k + 1) ≤ 1 := hS.W_le_one _
  have hH0 : 0 < S.H (k + 1) := hS.H_pos _
  have hHle : S.H (k + 1) ≤ S.W (k + 1) * S.ell ^ 30 := hS.H_le _
  have hl30 := hS.ell30
  have hHl : S.H (k + 1) ≤ S.ell := by
    calc S.H (k + 1) ≤ S.W (k + 1) * S.ell ^ 30 := hHle
      _ ≤ 1 * S.ell := by gcongr
      _ = S.ell := one_mul _
  -- the term `H w`
  have hHCJ : S.H (k + 1) * S.CJ k ≤ 1 := by
    calc S.H (k + 1) * S.CJ k ≤ S.ell * S.Q ^ g := mul_le_mul hHl hCJg hCJ0 hl0.le
      _ ≤ 1 := hS.ellQ (by omega)
  have t2 : S.H (k + 1) * S.w k ≤ S.W k := by
    have hw : S.w k = S.CJ k * S.W k := rfl
    calc S.H (k + 1) * S.w k = (S.H (k + 1) * S.CJ k) * S.W k := by rw [hw]; ring
      _ ≤ 1 * S.W k := by gcongr
      _ = S.W k := one_mul _
  -- the term `H² (K + 2 BR K)`
  have t3a : S.H (k + 1) ^ 2 * (S.Q + 2 * S.BR k * S.Q) ≤ S.W k := by
    have hQg : 1 ≤ S.Q ^ g := hS.one_le_pow g
    have h1 : S.Q + 2 * S.BR k * S.Q ≤ S.Q ^ (g + 2) := by
      calc S.Q + 2 * S.BR k * S.Q ≤ S.Q ^ g * S.Q + 2 * S.Q ^ g * S.Q := by
            gcongr
            calc S.Q = 1 * S.Q := (one_mul _).symm
              _ ≤ S.Q ^ g * S.Q := by gcongr
        _ = 3 * S.Q ^ (g + 1) := by ring
        _ ≤ S.Q * S.Q ^ (g + 1) := by gcongr; linarith
        _ = S.Q ^ (g + 2) := by ring
    have hl28 : S.ell ^ 28 ≤ 1 := pow_le_one₀ hl0.le hl1
    have hlQ : S.ell * S.Q ^ (g + 2) ≤ 1 := hS.ellQ (by omega)
    have h2 : S.H (k + 1) * (S.Q + 2 * S.BR k * S.Q) ≤ S.W (k + 1) * S.ell := by
      calc S.H (k + 1) * (S.Q + 2 * S.BR k * S.Q)
          ≤ (S.W (k + 1) * S.ell ^ 30) * S.Q ^ (g + 2) := by gcongr
        _ = (S.W (k + 1) * S.ell) * (S.ell ^ 28 * (S.ell * S.Q ^ (g + 2))) := by ring
        _ ≤ (S.W (k + 1) * S.ell) * (1 * 1) := by gcongr
        _ = S.W (k + 1) * S.ell := by ring
    calc S.H (k + 1) ^ 2 * (S.Q + 2 * S.BR k * S.Q)
        = S.H (k + 1) * (S.H (k + 1) * (S.Q + 2 * S.BR k * S.Q)) := by ring
      _ ≤ S.H (k + 1) * (S.W (k + 1) * S.ell) := by gcongr
      _ = S.W k := by rw [hW]; ring
  -- the term `eT (4 K)`
  have t3b : S.eT (k + 1) * (4 * S.Q) ≤ S.W k := by
    rw [eT_eq, hW]
    have h1 : S.ell * (4 * S.Q ^ 2) ≤ 1 := by
      calc S.ell * (4 * S.Q ^ 2) ≤ S.ell * S.Q ^ 3 := by
            gcongr
            calc 4 * S.Q ^ 2 ≤ S.Q * S.Q ^ 2 := by gcongr; linarith
              _ = S.Q ^ 3 := by ring
        _ ≤ 1 := hS.ellQ (by omega)
    calc S.Q * S.H (k + 1) * S.W (k + 1) * S.ell ^ 3 * (4 * S.Q)
        = (S.H (k + 1) * S.W (k + 1) * S.ell) * (S.ell * (S.ell * (4 * S.Q ^ 2))) := by ring
      _ ≤ (S.H (k + 1) * S.W (k + 1) * S.ell) * (1 * 1) := by gcongr
      _ = S.H (k + 1) * S.W (k + 1) * S.ell := by ring
  unfold errS
  linarith

theorem Ok.nG_le (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    S.nG k ≤ 10 * S.n k ^ 3 := by
  have hr := hS.ratio hk hL
  have hW0 := hS.W_pos k
  have hfl : ⌊2 * (S.W k + S.H (k + 1) * S.w k + errS S.Q (S.BR k) (S.H (k + 1)) (S.eT (k + 1))) /
      S.W k⌋₊ ≤ 8 := by
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hW0]; push_cast; linarith
  simp only [nG, pairNG, nGrad]
  calc S.n k * ((1 * S.n k) * (⌊2 * (S.W k + S.H (k + 1) * S.w k +
          errS S.Q (S.BR k) (S.H (k + 1)) (S.eT (k + 1))) / S.W k⌋₊ + 2)) * S.n k
      ≤ S.n k * ((1 * S.n k) * (8 + 2)) * S.n k := by gcongr
    _ = 10 * S.n k ^ 3 := by ring

theorem Ok.nG_le_real (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    (S.nG k : ℝ) ≤ 10 * S.Q ^ (3 * gExp S.D k) := by
  have h := hS.nG_le hk hL
  have hn := hL.2.1
  have h' : (S.nG k : ℝ) ≤ 10 * (S.n k : ℝ) ^ 3 := by exact_mod_cast h
  calc (S.nG k : ℝ) ≤ 10 * (S.n k : ℝ) ^ 3 := h'
    _ ≤ 10 * (S.Q ^ gExp S.D k) ^ 3 := by gcongr
    _ = 10 * S.Q ^ (3 * gExp S.D k) := by ring

theorem Ok.one_le_nG {k : ℕ} (hL : LevelOK S k) : 1 ≤ S.nG k :=
  le_trans hL.1 (le_nGrad hL.1)

theorem Ok.X_le (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    pairX S.Q (S.mD k) S.D (S.nG k) ≤ S.Q ^ (3 * gExp S.D k + 11) := by
  set g := gExp S.D k
  have hnG := hS.nG_le_real hk hL
  have hmD := hS.mD_pos hk
  have hQ3 := hS.one_le_Q3mD hk
  have hQ0 := hS.Q_pos
  have hc := hS.D_le (c := 1200000) (by norm_num) (by norm_num)
  have hD : (S.D : ℝ) ≤ S.D + 2 := by linarith
  unfold pairX
  rw [div_le_iff₀ hmD]
  calc 120000 * (S.D : ℝ) * S.Q ^ 7 * (S.nG k : ℝ) ≤ 120000 * ((S.D : ℝ) + 2) * S.Q ^ 7 *
        (10 * S.Q ^ (3 * g)) := by gcongr
    _ = (1200000 * ((S.D : ℝ) + 2)) * S.Q ^ (3 * g + 7) := by ring
    _ ≤ S.Q * S.Q ^ (3 * g + 7) := by gcongr
    _ = S.Q ^ (3 * g + 8) * 1 := by ring
    _ ≤ S.Q ^ (3 * g + 8) * (S.Q ^ 3 * S.mD k) := by gcongr
    _ = S.Q ^ (3 * g + 11) * S.mD k := by ring

theorem Ok.one_le_X (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    1 ≤ pairX S.Q (S.mD k) S.D (S.nG k) := by
  have hmD := hS.mD_pos hk
  have hmD1 := hS.mD_le_one hk
  have hnG : (1 : ℝ) ≤ S.nG k := by exact_mod_cast Ok.one_le_nG hL
  have hD : (1 : ℝ) ≤ S.D := by exact_mod_cast hS.hD
  have hQ6 : 1 ≤ S.Q ^ 7 := hS.one_le_pow 7
  unfold pairX
  rw [le_div_iff₀ hmD]
  have h1 : (1 : ℝ) ≤ S.D * S.Q ^ 7 := one_le_mul_of_one_le_of_one_le hD hQ6
  have h2 : (1 : ℝ) ≤ S.D * S.Q ^ 7 * S.nG k := one_le_mul_of_one_le_of_one_le h1 hnG
  nlinarith

theorem Ok.Lam_le (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) {j : ℕ}
    (hj : j ≤ S.D) :
    pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) j ≤
      S.Q ^ (gExp S.D k + 1 + S.D * (3 * gExp S.D k + 11)) := by
  set g := gExp S.D k
  have hX := hS.X_le hk hL
  have hX1 := hS.one_le_X hk hL
  have hB := hL.2.2.2.1
  have hQ1 := hS.one_le_Q
  have hbig := hS.big
  unfold pairLam
  have hXj : pairX S.Q (S.mD k) S.D (S.nG k) ^ j ≤ S.Q ^ (S.D * (3 * g + 11)) := by
    calc pairX S.Q (S.mD k) S.D (S.nG k) ^ j ≤ (S.Q ^ (3 * g + 11)) ^ j := by gcongr
      _ = S.Q ^ ((3 * g + 11) * j) := by rw [← pow_mul]
      _ ≤ S.Q ^ (S.D * (3 * g + 11)) := hS.pow_le_pow (by rw [mul_comm]; exact Nat.mul_le_mul_right _ hj)
  have hB1 : S.BR k + 1 ≤ S.Q ^ (g + 1) := by
    have h1 : 1 ≤ S.Q ^ g := hS.one_le_pow g
    calc S.BR k + 1 ≤ S.Q ^ g + S.Q ^ g := by linarith
      _ = 2 * S.Q ^ g := by ring
      _ ≤ S.Q * S.Q ^ g := by gcongr; linarith
      _ = S.Q ^ (g + 1) := by ring
  calc (S.BR k + 1) * pairX S.Q (S.mD k) S.D (S.nG k) ^ j
      ≤ S.Q ^ (g + 1) * S.Q ^ (S.D * (3 * g + 11)) := by
        gcongr
    _ = S.Q ^ (g + 1 + S.D * (3 * g + 11)) := by rw [← pow_add]

theorem Ok.Z_le (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    pairZ S.Q (S.mD k) S.D (S.n k) (S.nG k) ≤ S.Q ^ (4 * gExp S.D k + 11) := by
  set g := gExp S.D k
  have hnG := hS.nG_le_real hk hL
  have hn := hL.2.1
  have hmD := hS.mD_pos hk
  have hQ3 := hS.one_le_Q3mD hk
  have hQ0 := hS.Q_pos
  have hQ1 := hS.one_le_Q
  have hc := hS.D_le (c := 320000) (by norm_num) (by norm_num)
  have hD : (S.D : ℝ) ≤ S.D + 2 := by linarith
  have hD0 : (0 : ℝ) ≤ S.D := Nat.cast_nonneg _
  unfold pairZ
  have h1 : 1 + 2 * (S.D : ℝ) * S.Q ≤ 2 * ((S.D : ℝ) + 2) * S.Q := by nlinarith
  have h2 : 16000 * S.Q ^ 6 * (S.n k : ℝ) * (S.nG k : ℝ) ≤ 160000 * S.Q ^ (4 * g + 6) := by
    calc 16000 * S.Q ^ 6 * (S.n k : ℝ) * (S.nG k : ℝ) ≤ 16000 * S.Q ^ 6 * S.Q ^ g *
          (10 * S.Q ^ (3 * g)) := by gcongr
      _ = 160000 * S.Q ^ (4 * g + 6) := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hmD]
  calc 16000 * S.Q ^ 6 * (S.n k : ℝ) * (S.nG k : ℝ) * (1 + 2 * (S.D : ℝ) * S.Q)
      ≤ 160000 * S.Q ^ (4 * g + 6) * (2 * ((S.D : ℝ) + 2) * S.Q) := by
        gcongr
    _ = (320000 * ((S.D : ℝ) + 2)) * S.Q ^ (4 * g + 7) := by ring
    _ ≤ S.Q * S.Q ^ (4 * g + 7) := by gcongr
    _ = S.Q ^ (4 * g + 8) * 1 := by ring
    _ ≤ S.Q ^ (4 * g + 8) * (S.Q ^ 3 * S.mD k) := by gcongr
    _ = S.Q ^ (4 * g + 11) * S.mD k := by ring

theorem Ok.one_le_Z (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    1 ≤ pairZ S.Q (S.mD k) S.D (S.n k) (S.nG k) := by
  have hmD := hS.mD_pos hk
  have hmD1 := hS.mD_le_one hk
  have hnG : (1 : ℝ) ≤ S.nG k := by exact_mod_cast Ok.one_le_nG hL
  have hn : (1 : ℝ) ≤ S.n k := by exact_mod_cast hL.1
  have hQ5 : 1 ≤ S.Q ^ 6 := hS.one_le_pow 6
  have hQ1 := hS.one_le_Q
  have hD0 : (0 : ℝ) ≤ S.D := Nat.cast_nonneg _
  unfold pairZ
  have h1 : (1 : ℝ) ≤ S.Q ^ 6 * S.n k * S.nG k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hQ5 hn) hnG
  have h2 : 1 ≤ 16000 * S.Q ^ 6 * (S.n k : ℝ) * S.nG k / S.mD k := by
    rw [le_div_iff₀ hmD]; nlinarith
  have h3 : (1 : ℝ) ≤ 1 + 2 * S.D * S.Q := by nlinarith
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ 16000 * S.Q ^ 6 * (S.n k : ℝ) * S.nG k / S.mD k * (1 + 2 * S.D * S.Q) :=
        mul_le_mul h2 h3 zero_le_one (by linarith)

theorem Ok.level_zero (hS : S.Ok ζ) : LevelOK S 0 := by
  have hQ1 := hS.one_le_Q
  have hbig := hS.big
  have hW0 := hS.W_pos 0
  have hw0 : S.w 0 = (3 + 8 * S.Q) * S.W 0 := by
    simp only [w, CJ, CJof, BR_zero]; push_cast; ring
  have hw0pos : 0 < S.w 0 := by rw [hw0]; positivity
  have hfl : ⌊2 * S.p₁ / S.w 0⌋₊ ≤ 2 := by
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hw0pos, hw0]
    push_cast
    have := hS.hpW
    nlinarith
  have hfl' : (⌊2 * S.p₁ / S.w 0⌋₊ : ℝ) ≤ 2 := by exact_mod_cast hfl
  have hn1 : (1 : ℝ) ≤ S.n₁ := by exact_mod_cast hS.hn₁
  have hKp : 1 ≤ S.Kpop := hS.one_le_pow 6
  have hg0 : gExp S.D 0 = 10 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [n_zero]
    apply Nat.le_floor
    push_cast
    have h2 : (2 : ℝ) ≤ (⌊2 * S.p₁ / S.w 0⌋₊ : ℝ) + 2 := by
      linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌊2 * S.p₁ / S.w 0⌋₊)]
    calc (1 : ℝ) ≤ 3 * 1 * (1 * 2) * 1 := by norm_num
      _ ≤ 3 * S.Q * (S.n₁ * ((⌊2 * S.p₁ / S.w 0⌋₊ : ℝ) + 2)) * S.Kpop := by gcongr
  · rw [n_zero, hg0]
    calc ((⌊3 * S.Q * ((S.n₁ * (⌊2 * S.p₁ / S.w 0⌋₊ + 2) : ℕ) : ℝ) * S.Kpop⌋₊ : ℕ) : ℝ)
        ≤ 3 * S.Q * ((S.n₁ * (⌊2 * S.p₁ / S.w 0⌋₊ + 2) : ℕ) : ℝ) * S.Kpop :=
          Nat.floor_le (by positivity)
      _ ≤ 3 * S.Q * (S.Q * (2 + 2)) * S.Q ^ 6 := by
          push_cast
          gcongr
          · exact hS.hn₁Q
          · exact le_of_eq rfl
      _ = 12 * S.Q ^ 8 := by ring
      _ ≤ S.Q * S.Q ^ 8 := by gcongr; linarith
      _ = S.Q ^ 9 := by ring
      _ ≤ S.Q ^ 10 := hS.pow_le_pow (by norm_num)
  · rw [BR_zero]; exact hQ1
  · rw [BR_zero, hg0]
    calc S.Q = S.Q ^ 1 := (pow_one _).symm
      _ ≤ S.Q ^ 10 := hS.pow_le_pow (by norm_num)
  · rw [hg0]
    simp only [CJ, CJof, BR_zero]
    push_cast
    calc 3 + 2 * (0 + 4) * S.Q ≤ S.Q * S.Q := by nlinarith
      _ = S.Q ^ 2 := by ring
      _ ≤ S.Q ^ 10 := hS.pow_le_pow (by norm_num)

theorem Ok.BR_succ_le (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    S.BR (k + 1) ≤ S.Q ^ (gExp S.D k + 1 + S.D * (3 * gExp S.D k + 11)) := by
  rw [BR_succ]
  refine max_le ?_ (hS.Lam_le hk hL hk)
  exact hL.2.2.2.1.trans (hS.pow_le_pow (by omega))

theorem Ok.level_succ (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    LevelOK S (k + 1) := by
  set g := gExp S.D k with hg
  obtain ⟨hge1, hge2, hge3⟩ := gExp_succ_ge S.D k
  have hnG := hS.nG_le_real hk hL
  have hnG1 : (1 : ℝ) ≤ S.nG k := by exact_mod_cast Ok.one_le_nG hL
  have hQ1 := hS.one_le_Q
  have hbig := hS.big
  have hKp : 1 ≤ S.Kpop := hS.one_le_pow 6
  have hBR := hS.BR_succ_le hk hL
  have hB1 : 1 ≤ S.BR (k + 1) := by rw [BR_succ]; exact le_trans hL.2.2.1 (le_max_left _ _)
  refine ⟨?_, ?_, hB1, hBR.trans (hS.pow_le_pow (by omega)), ?_⟩
  · rw [n_succ]
    apply Nat.le_floor
    push_cast
    calc (1 : ℝ) ≤ 3 * 1 * (4 * 1) * 1 := by norm_num
      _ ≤ 3 * S.Q * (4 * (S.nG k : ℝ)) * S.Kpop := by gcongr
  · rw [n_succ]
    calc ((⌊3 * S.Q * ((4 * S.nG k : ℕ) : ℝ) * S.Kpop⌋₊ : ℕ) : ℝ)
        ≤ 3 * S.Q * ((4 * S.nG k : ℕ) : ℝ) * S.Kpop := Nat.floor_le (by positivity)
      _ ≤ 3 * S.Q * (4 * (10 * S.Q ^ (3 * g))) * S.Q ^ 6 := by
          push_cast
          gcongr
          exact le_of_eq rfl
      _ = 120 * S.Q ^ (3 * g + 7) := by ring
      _ ≤ S.Q * S.Q ^ (3 * g + 7) := by gcongr; linarith
      _ = S.Q ^ (3 * g + 8) := by ring
      _ ≤ S.Q ^ gExp S.D (k + 1) := hS.pow_le_pow (by omega)
  · simp only [CJ, CJof]
    push_cast
    have hk8 : 2 * (k : ℝ) + 13 ≤ S.Q := by
      have h := hS.D_le (c := 13) (by norm_num) (by norm_num)
      have : (k : ℝ) + 1 ≤ S.D := by exact_mod_cast hk
      linarith
    calc 3 + 2 * ((k : ℝ) + 1 + 4) * S.BR (k + 1) ≤ (2 * (k : ℝ) + 13) * S.BR (k + 1) := by
          nlinarith
      _ ≤ S.Q * S.Q ^ (g + 1 + S.D * (3 * g + 11)) := by
          gcongr
      _ = S.Q ^ (g + 2 + S.D * (3 * g + 11)) := by ring
      _ ≤ S.Q ^ gExp S.D (k + 1) := hS.pow_le_pow hge1

theorem Ok.levels (hS : S.Ok ζ) : ∀ k, k ≤ S.D → LevelOK S k := by
  intro k
  induction k with
  | zero => intro _; exact hS.level_zero
  | succ k ih => intro hk; exact hS.level_succ hk (ih (by omega))

/-! ### The smallness conditions of one pair -/

theorem Ok.cond1 (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    4000 * S.Q ^ 6 * (S.n k : ℝ) * (S.nG k : ℝ) * S.W k ≤ S.mD k / 4 := by
  set g := gExp S.D k with hg
  have hE := hS.exp_le_bigE (show k ≤ S.D by omega)
  have hnG := hS.nG_le_real hk hL
  have hn := hL.2.1
  have hQ3 := hS.one_le_Q3mD hk
  have hbig := hS.big
  have hQ0 := hS.Q_pos
  have hWl := hS.W_le_ell k
  have hWk0 := (hS.W_pos k).le
  have hl0 := hS.hell0
  have h1 : 40000 * S.Q ^ (4 * g + 6) * S.ell * (4 * S.Q ^ 3) ≤
      (S.mD k / 4) * (4 * S.Q ^ 3) := by
    calc 40000 * S.Q ^ (4 * g + 6) * S.ell * (4 * S.Q ^ 3) =
          160000 * (S.ell * S.Q ^ (4 * g + 9)) := by ring
      _ ≤ S.Q * (S.ell * S.Q ^ (4 * g + 9)) := by gcongr; linarith
      _ = S.ell * S.Q ^ (4 * g + 10) := by ring
      _ ≤ 1 := hS.ellQ (by omega)
      _ ≤ S.Q ^ 3 * S.mD k := hQ3
      _ = (S.mD k / 4) * (4 * S.Q ^ 3) := by ring
  have h2 := le_of_mul_le_mul_right h1 (by positivity)
  calc 4000 * S.Q ^ 6 * (S.n k : ℝ) * (S.nG k : ℝ) * S.W k
      ≤ 4000 * S.Q ^ 6 * S.Q ^ g * (10 * S.Q ^ (3 * g)) * S.ell := by gcongr
    _ = 40000 * S.Q ^ (4 * g + 6) * S.ell := by ring
    _ ≤ S.mD k / 4 := h2

theorem Ok.cond2 (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) :
    S.eT (k + 1) * S.Kg / S.H (k + 1) ≤ 1 := by
  have hE := hS.exp_le_bigE (show k ≤ S.D by omega)
  have hH0 := hS.H_pos (k + 1)
  have hW1 := hS.W_le_one (k + 1)
  have hW0 := hS.W_pos (k + 1)
  have hl0 := hS.hell0
  have hl1 := hS.hell1
  have hQ0 := hS.Q_pos
  have e : S.eT (k + 1) * S.Kg / S.H (k + 1) = S.W (k + 1) * S.ell ^ 2 * (S.ell * S.Q ^ 4) := by
    rw [eT_eq]; unfold Kg; field_simp
  rw [e]
  have h1 : S.ell * S.Q ^ 4 ≤ 1 := hS.ellQ (by have := ten_le_gExp S.D k; omega)
  have h2 : S.ell ^ 2 ≤ 1 := pow_le_one₀ hl0.le hl1
  calc S.W (k + 1) * S.ell ^ 2 * (S.ell * S.Q ^ 4) ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by ring

theorem Ok.cond3 (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    2 * (S.CJ k * S.W k) * S.Kg / S.H (k + 1) + 2 * S.Q * (S.H (k + 1) *
      pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) (k + 1) + ((k + 1 : ℕ) : ℝ) *
      pairDc S.Q S.Kg (S.H (k + 1)) (S.eT (k + 1)) (S.CJ k * S.W k) (S.BR k) (S.mD k) S.D (S.n k)
        (S.nG k) (k + 1 - 1)) ≤ S.W (k + 1) := by
  obtain ⟨hge1, hge2, hge3⟩ := gExp_succ_ge S.D k
  have hGD : gExp S.D (k + 1) ≤ gExp S.D S.D := gExp_mono S.D hk
  have hE := hS.exp_le_bigE (le_refl S.D)
  set g := gExp S.D k with hg
  set G1 := g + 1 + S.D * (3 * g + 11) with hG1
  have hD1 := hS.hD
  have hDg : 3 * g + 11 ≤ S.D * (3 * g + 11) := Nat.le_mul_of_pos_left _ hD1
  have hCJ0 := Ok.CJ_nonneg hL
  have hCJg := hL.2.2.2.2
  have hQ1 := hS.one_le_Q
  have hQ0 := hS.Q_pos
  have hbig := hS.big
  have hl0 := hS.hell0
  have hl1 := hS.hell1
  have hW := hS.W_succ (show k < S.D by omega)
  have hW'0 : 0 < S.W (k + 1) := hS.W_pos _
  have hH0 : 0 < S.H (k + 1) := hS.H_pos _
  have hH1 : S.H (k + 1) ≤ 1 := hS.H_le_one _
  have hHle : S.H (k + 1) ≤ S.W (k + 1) * S.ell ^ 30 := hS.H_le _
  have hl30 := hS.ell30
  have hHl : S.H (k + 1) ≤ S.W (k + 1) * S.ell := by
    calc S.H (k + 1) ≤ S.W (k + 1) * S.ell ^ 30 := hHle
      _ ≤ S.W (k + 1) * S.ell := by gcongr
  have hLm : pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) (k + 1) ≤ S.Q ^ G1 := hS.Lam_le hk hL hk
  have hLD : pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) S.D ≤ S.Q ^ G1 := hS.Lam_le hk hL le_rfl
  have hLD0 : 0 ≤ pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) S.D := by
    have := hS.one_le_X hk hL
    have := hL.2.2.1
    unfold pairLam; positivity
  have hLm0 : 0 ≤ pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) (k + 1) := by
    have := hS.one_le_X hk hL
    have := hL.2.2.1
    unfold pairLam; positivity
  have hZ := hS.Z_le hk hL
  have hZ1 := hS.one_le_Z hk hL
  have hkQ : ((k + 1 : ℕ) : ℝ) ≤ S.Q := by
    have h := hS.D_le (c := 1) (by norm_num) (by norm_num)
    have : ((k + 1 : ℕ) : ℝ) ≤ S.D := by exact_mod_cast hk
    linarith
  set W' := S.W (k + 1) with hW'
  set H := S.H (k + 1) with hH
  set ℓ := S.ell with hℓ
  set Lm := pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) (k + 1) with hLmdef
  set LD := pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) S.D with hLDdef
  set Z := pairZ S.Q (S.mD k) S.D (S.n k) (S.nG k) with hZdef
  have hWl0 : 0 < W' * ℓ := by positivity
  -- the gradient-precision term
  have ea : 2 * (S.CJ k * S.W k) * S.Kg / H = 2 * S.CJ k * S.Q ^ 3 * (W' * ℓ) := by
    rw [hW]; unfold Kg; field_simp
  -- the compatibility base
  have hs : pairS S.Q S.Kg H (S.eT (k + 1)) (S.CJ k * S.W k) (S.BR k) (S.mD k) S.D (S.nG k) ≤
      W' * ℓ * S.Q ^ (G1 + 2) := by
    unfold pairS
    have e4 : S.eT (k + 1) * S.Kg / H = S.Q ^ 4 * ℓ ^ 2 * (W' * ℓ) := by
      rw [eT_eq]; unfold Kg; field_simp; ring
    have e1 : S.CJ k * S.W k = S.CJ k * H * (W' * ℓ) := by rw [hW]; ring
    rw [ea, e4, e1]
    rw [← hLDdef]
    have t1 : S.CJ k * H * (W' * ℓ) ≤ S.Q ^ (G1 + 1) * (W' * ℓ) := by
      have : S.CJ k * H ≤ S.Q ^ (G1 + 1) := by
        calc S.CJ k * H ≤ S.Q ^ g * 1 := mul_le_mul hCJg hH1 hH0.le (by positivity)
          _ = S.Q ^ g := mul_one _
          _ ≤ S.Q ^ (G1 + 1) := hS.pow_le_pow (by omega)
      gcongr
    have t2 : 2 * S.CJ k * S.Q ^ 3 * (W' * ℓ) ≤ S.Q ^ (G1 + 1) * (W' * ℓ) := by
      have : 2 * S.CJ k * S.Q ^ 3 ≤ S.Q ^ (G1 + 1) := by
        calc 2 * S.CJ k * S.Q ^ 3 ≤ S.Q * S.Q ^ g * S.Q ^ 3 := by gcongr; linarith
          _ = S.Q ^ (g + 4) := by ring
          _ ≤ S.Q ^ (G1 + 1) := hS.pow_le_pow (by omega)
      gcongr
    have t3 : 2 * S.Q * H * LD ≤ 2 * (S.Q ^ (G1 + 1) * (W' * ℓ)) := by
      calc 2 * S.Q * H * LD ≤ 2 * S.Q * (W' * ℓ) * S.Q ^ G1 := by gcongr
        _ = 2 * (S.Q ^ (G1 + 1) * (W' * ℓ)) := by ring
    have t4 : S.Q ^ 4 * ℓ ^ 2 * (W' * ℓ) ≤ S.Q ^ (G1 + 1) * (W' * ℓ) := by
      have : S.Q ^ 4 * ℓ ^ 2 ≤ S.Q ^ (G1 + 1) := by
        calc S.Q ^ 4 * ℓ ^ 2 ≤ S.Q ^ 4 * 1 := by gcongr; exact pow_le_one₀ hl0.le hl1
          _ = S.Q ^ 4 := mul_one _
          _ ≤ S.Q ^ (G1 + 1) := hS.pow_le_pow (by omega)
      gcongr
    calc S.CJ k * H * (W' * ℓ) + 2 * S.CJ k * S.Q ^ 3 * (W' * ℓ) + 2 * S.Q * H * LD +
          S.Q ^ 4 * ℓ ^ 2 * (W' * ℓ)
        ≤ 5 * S.Q ^ (G1 + 1) * (W' * ℓ) := by linarith
      _ ≤ S.Q * S.Q ^ (G1 + 1) * (W' * ℓ) := by gcongr; linarith
      _ = W' * ℓ * S.Q ^ (G1 + 2) := by ring
  -- the compatibility threshold
  have hδ : pairDc S.Q S.Kg H (S.eT (k + 1)) (S.CJ k * S.W k) (S.BR k) (S.mD k) S.D (S.n k)
      (S.nG k) (k + 1 - 1) ≤ W' * ℓ * S.Q ^ (G1 + 2 + S.D * (4 * g + 11)) := by
    simp only [pairDc, Nat.add_sub_cancel]
    rw [← hZdef]
    have hZk : Z ^ (k + 1) ≤ S.Q ^ (S.D * (4 * g + 11)) := by
      calc Z ^ (k + 1) ≤ (S.Q ^ (4 * g + 11)) ^ (k + 1) := by gcongr
        _ = S.Q ^ ((4 * g + 11) * (k + 1)) := by rw [← pow_mul]
        _ ≤ S.Q ^ (S.D * (4 * g + 11)) :=
            hS.pow_le_pow (by rw [mul_comm]; exact Nat.mul_le_mul_right _ hk)
    have hs0 : 0 ≤ pairS S.Q S.Kg H (S.eT (k + 1)) (S.CJ k * S.W k) (S.BR k) (S.mD k) S.D
        (S.nG k) := by
      unfold pairS
      have := hS.eT_nonneg (k + 1)
      have := hS.W_pos k
      unfold Kg
      positivity
    calc pairS S.Q S.Kg H (S.eT (k + 1)) (S.CJ k * S.W k) (S.BR k) (S.mD k) S.D (S.nG k) *
          Z ^ (k + 1) ≤ W' * ℓ * S.Q ^ (G1 + 2) * S.Q ^ (S.D * (4 * g + 11)) := by
          gcongr
      _ = W' * ℓ * S.Q ^ (G1 + 2 + S.D * (4 * g + 11)) := by ring
  set δ := pairDc S.Q S.Kg H (S.eT (k + 1)) (S.CJ k * S.W k) (S.BR k) (S.mD k) S.D (S.n k)
      (S.nG k) (k + 1 - 1) with hδdef
  have hδ0 : 0 ≤ δ := by
    simp only [hδdef, pairDc, Nat.add_sub_cancel]
    have := hS.eT_nonneg (k + 1)
    have := hS.W_pos k
    have hZ0 : 0 ≤ Z := by linarith
    unfold pairS Kg
    positivity
  rw [ea]
  set E3 := G1 + 5 + S.D * (4 * g + 11) with hE3
  have hE3 : E3 + 1 ≤ bigE S.D := by
    have h1 : S.D * (3 * g + 11) ≤ S.D * (4 * g + 11) := Nat.mul_le_mul_left _ (by omega)
    omega
  have u1 : 2 * S.CJ k * S.Q ^ 3 * (W' * ℓ) ≤ S.Q ^ E3 * (W' * ℓ) := by
    have : 2 * S.CJ k * S.Q ^ 3 ≤ S.Q ^ E3 := by
      calc 2 * S.CJ k * S.Q ^ 3 ≤ S.Q * S.Q ^ g * S.Q ^ 3 := by gcongr; linarith
        _ = S.Q ^ (g + 4) := by ring
        _ ≤ S.Q ^ E3 := hS.pow_le_pow (by omega)
    gcongr
  have u2 : S.Q * (H * Lm) ≤ S.Q ^ E3 * (W' * ℓ) := by
    calc S.Q * (H * Lm) ≤ S.Q * ((W' * ℓ) * S.Q ^ G1) := by gcongr
      _ = S.Q ^ (G1 + 1) * (W' * ℓ) := by ring
      _ ≤ S.Q ^ E3 * (W' * ℓ) := by gcongr; omega
  have u3 : S.Q * (((k + 1 : ℕ) : ℝ) * δ) ≤ S.Q ^ E3 * (W' * ℓ) := by
    calc S.Q * (((k + 1 : ℕ) : ℝ) * δ) ≤
          S.Q * (S.Q * (W' * ℓ * S.Q ^ (G1 + 2 + S.D * (4 * g + 11)))) := by
          gcongr
      _ = S.Q ^ (G1 + 4 + S.D * (4 * g + 11)) * (W' * ℓ) := by ring
      _ ≤ S.Q ^ E3 * (W' * ℓ) := by gcongr; omega
  have hlast : ℓ * S.Q ^ (E3 + 1) ≤ 1 := hS.ellQ (by omega)
  calc 2 * S.CJ k * S.Q ^ 3 * (W' * ℓ) + 2 * S.Q * (H * Lm + ((k + 1 : ℕ) : ℝ) * δ)
      = 2 * S.CJ k * S.Q ^ 3 * (W' * ℓ) + 2 * (S.Q * (H * Lm)) +
          2 * (S.Q * (((k + 1 : ℕ) : ℝ) * δ)) := by
        ring
    _ ≤ 5 * S.Q ^ E3 * (W' * ℓ) := by linarith
    _ ≤ S.Q * S.Q ^ E3 * (W' * ℓ) := by gcongr; linarith
    _ = W' * (ℓ * S.Q ^ (E3 + 1)) := by ring
    _ ≤ W' * 1 := by gcongr
    _ = W' := mul_one _

/-! ### The tree budget -/

theorem Ok.one_le_CJ {k : ℕ} (hL : LevelOK S k) : 1 ≤ S.CJ k := by
  have := hL.2.2.1
  simp only [CJ, CJof]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem Ok.pairBudget (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) (hL : LevelOK S k) :
    PairBudget S.Q ζ (S.BR k) (S.H (k + 1)) S.Kg (S.eT (k + 1)) (S.W k) (S.w k) (S.W (k + 1))
      (S.w (k + 1)) (S.mass (k + 1) - 2 * S.loss k) (S.CJ (k + 1)) (S.n k) (k + 1)
      (S.Lam (k + 1)) (S.δc (k + 1)) := by
  have hL' := hS.level_succ hk hL
  have hB1 := hL.2.2.1
  have hBB : S.BR k ≤ S.BR (k + 1) := by rw [BR_succ]; exact le_max_left _ _
  have hCJ' : S.CJ k ≤ S.CJ (k + 1) := by
    simp only [CJ, CJof]; push_cast
    have : ((k : ℝ) + 4) * S.BR k ≤ ((k : ℝ) + 1 + 4) * S.BR (k + 1) := by
      apply mul_le_mul (by linarith) hBB (by linarith) (by positivity)
    linarith
  have hCJbig : 3 + 4 * max (S.BR k) (pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) (k + 1)) +
      2 * (((k + 1 : ℕ) : ℝ) + 1) *
        max (S.BR k) (pairLam S.Q (S.BR k) (S.mD k) S.D (S.nG k) (k + 1))
      ≤ S.CJ (k + 1) := by
    change 3 + 4 * S.BR (k + 1) + 2 * (((k + 1 : ℕ) : ℝ) + 1) * S.BR (k + 1) ≤
      3 + 2 * (((k + 1 : ℕ) : ℝ) + 4) * S.BR (k + 1)
    have : 0 ≤ S.BR (k + 1) := by linarith
    push_cast
    nlinarith
  exact pairBudget_of_small (K := S.Q) (ζ := ζ) (BR := S.BR k) (H := S.H (k + 1)) (Kg := S.Kg)
    (eT := S.eT (k + 1)) (W := S.W k) (W' := S.W (k + 1)) (mD := S.mD k) (CJ := S.CJ k)
    (CJ' := S.CJ (k + 1)) (n := S.n k) (M := S.D) (m := k + 1)
    hS.one_le_Q (hS.one_le_pow 3) (by linarith) (hS.H_pos _) (hS.eT_nonneg _) (hS.W_pos _)
    (Ok.one_le_CJ hL) (hS.mD_pos hk) (hS.mD_le_one hk) hL.1 (by omega) hk
    (hS.hζq.trans (hS.hqW.trans (hS.W_mono (Nat.zero_le k)))) (hS.W_mono (Nat.le_succ k))
    (hS.W_le_one _) hCJ' hCJbig (hS.cond1 hk hL) (hS.cond2 hk) (hS.cond3 hk hL)

theorem Ok.lstep (hS : S.Ok ζ) (k : ℕ) :
    2 * S.loss k + ((k + 1 : ℕ) + 1) * (9600 * S.Q ^ 3 / S.Kpop) ≤ S.loss (k + 1) := by
  have hc : 0 ≤ 9600 * S.Q ^ 3 / S.Kpop := by have := hS.Kpop_pos; have := hS.Q_pos; positivity
  set c := 9600 * S.Q ^ 3 / S.Kpop
  simp only [loss]
  push_cast
  have h2 : (k : ℝ) + 2 ≤ 2 ^ (k + 2) := by
    have h := Nat.lt_two_pow_self (n := k + 2)
    have : ((k + 2 : ℕ) : ℝ) ≤ ((2 ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast h.le
    push_cast at this; linarith
  have e : ((k : ℝ) + 1 + 1) * 2 ^ (k + 1 + 1) * c - (2 * (((k : ℝ) + 1) * 2 ^ (k + 1) * c) +
      ((k : ℝ) + 1 + 1) * c) = (2 ^ (k + 2) - ((k : ℝ) + 2)) * c := by ring
  have : 0 ≤ (2 ^ (k + 2) - ((k : ℝ) + 2)) * c := mul_nonneg (by linarith) hc
  linarith

theorem Ok.mstep (hS : S.Ok ζ) {k : ℕ} (hk : k + 1 ≤ S.D) :
    S.mass k ≤ S.mass (k + 1) - S.loss k := by
  have hl := hS.loss_le (show k ≤ S.D by omega)
  have hD1 : (0 : ℝ) < S.D + 1 := by positivity
  have hm := hS.hm0
  simp only [mass]
  push_cast
  have e : S.mstar * ((k : ℝ) + 1 + 1) / (S.D + 1) = S.mstar * ((k : ℝ) + 1) / (S.D + 1) +
      S.mstar / (S.D + 1) := by field_simp
  rw [e]
  have : S.loss k ≤ S.mstar / (S.D + 1) := by
    calc S.loss k ≤ S.mstar / (2 * (S.D + 1)) := hl
      _ ≤ S.mstar / (S.D + 1) := by
          apply div_le_div_of_nonneg_left hm.le hD1; linarith
  linarith

/-- **The schedule is a tree budget.** -/
theorem Ok.treeBudget (hS : S.Ok ζ) :
    TreeBudget S.Q ζ S.Kg S.Kpop S.H S.eT S.W S.w S.D S.n S.BR S.mass S.loss S.CJ S.Lam S.δc
      S.q₁ S.p₁ S.n₁ where
  hH := fun k _ _ => hS.H_pos k
  hKg := hS.one_le_pow 3
  kpop := hS.Kpop_pos
  pair := fun k hk => hS.pairBudget hk (hS.levels k (by omega))
  nstep := fun _ _ => le_rfl
  bstep := fun _ _ => le_rfl
  lstep := fun k _ => hS.lstep k
  mstep := fun _ hk => hS.mstep hk
  loss_nn := hS.loss_nonneg
  hζq₁ := hS.hζq
  hq₁W := hS.hqW
  hp₁ := hS.hp0
  hp₁w := by
    have h1 := Ok.one_le_CJ (hS.levels 0 (Nat.zero_le _))
    have hW := hS.W_pos 0
    calc S.p₁ ≤ S.W 0 := hS.hpW
      _ = 1 * S.W 0 := (one_mul _).symm
      _ ≤ S.CJ 0 * S.W 0 := by gcongr
  hW0 := hS.W_le_one 0
  hw0 := by
    have h1 := Ok.one_le_CJ (hS.levels 0 (Nat.zero_le _))
    have hW := hS.W_pos 0
    show 0 < S.CJ 0 * S.W 0
    positivity
  hCJ0 := by
    have := hS.one_le_Q
    simp only [CJ, CJof, BR_zero]; push_cast; linarith
  hwCJ0 := le_rfl
  n0 := le_rfl
  loss0 := by
    have hc : 0 ≤ 9600 * S.Q ^ 3 / S.Kpop := by have := hS.Kpop_pos; have := hS.Q_pos; positivity
    simp only [loss]; push_cast; linarith

theorem mass_top : S.mass S.D = S.mstar := by
  simp only [mass]; field_simp

theorem Ok.loss_top_le (hS : S.Ok ζ) : S.loss S.D ≤ S.mstar / 2 := by
  have h := hS.loss_le (le_refl S.D)
  have hm := hS.hm0
  calc S.loss S.D ≤ S.mstar / (2 * (S.D + 1)) := h
    _ ≤ S.mstar / 2 := by
        apply div_le_div_of_nonneg_left hm.le (by norm_num)
        have : (0 : ℝ) ≤ S.D := Nat.cast_nonneg _
        linarith

theorem W_top : S.W S.D = S.ell ^ S.top := by
  simp only [W, ω, omegaE_of_le (le_refl S.D)]

end Sched

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
