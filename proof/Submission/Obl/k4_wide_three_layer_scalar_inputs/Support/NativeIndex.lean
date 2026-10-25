import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreementLossBudget
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreementRetention
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeSlope
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeWidthBudgets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.DeepBudgets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.FieldRecovery
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.FieldCaps
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualExtraction

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

/-- The auxiliary scalar exponents used at one index. The hidden matching
window `sp` may depend on the index; the output depths do not. -/
structure NativeIndexScales where
  R : ℝ
  se : ℝ
  m : ℝ
  J : ℝ
  C₀ : ℝ
  A : ℝ
  B : ℝ
  εF : ℝ
  η : ℝ
  ζ : ℝ
  β : ℝ
  r : ℝ
  sp : ℝ
  scell : ℝ
  v₀ : ℝ

def nativeTau (d u : ℝ) : ℝ := (1 - d) * u / 2

def nativeAgreeParams (N d u M B : ℝ) : AgreeParams where
  δz := N ^ (-B)
  δU := N ^ (-2 * u)
  δX := N ^ (-2 * u)
  δt := N ^ (-M)
  eR := N ^ (-nativeTau d u)
  e := N ^ (-nativeTau d u) / 2

def nativeMatchThreshold (N d u : ℝ) : ℝ :=
  ((N ^ (-nativeTau d u) / 2) / 2) * N ^ (-((1 - d) * u) / 8)

def nativeMatchFactor (N K H d u : ℝ) : ℝ :=
  nativeMatchThreshold N d u * (4 * (K + N ^ (-2 * u)) + 2) /
      (N ^ (-nativeTau d u) / 2) +
    4 * (H * N ^ (d * u)) *
      (100 * H * K ^ 2 * N ^ (-u) + N ^ (-2 * u) * (24 * H * K)) /
        nativeMatchThreshold N d u

def nativeReferenceDrift (N K q M : ℝ) : ℝ :=
  N ^ (-M) / q + N ^ (-M) * (2 * K + N ^ (-M)) / 2

def nativeNearRadius (N K q M B : ℝ) : ℝ :=
  2 * N ^ (-M) + (q * N ^ (-M) + q * N ^ (-B)) * (3 * K + N ^ (-M)) +
    (K + 1) * (q * N ^ (-B))

/-- Every premise in this record is an inequality between real numbers.
The original laws, assignments, and finite menus occur only in the theorem
which consumes it. -/
structure NativeIndexBudget (N K d S κ s u v M H q θ : ℝ)
    (E : NativeIndexScales) : Prop where
  s_nonneg : 0 ≤ s
  se_nonneg : 0 ≤ E.se
  εF_nonneg : 0 ≤ E.εF
  u_nonneg : 0 ≤ u
  M_nonneg : 0 ≤ M
  m_nonneg : 0 ≤ E.m
  M_m : M ≤ E.m
  M_A : M ≤ E.A
  M_B : M ≤ E.B
  two_u_M : 2 * u ≤ M
  m_B : E.m ≤ E.B
  field_mesh : E.B = E.C₀ * (E.A + nativeTau d u)
  chart_length : N ^ (-M) ≤ q
  source_width : K * N ^ (-M) ≤ q * N ^ (-κ * s) * N ^ (-2 * u)
  reference_drift : nativeReferenceDrift N K q M ≤ N ^ (-2 * u)
  gap : 10 * H * N ^ (-2 * u) ≤ N ^ (-nativeTau d u)
  match_factor : nativeMatchFactor N K H d u ≤ N ^ (-E.β)
  mass : N ^ (-E.η) + 81 * N ^ (-E.ζ) +
      2 * (K * N ^ E.ζ) * N ^ (-E.β) * (100000000 * K ^ 4 * H ^ 4) ≤ H⁻¹
  conditional : 2 * K * N ^ E.ζ ≤ N ^ E.η
  r_lo : E.R⁻¹ ≤ E.r
  r_hi : E.r ≤ E.R
  sp_lo : 0 ≤ E.sp
  sp_hi : E.sp ≤ E.R
  B_lo : E.R⁻¹ ≤ E.B
  B_hi : E.B ≤ E.R
  window : N ^ (-s) * (2 * H + 1) * N ^ (-u) = N ^ (-E.sp)
  match_mesh_time : N ^ (-E.r) ≤ q * N ^ (-M) / 2
  match_mesh_chart : 5 * K ^ 2 * N ^ (-E.r) ≤ N ^ (-M)
  match_mesh_transverse : 5 * K ^ 2 * N ^ (-E.r) ≤
      q * N ^ (-κ * s) * N ^ (-2 * u) / 2
  match_mesh_width : (3 + 3 * K) * N ^ (-E.r) ≤ q * N ^ (-κ * s)
  match_lip : 3 * (H * N ^ (2 * s)) * N ^ (-E.r) +
      N ^ (-s) * H * (3 * K + 7) * (3 * K + 3) * N ^ (-E.r) /
        (q * N ^ (-κ * s)) ≤ N ^ (-E.sp)
  field_K : 3 * K ≤ N ^ E.η
  field_H : H * (5 + 3 * K) ≤ N ^ E.η
  field_fit : N ^ (-nativeTau d u) + H * (N ^ (-E.B) + N ^ (-M) / q + N ^ (-M)) ≤
      N ^ E.η * N ^ (-nativeTau d u)
  field_base_width : N ^ (-E.B) ≤ N ^ (-κ * s)
  cell_lo : 0 ≤ E.scell
  cell_hi : E.scell ≤ E.R
  R_one : 1 ≤ E.R
  cell_hidden_width : 2 * K * N ^ (-s) ≤ N ^ (-E.scell)
  cell_mesh : (K + K ^ 2 + 1) * N ^ (-E.r) ≤ q * N ^ (-E.B) / 2
  cell_lip : 3 * (H * N ^ (2 * s)) * N ^ (-E.r) ≤ N ^ (-E.scell)
  cell_budget : 2250 * K ^ 3 * (N ^ (-E.scell)) ^ d ≤
      N ^ E.η * (N ^ (-s)) ^ d
  frost_v₀_pos : 0 < E.v₀
  frost_v₀_B : E.v₀ ≤ E.B
  frost_dimension : E.v₀ * S ≤ E.η
  frost_K : 4 * K ≤ N ^ E.η
  frost_lo : E.R⁻¹ ≤ E.v₀
  deep_coordinates : 100 * K ^ 7 * N ^ (2 * s - κ * E.se) ≤ N ^ (-E.B)
  deep_corrected : 1600 * N ^ E.εF * K ^ 8 * N ^ (2 * s - κ * E.se) ≤ N ^ (-v)
  recovery : H * N ^ (-v) +
      (N ^ E.εF * N ^ (-nativeTau d u) + N ^ (-nativeTau d u) + H * N ^ (-E.B)) *
        (K + K ^ 2) ≤ (8 * H * K ^ 2) * N ^ (-v)
  output_small : (8 * H * K ^ 2) * (5 + 3 * K) * N ^ (-E.m) ≤ N ^ (-v)
  output_large : 54 ≤ N ^ E.εF
  output_loss : 2 * E.εF ≤ θ
  output_C : E.εF ≤ θ
  output_count : 84 * K *
      ((ENNReal.ofReal K / ENNReal.ofReal (N ^ (-2 * E.εF))).toReal *
        (48 * K) * (8 * H * K ^ 2) ^ 3) ≤ N ^ θ
  output_L : H * N ^ (2 * s) ≤ N ^ E.J
  output_K : K ≤ N ^ θ

/-- The measured output of fine-state pruning and coefficient consensus.
Its law is still dominated by the original compared-block law. -/
structure NativeConsensusData {α : Type} [MeasurableSpace α] {cfg : Data α}
    {k : ℕ} {s u v M H : ℝ}
    (CB : ComparedBlock cfg k s u v (cfg.N k ^ (-M)) H) (E : NativeIndexScales) where
  lam : Measure (α × ℝ)
  center : (Fin 4 → ℤ) → CB.Γ
  le : lam ≤ CB.lam
  mass : ENNReal.ofReal (cfg.N k ^ (-E.η)) *
      (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)) ≤ lam univ
  agree : ∀ᵐ p ∂lam,
    CB.Rg (nativeAgreeParams (cfg.N k) cfg.d u M E.B)
      (CB.sig (nativeAgreeParams (cfg.N k) cfg.d u M E.B) p) (CB.cls p)
      (center (CB.sig (nativeAgreeParams (cfg.N k) cfg.d u M E.B) p))
  state : ∀ (Q : Fin 4 → ℤ) (V : Set ℤ),
    lam {p | CB.sig (nativeAgreeParams (cfg.N k) cfg.d u M E.B) p = Q ∧
        vbin (cfg.N k ^ (-E.B)) (cfg.b k p.1 3) ∈ V} ≤
      ENNReal.ofReal (cfg.N k ^ E.η) *
        lam (CB.sig (nativeAgreeParams (cfg.N k) cfg.d u M E.B) ⁻¹' {Q}) *
        paletteBins (cfg.π k) (cfg.N k ^ (-E.B)) V

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
