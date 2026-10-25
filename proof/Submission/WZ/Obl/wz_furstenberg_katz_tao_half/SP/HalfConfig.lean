-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.HalfConfig.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CotFrame

/-!
# The configuration produced by the near-extremal extraction at `s = 1/2`

Interface between the extraction (from a configuration with few separated lines) and the
two endgames:
* the parallel-projection endgame (`dense_family_expansion`), which uses the pins `H` on the
  rich line `ℓ₀` and their 1/2-Frostman positions;
* the Elekes-type endgame (BSG for sums and products, `discretized_sum_product`), which
  uses one pin of `H` (and would add a joined relation among the pins of `Q`).

All quantities are in the original coordinates; `ℓ₀` passes through `p₀` with unit
normal `n`. Losses are measured by `K` (think `K = r ^ (-κ)`) and the separation of the
geometry by `c` (think `c = r ^ κ`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- Katz–Tao bushes of exponent `1/2` with constant `K` at scale `r`. -/
def HalfBush (r K : ℝ) (E : Finset Plane) : Prop :=
  (∀ e ∈ E, ‖e‖ = 1) ∧ (∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → r ≤ dist e e') ∧
    ∀ u : Plane, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      ((E.filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ K * (ρ / r) ^ (1 / 2 : ℝ)

/-- The configuration at `s = 1/2`. Joins and closeness to `ℓ₀` are measured at `64 r`
(what the extraction from line classes gives); separations and bushes at `r`. -/
structure HalfConfig (r K c : ℝ) (n p₀ p₁ p₂ : Plane) (H Q : Finset Plane)
    (D : Plane → Finset Plane) (Qh : Plane → Finset Plane) : Prop where
  unit_normal : ‖n‖ = 1
  bush : ∀ p ∈ insert p₁ (insert p₂ (H ∪ Q)), HalfBush r K (D p)
  /-- the two base pins lie on `ℓ₀`, at distance at least `c` along it -/
  base_on_line : |acrossCoord n p₀ p₁| ≤ 64 * r ∧ |acrossCoord n p₀ p₂| ≤ 64 * r
  base_gap : c ≤ |alongCoord n p₀ p₂ - alongCoord n p₀ p₁|
  /-- the pins of `H` lie on `ℓ₀`, between the base pins and closer to `p₁` -/
  line_pins : ∀ p ∈ H, |acrossCoord n p₀ p| ≤ 64 * r ∧
    0 ≤ (alongCoord n p₀ p - alongCoord n p₀ p₁) * (alongCoord n p₀ p₂ - alongCoord n p₀ p) ∧
    |alongCoord n p₀ p - alongCoord n p₀ p₁| ≤ |alongCoord n p₀ p₂ - alongCoord n p₀ p|
  /-- positions along `ℓ₀` are separated and 1/2-Frostman -/
  line_sep : ∀ p ∈ H, ∀ p' ∈ H, p ≠ p' → r ≤ |alongCoord n p₀ p - alongCoord n p₀ p'|
  line_frostman : ∀ x ρ : ℝ, r ≤ ρ →
    ((H.filter (fun p => |alongCoord n p₀ p - x| ≤ ρ)).card : ℝ) ≤
      K * ρ ^ (1 / 2 : ℝ) * (H.card : ℝ)
  line_nonempty : H.Nonempty
  /-- all pins are near `p₀` -/
  line_bounded : ∀ p ∈ insert p₁ (insert p₂ H), ‖p - p₀‖ ≤ 8
  /-- the joined pins: separated, bounded, away from `ℓ₀` on one side -/
  pins_sep : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → r ≤ dist q q'
  pins_bounded : ∀ q ∈ Q, ‖q - p₀‖ ≤ 8
  pins_far : ∀ q ∈ Q, c ≤ acrossCoord n p₀ q
  pins_many : K⁻¹ * r⁻¹ ≤ (Q.card : ℝ)
  /-- every joined pin lies on bush lines of both base pins -/
  join₁ : ∀ q ∈ Q, ∃ e ∈ D p₁, |inner ℝ (q - p₁) e| ≤ 64 * r
  join₂ : ∀ q ∈ Q, ∃ e ∈ D p₂, |inner ℝ (q - p₂) e| ≤ 64 * r
  /-- each pin of `H` is joined to a dense part of `Q` -/
  line_dense : ∀ p ∈ H, Qh p ⊆ Q ∧ K⁻¹ * (Q.card : ℝ) ≤ ((Qh p).card : ℝ) ∧
    ∀ q ∈ Qh p, ∃ e ∈ D p, |inner ℝ (q - p) e| ≤ 64 * r

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
