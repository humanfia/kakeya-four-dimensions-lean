-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Consensus; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Numerics
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Prune

/-!
# Coefficient consensus of compared samples (paper Prop. 8.4, coefficient agreement)

`Parent.Valid.consensus_of_sample`: for a valid parent there is a room multiplier `Λ` such that,
for every base-mesh multiplier `C₀ ≥ 1` and compared exponents `(r, u, v, m)` with
`Λ (1 + C₀) m ≤ U`, and every `η > 0`, there is `δ > 0` such that eventually every compared
sample with loss `2 ≤ H ≤ N^δ`, `K ≤ H`, carries a `ConsensusLaw` at native base mesh and
velocity mesh `N^(-C₀ (m + r + (1-d) u / 2))`, signal mesh `N^(-(r+u))`, agreement precision
`N^(-(r + (1-d) u / 2))` and domination constant `N^η`.

* `consensus_exponent_facts`: the exponent inequalities;
* `consensus_of_numerics`: the index-local derivation of the numeric hypotheses of
  `consensus_at_index` from monomial bounds;
* `Parent.Valid.consensus_of_sample`: the eventual statement.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

/-- Splitting a power: `A N^(c + e) ≤ 1` gives `A N^c ≤ N^(-e)`. -/
theorem agree_le_rpow_of_mul_le_one {N A c e : ℝ} (hN : 0 < N) (hA : 0 ≤ A)
    (h : A * N ^ (c + e) ≤ 1) : A * N ^ c ≤ N ^ (-e) := by
  have hsplit : N ^ c = N ^ (c + e) * N ^ (-e) := by
    rw [← Real.rpow_add hN]
    ring_nf
  rw [hsplit]
  calc A * (N ^ (c + e) * N ^ (-e)) = (A * N ^ (c + e)) * N ^ (-e) := by ring
    _ ≤ 1 * N ^ (-e) := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hN.le _)
    _ = N ^ (-e) := one_mul _

/-- **The exponent inequalities** of coefficient consensus. -/
theorem consensus_exponent_facts {d κ ℓ r u m C₀ : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hℓ : 0 < ℓ) (hr : 0 < r) (hu : 0 < u) (hur : u < r)
    (hm10000 : 10000 * (1 + ℓ) * r < m) (hC₀ : 1 ≤ C₀) :
    10000 * r < m ∧ 10000 * (ℓ * r) < m ∧ 0 < m ∧ 0 ≤ d * u ∧ d * u ≤ u ∧
      (1 - d) * u / 8 ≤ u / 8 ∧ 0 < (1 - d) * u / 8 ∧ (1 - d) * u / 2 ≤ u ∧
      m + r ≤ C₀ * (m + r + (1 - d) * u / 2) ∧
      r + C₀ * (m + r + (1 - d) * u / 2) + (r + u) ≤ 2 * (1 + C₀) * m ∧
      0 < κ * r ∧ κ * r ≤ r ∧ 0 < ℓ * r := by
  have hℓr : 0 < ℓ * r := mul_pos hℓ hr
  have h1 : 10000 * r < m := by nlinarith
  have h2 : 10000 * (ℓ * r) < m := by nlinarith
  have hm : 0 < m := by linarith
  have hdu0 : 0 ≤ d * u := mul_nonneg hd0 hu.le
  have hdu : d * u ≤ u := by nlinarith
  have h1d : 0 < 1 - d := by linarith
  have hτ : (1 - d) * u / 8 ≤ u / 8 := by nlinarith
  have hτ0 : 0 < (1 - d) * u / 8 := by positivity
  have hb : (1 - d) * u / 2 ≤ u := by nlinarith
  have hb0 : 0 ≤ (1 - d) * u / 2 := by positivity
  have hβ : m + r ≤ C₀ * (m + r + (1 - d) * u / 2) := by
    have h0 : 0 ≤ m + r + (1 - d) * u / 2 := by positivity
    nlinarith
  have hβle : C₀ * (m + r + (1 - d) * u / 2) ≤ C₀ * (m + 2 * r) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hroom : r + C₀ * (m + r + (1 - d) * u / 2) + (r + u) ≤ 2 * (1 + C₀) * m := by
    have : C₀ * (m + 2 * r) ≤ C₀ * m + C₀ * m := by nlinarith
    linarith
  have hκr : 0 < κ * r := mul_pos hκ hr
  have hκr1 : κ * r ≤ r := by nlinarith
  exact ⟨h1, h2, hm, hdu0, hdu, hτ, hτ0, hb, hβ, hroom, hκr, hκr1, hℓr⟩

namespace Parent

namespace ComparedSample

variable {α : Type} [MeasurableSpace α] {p : Parent α}
variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

/-- **Consensus at one index from monomial bounds.** -/
theorem consensus_of_numerics (hbase : p.Basic) {R : ℝ} (hat : p.AtDepth k r R)
    (hN : 1 < p.N k) (hK1 : 1 ≤ p.K k) (hKH : p.K k ≤ H)
    (hr : 0 < r) (hu : 0 < u) (hm : 0 < m) (hd0 : 0 ≤ p.d) (hd1 : p.d < 1)
    (hℓr : 0 < p.ℓ * r) (hdu : 0 ≤ p.d * u) (hbr : (1 - p.d) * u / 2 ≤ u)
    {βb τ₀ rm δ η : ℝ} (hβb : m + r ≤ βb) (hτ₀ : τ₀ = (1 - p.d) * u / 8) (hτ₀0 : 0 < τ₀)
    (hcapk : ∀ s' : ℝ, 0 ≤ s' → s' ≤ r + u → ∀ (q : Fin 3 → ℤ) (a v' : ℤ),
      p.μ k {ω | p.z k (p.N k) rm ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s'))⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v'} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * rm - p.d * s')) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v'})
    (hpr : ∀ ϑ : ℝ, 0 < ϑ → p.N k ^ (-(2 * δ)) ≤ ϑ →
      ∀ (Q : Fin (p.n k r)) (θ : Measure (α × ℝ)), θ ≤ p.μ k →
        (∀ᵐ ω ∂θ, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q)) →
        ∃ θ' : Measure (α × ℝ), θ' ≤ θ ∧
          θ univ ≤ θ' univ +
            ENNReal.ofReal ϑ * (ENNReal.ofReal (p.blockLen k r) * p.ν k (p.A k r Q)) ∧
          ∀ (σ : Fin 4 → ℤ) (j : ℤ),
            θ' {ω | p.nativeState k r Q (p.N k ^ (-βb)) (p.N k ^ (-(r + u))) ω = σ ∧
                ⌊p.b k ω.1 3 / p.N k ^ (-βb)⌋ = j} ≤
              ENNReal.ofReal (324 * p.K k / ϑ) *
                θ' {ω | p.nativeState k r Q (p.N k ^ (-βb)) (p.N k ^ (-(r + u))) ω = σ} *
                p.π k {x | ⌊x / p.N k ^ (-βb)⌋ = j})
    (e1 : 16000000 * p.K k ^ 11 * p.N k ^ (m / 1000 - βb + (r + u)) ≤ 1)
    (e2 : 16000000 * p.K k ^ 11 * p.N k ^ (m / 1000 - m + (r + u)) ≤ 1)
    (e3 : 4 * p.K k * p.N k ^ (m - βb) ≤ 1)
    (e4 : 2 * p.K k * p.N k ^ (p.κ * r + βb - rm) ≤ 1)
    (e5 : 3 * p.K k ^ 2 * p.N k ^ (m - rm) ≤ 1)
    (e6 : 864 * p.K k ^ 4 * p.N k ^ (m / 1000 - rm + (r + u)) ≤ 1)
    (e7 : 16 * H * p.N k ^ (-(2 * δ)) ≤ 1)
    (e8 : 10368 * p.K k * H * p.N k ^ (-η) ≤ 1)
    (e9 : 300000000000 * p.K k ^ 4 * H ^ 8 * p.N k ^ (-τ₀) ≤ 1)
    (e10 : 20000000000000 * p.K k ^ 3 * H ^ 13 * p.N k ^ (-(3 * τ₀)) ≤ 1)
    (e11 : 600000000000 * p.K k ^ 5 * H ^ 12 *
      p.N k ^ (p.d * u - m + p.κ * r + p.ℓ * r) ≤ 1) :
    Nonempty (p.ConsensusLaw k s βb (r + u) βb (p.N k ^ (-(r + (1 - p.d) * u / 2)))
      (p.N k ^ η)) := by
  have hH2 : 2 ≤ H := s.loss_one
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hNpos : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := hN.le
  have hK0 : 0 ≤ p.K k := by linarith
  have hKpos : 0 < p.K k := by linarith
  have hβb0 : 0 < βb := by linarith
  have hδb1 : p.N k ^ (-βb) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hχ1 : p.N k ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hδbχ' : p.N k ^ (-βb) ≤ p.N k ^ (-m) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hfz : 8000000 * p.K k ^ 11 * p.N k ^ (m / 1000) * (p.N k ^ (-βb) + p.N k ^ (-m)) ≤
      p.N k ^ (-(r + u)) := by
    have h1 := agree_le_rpow_of_mul_le_one (A := 16000000 * p.K k ^ 11) (c := m / 1000 - βb)
      (e := r + u) hNpos (by positivity) e1
    have h2 := agree_le_rpow_of_mul_le_one (A := 16000000 * p.K k ^ 11) (c := m / 1000 - m)
      (e := r + u) hNpos (by positivity) e2
    have hs1 : p.N k ^ (m / 1000) * p.N k ^ (-βb) = p.N k ^ (m / 1000 - βb) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have hs2 : p.N k ^ (m / 1000) * p.N k ^ (-m) = p.N k ^ (m / 1000 - m) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    calc 8000000 * p.K k ^ 11 * p.N k ^ (m / 1000) * (p.N k ^ (-βb) + p.N k ^ (-m))
        = (16000000 * p.K k ^ 11 * p.N k ^ (m / 1000 - βb) +
            16000000 * p.K k ^ 11 * p.N k ^ (m / 1000 - m)) / 2 := by
          rw [← hs1, ← hs2]
          ring
      _ ≤ (p.N k ^ (-(r + u)) + p.N k ^ (-(r + u))) / 2 := by gcongr
      _ = p.N k ^ (-(r + u)) := by ring
  have hδbχ : 2 * (p.K k + 1) * p.N k ^ (-βb) ≤ p.N k ^ (-m) := by
    have h1 := agree_le_rpow_of_mul_le_one (A := 4 * p.K k) (c := -βb) (e := m) hNpos (by positivity)
      (by rw [show -βb + m = m - βb by ring]; exact e3)
    have h2 : 2 * (p.K k + 1) ≤ 4 * p.K k := by linarith
    calc 2 * (p.K k + 1) * p.N k ^ (-βb) ≤ 4 * p.K k * p.N k ^ (-βb) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hNpos.le _)
      _ ≤ _ := h1
  set E := p.N k ^ (-(r + (1 - p.d) * u / 2)) with hE_def
  have haE : p.N k ^ (-(r + u)) ≤ E :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hE0 : 0 < E := Real.rpow_pos_of_pos hNpos _
  -- the mesh of the source caps
  have h2T := hat.2.1
  have hrm1 : p.N k ^ (-rm) ≤ p.blockLen k r * p.N k ^ (-βb) / 2 := by
    have h1 := agree_le_rpow_of_mul_le_one (A := 2 * p.K k) (c := -rm) (e := p.κ * r + βb) hNpos
      (by positivity) (by rw [show -rm + (p.κ * r + βb) = p.κ * r + βb - rm by ring]; exact e4)
    have hsplit : p.N k ^ (-(p.κ * r + βb)) = p.N k ^ (-(p.κ * r)) * p.N k ^ (-βb) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have hT : (p.K k * p.N k ^ (p.κ * r))⁻¹ ≤ p.blockLen k r := by
      unfold blockLen
      exact inv_anti₀ (by positivity) h2T
    have hKN : p.N k ^ (-(p.κ * r)) = (p.N k ^ (p.κ * r))⁻¹ := Real.rpow_neg hNpos.le _
    have hNκ : 0 < p.N k ^ (p.κ * r) := Real.rpow_pos_of_pos hNpos _
    have hδbpos : 0 < p.N k ^ (-βb) := Real.rpow_pos_of_pos hNpos _
    have h2K : 0 < 2 * p.K k := by positivity
    calc p.N k ^ (-rm) = (2 * p.K k * p.N k ^ (-rm)) / (2 * p.K k) := by
          field_simp
      _ ≤ p.N k ^ (-(p.κ * r + βb)) / (2 * p.K k) := div_le_div_of_nonneg_right h1 h2K.le
      _ = (p.K k * p.N k ^ (p.κ * r))⁻¹ * p.N k ^ (-βb) / 2 := by
          rw [hsplit, hKN]
          field_simp
      _ ≤ p.blockLen k r * p.N k ^ (-βb) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hT hδbpos.le
  have hrm2 : 3 * p.K k ^ 2 * p.N k ^ (-rm) ≤ p.N k ^ (-m) :=
    agree_le_rpow_of_mul_le_one (A := 3 * p.K k ^ 2) (c := -rm) (e := m) hNpos (by positivity)
      (by rw [show -rm + m = m - rm by ring]; exact e5)
  have hrm3 : 54 * p.N k ^ (m / 1000) * (p.K k + 1) ^ 4 * p.N k ^ (-rm) ≤
      p.N k ^ (-(r + u)) := by
    have h1 := agree_le_rpow_of_mul_le_one (A := 864 * p.K k ^ 4) (c := m / 1000 - rm) (e := r + u)
      hNpos (by positivity) e6
    have hK4 : (p.K k + 1) ^ 4 ≤ 16 * p.K k ^ 4 := by
      have : p.K k + 1 ≤ 2 * p.K k := by linarith
      calc (p.K k + 1) ^ 4 ≤ (2 * p.K k) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
        _ = 16 * p.K k ^ 4 := by ring
    have hs : p.N k ^ (m / 1000) * p.N k ^ (-rm) = p.N k ^ (m / 1000 - rm) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have hNN : 0 ≤ p.N k ^ (m / 1000) * p.N k ^ (-rm) := by positivity
    calc 54 * p.N k ^ (m / 1000) * (p.K k + 1) ^ 4 * p.N k ^ (-rm)
        = 54 * (p.K k + 1) ^ 4 * (p.N k ^ (m / 1000) * p.N k ^ (-rm)) := by ring
      _ ≤ 54 * (16 * p.K k ^ 4) * (p.N k ^ (m / 1000) * p.N k ^ (-rm)) := by gcongr
      _ = 864 * p.K k ^ 4 * p.N k ^ (m / 1000 - rm) := by rw [hs]; ring
      _ ≤ _ := h1
  -- the pruning loss parameter and the target domination constant
  set ϑ := 1 / (16 * H) with hϑ_def
  have hϑ0 : 0 < ϑ := by positivity
  have hϑlo : p.N k ^ (-(2 * δ)) ≤ ϑ := by
    rw [hϑ_def, le_div_iff₀ (by positivity)]
    linarith
  have hC : 2 * (324 * p.K k / ϑ) ≤ p.N k ^ η := by
    have hval : 2 * (324 * p.K k / ϑ) = 10368 * p.K k * H := by
      rw [hϑ_def]
      field_simp
      ring
    have hNη : p.N k ^ (-η) * p.N k ^ η = 1 := by
      rw [← Real.rpow_add hNpos]
      simp
    rw [hval]
    calc 10368 * p.K k * H = 10368 * p.K k * H * p.N k ^ (-η) * p.N k ^ η := by
          rw [mul_assoc (10368 * p.K k * H), hNη, mul_one]
      _ ≤ 1 * p.N k ^ η := mul_le_mul_of_nonneg_right e8 (Real.rpow_nonneg hNpos.le _)
      _ = p.N k ^ η := one_mul _
  -- the disagreement numeric
  have hdu1 : 1 ≤ p.N k ^ (p.d * u) := Real.one_le_rpow hN1 hdu
  have hid : p.N k ^ (p.d * u) * p.N k ^ (-(r + u)) =
      E * p.N k ^ (-τ₀) * p.N k ^ (-(3 * τ₀)) := by
    rw [hE_def, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    rw [hτ₀]
    ring
  have hW : 1 / p.blockWidth k r ≤ p.K k * (p.N k ^ (p.κ * r) * p.N k ^ (p.ℓ * r)) := by
    have hw : p.blockWidth k r = ((2 : ℝ) ^ p.T k r)⁻¹ * (p.N k ^ (p.ℓ * r))⁻¹ := by
      unfold blockWidth blockLen
      rw [show -p.ℓ * r = -(p.ℓ * r) by ring, Real.rpow_neg hNpos.le]
    have hNl : 0 < p.N k ^ (p.ℓ * r) := Real.rpow_pos_of_pos hNpos _
    rw [hw, one_div, mul_inv, inv_inv, inv_inv]
    calc (2 : ℝ) ^ p.T k r * p.N k ^ (p.ℓ * r) ≤
          p.K k * p.N k ^ (p.κ * r) * p.N k ^ (p.ℓ * r) :=
          mul_le_mul_of_nonneg_right h2T hNl.le
      _ = _ := by ring
  have hidZ : p.N k ^ (p.d * u) * p.N k ^ (-m) * (p.N k ^ (p.κ * r) * p.N k ^ (p.ℓ * r)) =
      p.N k ^ (p.d * u - m + p.κ * r + p.ℓ * r) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hτpos : 0 < p.N k ^ (-τ₀) := Real.rpow_pos_of_pos hNpos _
  have hτ1 : p.N k ^ (-τ₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hεnum := agree_epsnum_core (K := p.K k) (H := H) (X := p.N k ^ (-τ₀))
    (Y := p.N k ^ (-(3 * τ₀))) (Z := p.N k ^ (p.d * u - m + p.κ * r + p.ℓ * r)) (E := E)
    (a₁ := p.N k ^ (-(r + u))) (Nd := p.N k ^ (p.d * u)) (χ := p.N k ^ (-m))
    (wQ := p.blockWidth k r) (W := p.N k ^ (p.κ * r) * p.N k ^ (p.ℓ * r))
    (θ' := E / 8 * p.N k ^ (-τ₀)) (ϑ := ϑ) hK1 hH1 hτpos (Real.rpow_nonneg hNpos.le _)
    (Real.rpow_nonneg hNpos.le _) hE0 rfl hdu1 hid (Real.rpow_nonneg hNpos.le _)
    (agree_blockWidth_pos (p := p) r hNpos) hW hidZ hϑ_def e9 e10 e11
  have hθ'0 : 0 < E / 8 * p.N k ^ (-τ₀) := by positivity
  have hθ'E : E / 8 * p.N k ^ (-τ₀) ≤ E / 8 := by
    have h8 : 0 < E / 8 := by positivity
    calc E / 8 * p.N k ^ (-τ₀) ≤ E / 8 * 1 := mul_le_mul_of_nonneg_left hτ1 h8.le
      _ = E / 8 := mul_one _
  exact s.consensus_at_index hbase hat hN hK1 hKH hℓr.le hm.le (by linarith) hd0 hd1.le
    hδb1 hχ1 hδbχ' hfz hδbχ haE hrm1 hrm2 hrm3 hcapk hθ'0 hθ'E hϑ0 le_rfl
    (fun Q θ hθ hθs => hpr ϑ hϑ0 hϑlo Q θ hθ hθs) hεnum hC

end ComparedSample

end Parent

/-- **Coefficient consensus of compared samples.** -/
theorem Parent.Valid.consensus_of_sample {α : Type} [MeasurableSpace α] {p : Parent α}
    (h : p.Valid) : ∃ Λ : ℝ, 0 < Λ ∧ ∀ (C₀ : ℝ), 1 ≤ C₀ → ∀ {r u v m : ℝ},
    p.ComparedExponents r u v m →
    Λ * (1 + C₀) * m ≤ p.U → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in Filter.atTop,
      ∀ H : ℝ, 2 ≤ H → p.K k ≤ H → H ≤ p.N k ^ δ →
      ∀ (s : p.ComparedSample k r u v m H),
        Nonempty (p.ConsensusLaw k s (C₀ * (m + r + (1 - p.d) * u / 2)) (r + u)
          (C₀ * (m + r + (1 - p.d) * u / 2)) (p.N k ^ (-(r + (1 - p.d) * u / 2)))
          (p.N k ^ η)) := by
  obtain ⟨Λn, hΛn, hprune⟩ := h.nativeStatePruning_uniform
  refine ⟨2 * Λn, by positivity, ?_⟩
  intro C₀ hC₀ r u v m hexp hroom η hη
  obtain ⟨⟨hr, hv, hvr, hrvm, hℓrm, hrU⟩, hu, hur, hvd, hm10000, hκu⟩ := hexp
  have hd0 := h.dimension_nonneg
  have hd1 := h.dimension_lt_one
  have hκ := h.rate_pos
  obtain ⟨hx1, hx2, hm, hdu0, hdu, hτu, hτ0, hbr, hβb_ge, hroomβ, hκr, hκr1, hℓr⟩ :=
    consensus_exponent_facts hd0 hd1 hκ h.rate_le_one h.transverse_pos hr hu hur hm10000 hC₀
  set βb := C₀ * (m + r + (1 - p.d) * u / 2) with hβb_def
  set τ₀ := (1 - p.d) * u / 8 with hτ₀_def
  set δ := min (η / 4) (τ₀ / 20) with hδ_def
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδη : δ ≤ η / 4 := min_le_left _ _
  have hδτ : δ ≤ τ₀ / 20 := min_le_right _ _
  refine ⟨δ, hδ0, ?_⟩
  have hβb0 : 0 < βb := by linarith
  -- the pruning
  have hroom' : Λn * (r + βb + (r + u)) ≤ p.U :=
    calc Λn * (r + βb + (r + u)) ≤ Λn * (2 * (1 + C₀) * m) :=
          mul_le_mul_of_nonneg_left hroomβ hΛn.le
      _ = 2 * Λn * (1 + C₀) * m := by ring
      _ ≤ p.U := hroom
  have hδ₁ : 2 * δ < r + (r + u) := by linarith
  have hprune' := hprune r βb (r + u) βb hr hβb0 (by linarith) hβb0 hroom' (2 * δ) hδ₁
  -- the preparation at depth r
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < r⁻¹ + 2 := by linarith
  have hRr : (r⁻¹ + 2)⁻¹ ≤ r := by
    rw [inv_le_comm₀ (by linarith) hr]
    linarith
  have hrU' : r ≤ p.U := by
    have : 0 < 3 * m / p.κ := by positivity
    linarith
  have hprep := h.prepared (r⁻¹ + 2) hR
  -- the caps at a fine mesh
  set rm := p.κ * r + βb + m + r + u + 1 with hrm_def
  have hrm0 : 0 < rm := by rw [hrm_def]; linarith
  set Rc := rm + m + r + u + rm⁻¹ + m⁻¹ + 2 with hRc_def
  have hrminv : 0 < rm⁻¹ := inv_pos.mpr hrm0
  have hminv : 0 < m⁻¹ := inv_pos.mpr hm
  have hRc : 1 < Rc := by rw [hRc_def]; linarith
  have hRc0 : 0 < Rc := by linarith
  have hcaps := h.caps Rc hRc
  have hRcrm : Rc⁻¹ ≤ rm := by
    rw [inv_le_comm₀ hRc0 hrm0, hRc_def]
    linarith
  have hrmRc : rm ≤ Rc := by rw [hRc_def]; linarith
  have hRcm : Rc⁻¹ ≤ m := by
    rw [inv_le_comm₀ hRc0 hm, hRc_def]
    linarith
  have hmRc : m ≤ Rc := by rw [hRc_def]; linarith
  have hruRc : r + u ≤ Rc := by rw [hRc_def]; linarith
  -- eventual monomial bounds
  have e1 := agree_eventually_KH_le h 16000000 (by norm_num) 11 0 (a := m / 1000 - βb + (r + u))
    hδ0.le (by push_cast; linarith)
  have e2 := agree_eventually_KH_le h 16000000 (by norm_num) 11 0 (a := m / 1000 - m + (r + u))
    hδ0.le (by push_cast; linarith)
  have e3 := agree_eventually_KH_le h 4 (by norm_num) 1 0 (a := m - βb) hδ0.le
    (by push_cast; linarith)
  have e4 := agree_eventually_KH_le h 2 (by norm_num) 1 0 (a := p.κ * r + βb - rm) hδ0.le
    (by push_cast; rw [hrm_def]; linarith)
  have e5 := agree_eventually_KH_le h 3 (by norm_num) 2 0 (a := m - rm) hδ0.le
    (by push_cast; rw [hrm_def]; linarith)
  have e6 := agree_eventually_KH_le h 864 (by norm_num) 4 0 (a := m / 1000 - rm + (r + u)) hδ0.le
    (by push_cast; rw [hrm_def]; linarith)
  have e7 := agree_eventually_KH_le h 16 (by norm_num) 0 1 (a := -(2 * δ)) hδ0.le
    (by push_cast; linarith)
  have e8 := agree_eventually_KH_le h 10368 (by norm_num) 1 1 (a := -η) hδ0.le
    (by push_cast; linarith)
  have e9 := agree_eventually_KH_le h 300000000000 (by norm_num) 4 8 (a := -τ₀) hδ0.le
    (by push_cast; linarith)
  have e10 := agree_eventually_KH_le h 20000000000000 (by norm_num) 3 13 (a := -(3 * τ₀)) hδ0.le
    (by push_cast; linarith)
  have e11 := agree_eventually_KH_le h 600000000000 (by norm_num) 5 12
    (a := p.d * u - m + p.κ * r + p.ℓ * r) hδ0.le (by push_cast; linarith)
  have eN := h.scale_limit.eventually (eventually_gt_atTop (1 : ℝ))
  filter_upwards [hprep, hprune', hcaps, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, eN]
    with k hprepk hpr hcapk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 hN
  intro H hH2 hKH hHN s
  have hH0 : 0 ≤ H := by linarith
  have hcapk' : ∀ s' : ℝ, 0 ≤ s' → s' ≤ r + u → ∀ (q : Fin 3 → ℤ) (a v' : ℤ),
      p.μ k {ω | p.z k (p.N k) rm ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s'))⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v'} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * rm - p.d * s')) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v'} := by
    intro s' hs0 hs1 q a v'
    have hc := (hcapk rm s' m hRcrm hrmRc hs0 (by linarith) hRcm hmRc).2.2 true q a v'
    simpa using hc
  have f1 := e1 H hH0 hHN
  have f2 := e2 H hH0 hHN
  have f3 := e3 H hH0 hHN
  have f4 := e4 H hH0 hHN
  have f5 := e5 H hH0 hHN
  have f6 := e6 H hH0 hHN
  have f7 := e7 H hH0 hHN
  have f8 := e8 H hH0 hHN
  have f9 := e9 H hH0 hHN
  have f10 := e10 H hH0 hHN
  have f11 := e11 H hH0 hHN
  simp only [pow_zero, mul_one, pow_one] at f1 f2 f3 f4 f5 f6 f7 f8
  exact s.consensus_of_numerics h.basic (hprepk r hRr hrU') hN (h.subpower.1 k) hKH hr hu hm
    hd0 hd1 hℓr hdu0 hbr hβb_ge rfl hτ0 hcapk' hpr f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11


/-- **Coefficient consensus of compared samples, at any base mesh** `N^(-βb)` with
`m + r ≤ βb` and pruning room `Λ (r + βb + (r + u)) ≤ U`. -/
theorem Parent.Valid.consensus_of_sample_mesh {α : Type} [MeasurableSpace α] {p : Parent α}
    (h : p.Valid) : ∃ Λ : ℝ, 0 < Λ ∧ ∀ {r u v m βb : ℝ},
    p.ComparedExponents r u v m → m + r ≤ βb →
    Λ * (r + βb + (r + u)) ≤ p.U → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in Filter.atTop,
      ∀ H : ℝ, 2 ≤ H → p.K k ≤ H → H ≤ p.N k ^ δ →
      ∀ (s : p.ComparedSample k r u v m H),
        Nonempty (p.ConsensusLaw k s βb (r + u) βb (p.N k ^ (-(r + (1 - p.d) * u / 2)))
          (p.N k ^ η)) := by
  obtain ⟨Λn, hΛn, hprune⟩ := h.nativeStatePruning_uniform
  refine ⟨Λn, hΛn, ?_⟩
  intro r u v m βb hexp hβb_ge hroom' η hη
  obtain ⟨⟨hr, hv, hvr, hrvm, hℓrm, hrU⟩, hu, hur, hvd, hm10000, hκu⟩ := hexp
  have hd0 := h.dimension_nonneg
  have hd1 := h.dimension_lt_one
  have hκ := h.rate_pos
  obtain ⟨hx1, hx2, hm, hdu0, hdu, hτu, hτ0, hbr, -, -, hκr, hκr1, hℓr⟩ :=
    consensus_exponent_facts hd0 hd1 hκ h.rate_le_one h.transverse_pos hr hu hur
      hm10000 (le_refl (1 : ℝ))
  set τ₀ := (1 - p.d) * u / 8 with hτ₀_def
  set δ := min (η / 4) (τ₀ / 20) with hδ_def
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδη : δ ≤ η / 4 := min_le_left _ _
  have hδτ : δ ≤ τ₀ / 20 := min_le_right _ _
  refine ⟨δ, hδ0, ?_⟩
  have hβb0 : 0 < βb := by linarith
  -- the pruning
  have hδ₁ : 2 * δ < r + (r + u) := by linarith
  have hprune' := hprune r βb (r + u) βb hr hβb0 (by linarith) hβb0 hroom' (2 * δ) hδ₁
  -- the preparation at depth r
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < r⁻¹ + 2 := by linarith
  have hRr : (r⁻¹ + 2)⁻¹ ≤ r := by
    rw [inv_le_comm₀ (by linarith) hr]
    linarith
  have hrU' : r ≤ p.U := by
    have : 0 < 3 * m / p.κ := by positivity
    linarith
  have hprep := h.prepared (r⁻¹ + 2) hR
  -- the caps at a fine mesh
  set rm := p.κ * r + βb + m + r + u + 1 with hrm_def
  have hrm0 : 0 < rm := by rw [hrm_def]; linarith
  set Rc := rm + m + r + u + rm⁻¹ + m⁻¹ + 2 with hRc_def
  have hrminv : 0 < rm⁻¹ := inv_pos.mpr hrm0
  have hminv : 0 < m⁻¹ := inv_pos.mpr hm
  have hRc : 1 < Rc := by rw [hRc_def]; linarith
  have hRc0 : 0 < Rc := by linarith
  have hcaps := h.caps Rc hRc
  have hRcrm : Rc⁻¹ ≤ rm := by
    rw [inv_le_comm₀ hRc0 hrm0, hRc_def]
    linarith
  have hrmRc : rm ≤ Rc := by rw [hRc_def]; linarith
  have hRcm : Rc⁻¹ ≤ m := by
    rw [inv_le_comm₀ hRc0 hm, hRc_def]
    linarith
  have hmRc : m ≤ Rc := by rw [hRc_def]; linarith
  have hruRc : r + u ≤ Rc := by rw [hRc_def]; linarith
  -- eventual monomial bounds
  have e1 := agree_eventually_KH_le h 16000000 (by norm_num) 11 0 (a := m / 1000 - βb + (r + u))
    hδ0.le (by push_cast; linarith)
  have e2 := agree_eventually_KH_le h 16000000 (by norm_num) 11 0 (a := m / 1000 - m + (r + u))
    hδ0.le (by push_cast; linarith)
  have e3 := agree_eventually_KH_le h 4 (by norm_num) 1 0 (a := m - βb) hδ0.le
    (by push_cast; linarith)
  have e4 := agree_eventually_KH_le h 2 (by norm_num) 1 0 (a := p.κ * r + βb - rm) hδ0.le
    (by push_cast; rw [hrm_def]; linarith)
  have e5 := agree_eventually_KH_le h 3 (by norm_num) 2 0 (a := m - rm) hδ0.le
    (by push_cast; rw [hrm_def]; linarith)
  have e6 := agree_eventually_KH_le h 864 (by norm_num) 4 0 (a := m / 1000 - rm + (r + u)) hδ0.le
    (by push_cast; rw [hrm_def]; linarith)
  have e7 := agree_eventually_KH_le h 16 (by norm_num) 0 1 (a := -(2 * δ)) hδ0.le
    (by push_cast; linarith)
  have e8 := agree_eventually_KH_le h 10368 (by norm_num) 1 1 (a := -η) hδ0.le
    (by push_cast; linarith)
  have e9 := agree_eventually_KH_le h 300000000000 (by norm_num) 4 8 (a := -τ₀) hδ0.le
    (by push_cast; linarith)
  have e10 := agree_eventually_KH_le h 20000000000000 (by norm_num) 3 13 (a := -(3 * τ₀)) hδ0.le
    (by push_cast; linarith)
  have e11 := agree_eventually_KH_le h 600000000000 (by norm_num) 5 12
    (a := p.d * u - m + p.κ * r + p.ℓ * r) hδ0.le (by push_cast; linarith)
  have eN := h.scale_limit.eventually (eventually_gt_atTop (1 : ℝ))
  filter_upwards [hprep, hprune', hcaps, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, eN]
    with k hprepk hpr hcapk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 hN
  intro H hH2 hKH hHN s
  have hH0 : 0 ≤ H := by linarith
  have hcapk' : ∀ s' : ℝ, 0 ≤ s' → s' ≤ r + u → ∀ (q : Fin 3 → ℤ) (a v' : ℤ),
      p.μ k {ω | p.z k (p.N k) rm ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s'))⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v'} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * rm - p.d * s')) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v'} := by
    intro s' hs0 hs1 q a v'
    have hc := (hcapk rm s' m hRcrm hrmRc hs0 (by linarith) hRcm hmRc).2.2 true q a v'
    simpa using hc
  have f1 := e1 H hH0 hHN
  have f2 := e2 H hH0 hHN
  have f3 := e3 H hH0 hHN
  have f4 := e4 H hH0 hHN
  have f5 := e5 H hH0 hHN
  have f6 := e6 H hH0 hHN
  have f7 := e7 H hH0 hHN
  have f8 := e8 H hH0 hHN
  have f9 := e9 H hH0 hHN
  have f10 := e10 H hH0 hHN
  have f11 := e11 H hH0 hHN
  simp only [pow_zero, mul_one, pow_one] at f1 f2 f3 f4 f5 f6 f7 f8
  exact s.consensus_of_numerics h.basic (hprepk r hRr hrU') hN (h.subpower.1 k) hKH hr hu hm
    hd0 hd1 hℓr hdu0 hbr hβb_ge rfl hτ0 hcapk' hpr f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
