-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.TubeTwoEnds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/TubeTwoEnds.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.HeavyColumns
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.ColumnCodes

/-!
# Case A in one coarse tube, from two-ended classes

`tube_two_ends_false` is `coarse_tube_rounded_false` with the column hypotheses replaced by
what a uniformized configuration supplies directly:

* density `d` of the (column, class) relation of the tube;
* two-ended classes: the columns of each class in a window of length `ρ ≥ δ` are at most
  `A ρ^β` times all its columns;
* polynomial losses: `K₀, A, 1/d ≤ δ^(-η)` for the `η` the theorem provides, `ι ≤ K₀ r`.

The proof restricts to the heavy columns (`HeavyColumns`), which are `(4/d²) A`-Frostman and
`q`-spread for `q = δ^(6η/β)`, and checks the numerology of `coarse_tube_rounded_false`
(`caseA_numerics`). Here `δ = tubeTol ι Δs w`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

attribute [local instance] Classical.propDecidable

theorem le_rpow_neg_of_le_rpow {X c δ : ℝ} (hX : 0 < X) (hc : 0 < c) (hδ : 0 < δ)
    (h : δ ≤ X ^ (-(1 / c))) : X ≤ δ ^ (-c) := by
  have h1 := Real.rpow_le_rpow_of_nonpos hδ h (by linarith : -c ≤ 0)
  rw [← Real.rpow_mul hX.le] at h1
  have e : -(1 / c) * -c = 1 := by field_simp
  rw [e, Real.rpow_one] at h1
  exact h1

/-- The numerical core: all losses are powers of `Q` (for `K₀, A, 1/d`) and `P = 1/q`. -/
theorem numerics_core {b β K₀ A d Q P q Dn : ℝ} (hβ : 0 < β) (hQ : 1 ≤ Q)
    (hP : 1 ≤ P) (hq : 0 < q) (hqP : 1 / q = P)
    (hK₀1 : 1 ≤ K₀) (hK₀ : K₀ ≤ Q) (hA0 : 0 ≤ A) (hA : A ≤ Q) (hd0 : 0 < d) (hdQ : 1 / d ≤ Q)
    (hDn0 : 0 ≤ Dn) (hDn : Dn ≤ (813 * Q * P) ^ 2) :
    (4 * tubeKD (K₀ + 4 * A / d ^ 2) q b β (d / 2) Dn * (2 * (1 + 8 / q) ^ 2) ^ β) *
        2 ^ (1 + b) ≤
      (4 * 5 * 9 ^ (1 + b) * 8 ^ β * 64 * 813 ^ 2 * 8 * 162 ^ β * 2 ^ (1 + b)) *
        (Q ^ 8 * P ^ (3 + b + 2 * β)) := by
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hid : 0 < 1 / d := by positivity
  -- the factors
  have hK' : K₀ + 4 * A / d ^ 2 ≤ 5 * Q ^ 3 := by
    have e : 4 * A / d ^ 2 = 4 * A * (1 / d) ^ 2 := by field_simp
    have h1 : A * (1 / d) ^ 2 ≤ Q * Q ^ 2 :=
      mul_le_mul hA (pow_le_pow_left₀ hid.le hdQ 2) (by positivity) hQ0.le
    have h2 : Q ≤ Q ^ 3 := by
      calc Q = Q ^ 1 := (pow_one Q).symm
        _ ≤ Q ^ 3 := pow_le_pow_right₀ hQ (by norm_num)
    rw [e]
    nlinarith
  have hK'0 : 0 ≤ K₀ + 4 * A / d ^ 2 := by positivity
  have h9 : (9 / q) ^ (1 + b) = 9 ^ (1 + b) * P ^ (1 + b) := by
    rw [show 9 / q = 9 * P by rw [← hqP]; ring]
    exact Real.mul_rpow (by norm_num) hP0.le
  have hd3 : 1 / (d / 2) ^ 3 ≤ 8 * Q ^ 3 := by
    have e : 1 / (d / 2) ^ 3 = 8 * (1 / d) ^ 3 := by field_simp; norm_num
    rw [e]
    have := pow_le_pow_left₀ hid.le hdQ 3
    linarith
  have hbeta : (2 * (1 + 8 / q) ^ 2) ^ β ≤ 162 ^ β * P ^ (2 * β) := by
    have hle : 2 * (1 + 8 / q) ^ 2 ≤ 162 * P ^ (2 : ℝ) := by
      rw [show 8 / q = 8 * P by rw [← hqP]; ring, Real.rpow_two]
      nlinarith
    calc (2 * (1 + 8 / q) ^ 2) ^ β ≤ (162 * P ^ (2 : ℝ)) ^ β :=
          Real.rpow_le_rpow (by positivity) hle hβ.le
      _ = 162 ^ β * P ^ (2 * β) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hP0.le]
  have hexp : P ^ (3 + b + 2 * β) = P ^ (1 + b) * P ^ 2 * P ^ (2 * β) := by
    rw [show (3 + b + 2 * β) = (1 + b) + 2 + 2 * β by ring, Real.rpow_add hP0,
      Real.rpow_add hP0, Real.rpow_two]
  -- assemble
  unfold tubeKD
  have hrw : (4 * ((K₀ + 4 * A / d ^ 2) * (9 / q) ^ (1 + b) * 8 ^ β * 64 * Dn / (d / 2) ^ 3) *
      (2 * (1 + 8 / q) ^ 2) ^ β) * 2 ^ (1 + b) =
      4 * (K₀ + 4 * A / d ^ 2) * (9 / q) ^ (1 + b) * 8 ^ β * 64 * Dn * (1 / (d / 2) ^ 3) *
        (2 * (1 + 8 / q) ^ 2) ^ β * 2 ^ (1 + b) := by ring
  rw [hrw, h9, hexp]
  have h8 : (0 : ℝ) ≤ 8 ^ β := by positivity
  have h2b : (0 : ℝ) ≤ 2 ^ (1 + b) := by positivity
  have h9b : (0 : ℝ) ≤ 9 ^ (1 + b) * P ^ (1 + b) := by positivity
  calc 4 * (K₀ + 4 * A / d ^ 2) * (9 ^ (1 + b) * P ^ (1 + b)) * 8 ^ β * 64 * Dn *
        (1 / (d / 2) ^ 3) * (2 * (1 + 8 / q) ^ 2) ^ β * 2 ^ (1 + b)
      ≤ 4 * (5 * Q ^ 3) * (9 ^ (1 + b) * P ^ (1 + b)) * 8 ^ β * 64 * (813 * Q * P) ^ 2 *
        (8 * Q ^ 3) * (162 ^ β * P ^ (2 * β)) * 2 ^ (1 + b) := by
        gcongr
    _ = (4 * 5 * 9 ^ (1 + b) * 8 ^ β * 64 * 813 ^ 2 * 8 * 162 ^ β * 2 ^ (1 + b)) *
        (Q ^ 8 * (P ^ (1 + b) * P ^ 2 * P ^ (2 * β))) := by ring


theorem sq_813_aux {x : ℝ} (hx : 1 ≤ x) : (810 * x + 2) ^ 2 + 1 ≤ (813 * x) ^ 2 := by
  nlinarith

theorem caseA_numerics {b β ζ : ℝ} (hb : 0 < b) (hβ : 0 < β) (hζ : 0 < ζ) :
    ∃ η δ₁ : ℝ, 0 < η ∧ 0 < δ₁ ∧ δ₁ ≤ 1 / 2 ∧ 6 * η / β ≤ 1 / 2 ∧
    ∀ δ K₀ A d ι r Δs : ℝ, 0 < δ → δ ≤ δ₁ → 1 ≤ K₀ → K₀ ≤ δ ^ (-η) → 0 ≤ A → A ≤ δ ^ (-η) →
      δ ^ η ≤ d → 0 < r → ι ≤ K₀ * r → 0 < Δs → δ ≤ 9 / 8 * ι / Δs →
      (4 * tubeKD (K₀ + 4 * A / d ^ 2) (δ ^ (6 * η / β)) b β (d / 2)
          (⌈(18 * δ / (δ ^ (6 * η / β) * (r / (10 * (4 * Δs)))) + 2) ^ 2⌉₊ : ℝ) *
          (2 * (1 + 8 / δ ^ (6 * η / β)) ^ 2) ^ β) * 2 ^ (1 + b) ≤ δ ^ (-ζ) ∧
      4 ≤ δ ^ (-(ζ / 2)) ∧ 256 * A * (δ ^ (6 * η / β)) ^ β ≤ d ^ 4 ∧ δ ≤ δ ^ (6 * η / β) ∧
      δ ^ (6 * η / β) ≤ 1 := by
  set κ : ℝ := 8 + 6 * (3 + b + 2 * β) / β with hκ
  have hκpos : 0 < κ := by positivity
  set C : ℝ := 4 * 5 * 9 ^ (1 + b) * 8 ^ β * 64 * 813 ^ 2 * 8 * 162 ^ β * 2 ^ (1 + b) with hC
  have hCpos : 0 < C := by positivity
  set η : ℝ := min (ζ / (2 * κ)) (β / 12) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hηκ : η * κ ≤ ζ / 2 := by
    have h1 : η ≤ ζ / (2 * κ) := min_le_left _ _
    calc η * κ ≤ ζ / (2 * κ) * κ := mul_le_mul_of_nonneg_right h1 hκpos.le
      _ = ζ / 2 := by field_simp
  have hθ : 6 * η / β ≤ 1 / 2 := by
    have h1 : η ≤ β / 12 := min_le_right _ _
    rw [div_le_iff₀ hβ]; linarith
  have hθ0 : 0 ≤ 6 * η / β := by positivity
  set δ₁ : ℝ := min (1 / 2) (min (C ^ (-(1 / (ζ / 2))))
    (min ((256 : ℝ) ^ (-(1 / η))) ((4 : ℝ) ^ (-(1 / (ζ / 2)))))) with hδ₁
  have hδ₁pos : 0 < δ₁ := by
    refine lt_min (by norm_num) (lt_min (Real.rpow_pos_of_pos hCpos _)
      (lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)))
  refine ⟨η, δ₁, hηpos, hδ₁pos, min_le_left _ _, hθ, ?_⟩
  intro δ K₀ A d ι r Δs hδ hδδ₁ hK₀1 hK₀ hA0 hA hdlo hr hιr hΔs hδι
  have hδ1 : δ ≤ 1 := by linarith [min_le_left (1 / 2 : ℝ) (min (C ^ (-(1 / (ζ / 2))))
    (min ((256 : ℝ) ^ (-(1 / η))) ((4 : ℝ) ^ (-(1 / (ζ / 2))))))]
  have hδC : δ ≤ C ^ (-(1 / (ζ / 2))) :=
    hδδ₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ256 : δ ≤ (256 : ℝ) ^ (-(1 / η)) :=
    hδδ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ4 : δ ≤ (4 : ℝ) ^ (-(1 / (ζ / 2))) :=
    hδδ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hCδ : C ≤ δ ^ (-(ζ / 2)) := le_rpow_neg_of_le_rpow hCpos (by positivity) hδ hδC
  have h256 : 256 ≤ δ ^ (-η) := le_rpow_neg_of_le_rpow (by norm_num) hηpos hδ hδ256
  have h4 : 4 ≤ δ ^ (-(ζ / 2)) := le_rpow_neg_of_le_rpow (by norm_num) (by positivity) hδ hδ4
  set θ : ℝ := 6 * η / β with hθdef
  set q : ℝ := δ ^ θ with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hδ _
  have hq1 : q ≤ 1 := Real.rpow_le_one hδ.le hδ1 hθ0
  have hδq : δ ≤ q := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show θ ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  set Q : ℝ := δ ^ (-η) with hQ
  set P : ℝ := δ ^ (-θ) with hP
  have hQ1 : 1 ≤ Q := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hP1 : 1 ≤ P := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hqP : 1 / q = P := by rw [hq, hP, Real.rpow_neg hδ.le, one_div]
  have hd0 : 0 < d := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ _) hdlo
  have hdQ : 1 / d ≤ Q := by
    rw [hQ, Real.rpow_neg hδ.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hδ _) hdlo
  have hDn : (⌈(18 * δ / (q * (r / (10 * (4 * Δs)))) + 2) ^ 2⌉₊ : ℝ) ≤ (813 * Q * P) ^ 2 := by
    have hx : 18 * δ / (q * (r / (10 * (4 * Δs)))) ≤ 810 * Q * P := by
      have e : 18 * δ / (q * (r / (10 * (4 * Δs)))) = 720 * (δ * Δs) * (1 / q) / r := by
        field_simp; ring
      rw [e, hqP]
      have h1 : δ * Δs ≤ 9 / 8 * ι := by
        rw [le_div_iff₀ hΔs] at hδι; linarith
      have h2 : 720 * (δ * Δs) * P ≤ 810 * K₀ * r * P := by
        have : 720 * (δ * Δs) ≤ 810 * K₀ * r := by nlinarith
        exact mul_le_mul_of_nonneg_right this (by linarith)
      rw [div_le_iff₀ hr]
      have h3 : 810 * K₀ * r * P ≤ 810 * Q * P * r := by
        have := mul_le_mul_of_nonneg_right hK₀ (show 0 ≤ 810 * r * P by positivity)
        linarith
      linarith
    have hx0 : 0 ≤ 18 * δ / (q * (r / (10 * (4 * Δs)))) := by positivity
    have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (18 * δ / (q * (r / (10 * (4 * Δs)))) + 2) ^ 2
      by positivity)
    have hQP : 1 ≤ Q * P := one_le_mul_of_one_le_of_one_le hQ1 hP1
    have hsq : (18 * δ / (q * (r / (10 * (4 * Δs)))) + 2) ^ 2 ≤ (810 * Q * P + 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h813 := sq_813_aux hQP
    have e1 : 810 * Q * P = 810 * (Q * P) := by ring
    have e2 : 813 * Q * P = 813 * (Q * P) := by ring
    rw [e1] at hsq; rw [e2]
    linarith
  have hcore := numerics_core (b := b) (β := β) (K₀ := K₀) (A := A) (d := d) hβ hQ1 hP1 hq0 hqP
    hK₀1 hK₀ hA0 hA hd0 hdQ (by positivity) hDn
  have hpow : Q ^ 8 * P ^ (3 + b + 2 * β) = δ ^ (-(η * κ)) := by
    rw [hQ, hP, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le,
      ← Real.rpow_add hδ]
    congr 1
    rw [hκ, hθdef]; field_simp; ring
  have hmono : δ ^ (-(η * κ)) ≤ δ ^ (-(ζ / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  refine ⟨?_, h4, ?_, hδq, hq1⟩
  · calc _ ≤ C * (Q ^ 8 * P ^ (3 + b + 2 * β)) := hcore
      _ ≤ δ ^ (-(ζ / 2)) * δ ^ (-(ζ / 2)) := by
          rw [hpow]
          exact mul_le_mul hCδ hmono (Real.rpow_pos_of_pos hδ _).le (Real.rpow_pos_of_pos hδ _).le
      _ = δ ^ (-ζ) := by rw [← Real.rpow_add hδ]; ring_nf
  · have hqb : q ^ β = δ ^ (6 * η) := by
      rw [hq, ← Real.rpow_mul hδ.le, hθdef]; congr 1; field_simp
    rw [hqb]
    have hd4 : δ ^ (4 * η) ≤ d ^ 4 := by
      rw [show 4 * η = η * (4 : ℕ) by push_cast; ring, Real.rpow_mul hδ.le, Real.rpow_natCast]
      exact pow_le_pow_left₀ (Real.rpow_pos_of_pos hδ _).le hdlo 4
    have hsplit : δ ^ (6 * η) = δ ^ η * δ ^ η * δ ^ (4 * η) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
    have hAη : A * δ ^ η ≤ 1 := by
      have : A * δ ^ η ≤ δ ^ (-η) * δ ^ η :=
        mul_le_mul_of_nonneg_right hA (Real.rpow_pos_of_pos hδ _).le
      rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero] at this
      exact this
    have h256η : 256 * δ ^ η ≤ 1 := by
      have : 256 * δ ^ η ≤ δ ^ (-η) * δ ^ η :=
        mul_le_mul_of_nonneg_right h256 (Real.rpow_pos_of_pos hδ _).le
      rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero] at this
      exact this
    rw [hsplit]
    have hp1 : 0 ≤ δ ^ η := (Real.rpow_pos_of_pos hδ _).le
    have hp4 : 0 ≤ δ ^ (4 * η) := (Real.rpow_pos_of_pos hδ _).le
    calc 256 * A * (δ ^ η * δ ^ η * δ ^ (4 * η))
        = (A * δ ^ η) * (256 * δ ^ η) * δ ^ (4 * η) := by ring
      _ ≤ 1 * 1 * δ ^ (4 * η) := by gcongr
      _ = δ ^ (4 * η) := by ring
      _ ≤ d ^ 4 := hd4


theorem tubeTol_pos {ι Δs w : ℝ} (hι : 0 < ι) (hΔs : 0 < Δs) (hw : 0 < w) :
    0 < tubeTol ι Δs w := by
  unfold tubeTol; positivity

theorem tubeTol_le {ι Δs w : ℝ} (hΔs : 0 < Δs) (hwι : 4 * Δs * w ≤ 2 * ι) :
    tubeTol ι Δs w ≤ 9 / 8 * ι / Δs := by
  unfold tubeTol
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hΔs]
  have := mul_le_mul_of_nonneg_left hwι (le_of_lt (mul_pos hΔs hΔs))
  nlinarith

/-- **Case A in one coarse tube, from two-ended classes.** -/
theorem tube_two_ends_false {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (v : Plane) (cT aT r ι Δs w M d K₀ A : ℝ), ‖v‖ = 1 → 0 < r → 0 < ι → 0 < Δs → 0 < w →
      0 < M → 1 ≤ K₀ → 0 ≤ A → 4 * Δs * w ≤ 2 * ι → ι ≤ K₀ * r →
      tubeTol ι Δs w ≤ δ₀ →
      K₀ ≤ (tubeTol ι Δs w) ^ (-η) → A ≤ (tubeTol ι Δs w) ^ (-η) →
      (tubeTol ι Δs w) ^ η ≤ d → d ≤ 1 →
      ∀ (J : Finset (Plane × Plane)) (U : Finset Plane) (pin : Plane × Plane → Plane → Prop),
      J.Nonempty → U.Nonempty →
      (8 * (J.card : ℝ) / M ≤ (tubeTol ι Δs w) ^ (-(1 - e))) →
      (∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)| ∧
        |(lineChart v j).1| ≤ Δs) →
      (∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep r j j') →
      (∀ j ∈ J, ∀ x ∈ U, pin j x → |inner ℝ (x - j.1) j.2| ≤ ι) →
      (∀ x ∈ U, ‖x‖ ≤ 4) →
      (∀ x ∈ U, M ≤ ((J.filter (fun j => pin j x)).card : ℝ)) →
      (∀ j ∈ J, ∀ y ∈ U.image (tubeCol v w),
        |lineHeight (tubeLine v cT aT (4 * Δs) j) y| ≤ 7 / 2) →
      d * ((U.image (tubeCol v w)).card : ℝ) * J.card ≤
        ((((U.image (tubeCol v w)) ×ˢ J).filter
          (fun p : ℝ × (Plane × Plane) => ∃ x ∈ U, pin p.2 x ∧ tubeCol v w x = p.1)).card : ℝ) →
      (∀ j ∈ J, ∀ z ρ : ℝ, tubeTol ι Δs w ≤ ρ →
        (((U.image (tubeCol v w)).filter (fun y => (∃ x ∈ U, pin j x ∧ tubeCol v w x = y) ∧
          |y - z| ≤ ρ)).card : ℝ) ≤
          A * ρ ^ β * (((U.image (tubeCol v w)).filter
            (fun y => ∃ x ∈ U, pin j x ∧ tubeCol v w x = y)).card : ℝ)) →
      (∀ c a ρ : ℝ, tubeTol ι Δs w ≤ ρ →
        ((J.filter (fun j => |(tubeLine v cT aT (4 * Δs) j).1 - c| ≤ ρ ∧
          |(tubeLine v cT aT (4 * Δs) j).2 - a| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ (1 + b) * J.card) →
      64 * (J.card : ℝ) ≤ K₀ * M ^ 2 → False := by
  obtain ⟨ζ, δ₀', hζ, hδ₀', hδ₀'2, hmain⟩ := coarse_tube_rounded_false he hb hβ
  obtain ⟨η, δ₁, hη, hδ₁, hδ₁2, hθ, hnum⟩ := caseA_numerics hb hβ hζ
  refine ⟨η, min δ₀' δ₁, hη, lt_min hδ₀' hδ₁, (min_le_left _ _).trans hδ₀'2, ?_⟩
  intro v cT aT r ι Δs w M d K₀ A hv hr hι hΔs hw hM hK₀ hA0 hwι hιr hδ hK₀δ hAδ hdδ hd1
    J U pin hJ hU hF hJnorm hsep hpin hU4 hdeg hheight hdens htwo hline hquad
  have hδpos : 0 < tubeTol ι Δs w := tubeTol_pos hι hΔs hw
  obtain ⟨hN, h4, hspread, hδq, hq1⟩ := hnum (tubeTol ι Δs w) K₀ A d ι r Δs hδpos
    (hδ.trans (min_le_right _ _)) hK₀ hK₀δ hA0 hAδ hdδ hr hιr hΔs (tubeTol_le hΔs hwι)
  set δ := tubeTol ι Δs w with hδdef
  set q := δ ^ (6 * η / β) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hδpos _
  have hd0 : 0 < d := lt_of_lt_of_le (Real.rpow_pos_of_pos hδpos _) hdδ
  set I := U.image (tubeCol v w) with hI
  set R : ℝ → Plane × Plane → Prop := fun y j => ∃ x ∈ U, pin j x ∧ tubeCol v w x = y with hR
  set H := heavyCols I J R d with hH
  set U' := U.filter (fun x => tubeCol v w x ∈ H) with hU'
  have hHI : H ⊆ I := Finset.filter_subset _ _
  have hU'img : U'.image (tubeCol v w) = H := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (hHI hy)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxy ▸ hy⟩, hxy⟩
  have hHcard := card_heavy_ge (d := d) I J R hJ (by convert hdens)
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast (hU.image _).card_pos
  have hHpos : (0 : ℝ) < H.card := by
    have : 0 < d / 2 * (I.card : ℝ) := by positivity
    linarith
  have hHne : H.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hHpos
  have hU'ne : U'.Nonempty := by
    rw [← hU'img] at hHne
    exact Finset.image_nonempty.mp hHne
  have hfrost : ∀ z ρ : ℝ, δ ≤ ρ →
      ((H.filter (fun y => |y - z| ≤ ρ)).card : ℝ) ≤ 4 / d ^ 2 * A * ρ ^ β * H.card := by
    intro z ρ hρ
    have key := heavy_frostman (β := β) (ρ₀ := δ) (κ := (I.card : ℝ)) I J R hd0 hJ hA0 (Nat.cast_nonneg _)
      le_rfl (by convert hdens) ?_ z ρ hρ (hδpos.le.trans hρ)
    · convert key
    · intro j hj z' ρ' hρ'
      have h := htwo j hj z' ρ' hρ'
      have hρ0 : 0 ≤ ρ' := hδpos.le.trans hρ'
      have h2 : A * ρ' ^ β * (((U.image (tubeCol v w)).filter
            (fun y => ∃ x ∈ U, pin j x ∧ tubeCol v w x = y)).card : ℝ) ≤ A * ρ' ^ β * I.card := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA0 (Real.rpow_nonneg hρ0 _))
        exact_mod_cast Finset.card_filter_le _ _
      have h3 := h.trans h2
      refine le_trans (le_of_eq ?_) h3
      congr 2
      ext y
      simp only [Finset.mem_filter]
      exact Iff.rfl
  set K₀' := K₀ + 4 * A / d ^ 2 with hK₀'
  have hK₀K₀' : K₀ ≤ K₀' := by
    have : 0 ≤ 4 * A / d ^ 2 := by positivity
    linarith
  apply hmain v cT aT r ι Δs w M q (d / 2) K₀' hv hr hι hΔs hw hM hq0 hq1 (by positivity)
    (by linarith) (hK₀.trans hK₀K₀') hwι (hδ.trans (min_le_left _ _)) J U' pin hJ hU'ne hF hN h4
    hJnorm hsep
  · intro j hj x hx hjx
    exact hpin j hj x (Finset.mem_filter.mp hx).1 hjx
  · intro x hx
    exact hU4 x (Finset.mem_filter.mp hx).1
  · intro x hx
    exact hdeg x (Finset.mem_filter.mp hx).1
  · intro j hj y hy
    rw [hU'img] at hy
    exact hheight j hj y (hHI hy)
  · rw [hU'img]
    have h := heavy_density I J R hd0
    refine h.trans (le_of_eq ?_)
    congr 2
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, x, hx, hpx, hxy⟩
      exact ⟨⟨hp1, hp2⟩, x, Finset.mem_filter.mpr ⟨hx, hxy ▸ hp1⟩, hpx, hxy⟩
    · rintro ⟨⟨hp1, hp2⟩, x, hx, hpx, hxy⟩
      exact ⟨⟨hp1, hp2⟩, x, (Finset.mem_filter.mp hx).1, hpx, hxy⟩
  · intro y hy
    rw [hU'img] at hy ⊢
    have h1 : ((H.filter (fun y' => |y - y'| < q)).card : ℝ) ≤
        ((H.filter (fun y' => |y' - y| ≤ q)).card : ℝ) := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro y' hy'
      obtain ⟨hy'H, hlt⟩ := Finset.mem_filter.mp hy'
      exact Finset.mem_filter.mpr ⟨hy'H, by rw [abs_sub_comm]; exact hlt.le⟩
    refine h1.trans ((hfrost y q hδq).trans ?_)
    have hc : 4 / d ^ 2 * A * q ^ β ≤ (d / 2) ^ 2 / 16 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
  · intro z ρ hρ
    rw [hU'img]
    refine (hfrost z ρ hρ).trans ?_
    have hρ0 : 0 ≤ ρ := hδpos.le.trans hρ
    have h1 : 4 / d ^ 2 * A ≤ K₀' := by
      rw [hK₀']
      have : 4 / d ^ 2 * A = 4 * A / d ^ 2 := by ring
      linarith
    have hpow : 0 ≤ ρ ^ β := Real.rpow_nonneg hρ0 _
    calc 4 / d ^ 2 * A * ρ ^ β * (H.card : ℝ) = (4 / d ^ 2 * A) * (ρ ^ β * H.card) := by ring
      _ ≤ K₀' * (ρ ^ β * H.card) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = K₀' * ρ ^ β * H.card := by ring
  · intro c a ρ hρ
    refine (hline c a ρ hρ).trans ?_
    have hρ0 : 0 ≤ ρ := hδpos.le.trans hρ
    have : 0 ≤ ρ ^ (1 + b) * (J.card : ℝ) := by positivity
    calc K₀ * ρ ^ (1 + b) * (J.card : ℝ) = K₀ * (ρ ^ (1 + b) * J.card) := by ring
      _ ≤ K₀' * (ρ ^ (1 + b) * J.card) := mul_le_mul_of_nonneg_right hK₀K₀' this
      _ = K₀' * ρ ^ (1 + b) * J.card := by ring
  · have := mul_le_mul_of_nonneg_right hK₀K₀' (sq_nonneg M)
    linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
