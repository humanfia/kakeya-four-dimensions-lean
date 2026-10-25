-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfEndgame
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Defs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.LineCount
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Triples

/-!
# The extraction at `s = 1/2`: final assembly

`halfExtractionSmall_of_richClass`: the rich-class step `RichClassStep` (a line `ℓ₀` through
`p₀` with unit normal `n`, and a large, separated, `1/2`-Frostman family `A` of points of `P`
near `ℓ₀`, each with many far points of `P` on strips of its bush) gives the extraction
`HalfExtractionSmall` with `A = 1000`.

Proof, with `κ = ε₀ + η`, `d₀ = r ^ (20 κ)`, `c = r ^ (900 κ)`, `τ = r ^ (-1 + 100 κ) / 4`:
* (`asm_degree_split`) the far bush neighbours of `p ∈ A` within `c` of `ℓ₀` are few
  (`HalfData.near_line_degree`), so the others, at height `≥ c` on one of the two sides of `ℓ₀`,
  number at least `2 τ`; one side `s ∈ {n, -n}` carries `τ` of them for half of the points of
  `A` (`asm_main`);
* (`asm_side`) the data along `n` transfer to `s`;
* (`asm_core`) `triple_selection` on that half gives the base pins `p₁, p₂`, the joined pins `Q`
  and the pins `H` between them;
* (`asm_config`) these form a `SP.HalfConfig` with `K = r ^ (-1000 κ)` and `c' = r ^ (1000 κ)`;
  the numerical side conditions (`asm_num_*`) are monomial comparisons, all reduced by
  `asm_absorb` to the single smallness condition `10 ^ 12 * r ^ κ ≤ 1`.

`half_core_small`: the fixed-exponent bush estimate at `s = 1/2` from `HalfExtractionSmall` and
`half_endgame`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open SP

/-- The rich-class step (to be supplied as `half_rich_class`). -/
def RichClassStep : Prop :=
  ∀ ε₀ η : ℝ, 0 < ε₀ → 0 < η → ε₀ ≤ 1 / 1000 → η ≤ 1 / 1000 →
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ → ∀ (P : Finset E2) (D : Finset (E2 × E2)),
      HalfData r ε₀ η P D →
      ∃ (p₀ n : E2) (A : Finset E2), ‖n‖ = 1 ∧ ‖p₀‖ ≤ 4 ∧ A ⊆ P ∧
        (∀ p ∈ A, |SP.acrossCoord n p₀ p| ≤ 9 * r) ∧
        (∀ p ∈ A, ∀ p' ∈ A, p ≠ p' → r ≤ |SP.alongCoord n p₀ p - SP.alongCoord n p₀ p'|) ∧
        (∀ x ρ : ℝ, r ≤ ρ → ((A.filter (fun p => |SP.alongCoord n p₀ p - x| ≤ ρ)).card : ℝ) ≤
            r ^ (-(100 * (ε₀ + η))) * ρ ^ (1 / 2 : ℝ) * (A.card : ℝ)) ∧
        r ^ (-(1 / 2) + 100 * (ε₀ + η)) ≤ (A.card : ℝ) ∧
        ∀ p ∈ A, r ^ (-1 + 100 * (ε₀ + η)) ≤
          ((P.filter (fun q => r ^ (20 * (ε₀ + η)) ≤ dist q p ∧
            ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r)).card : ℝ)

/-- `HalfExtraction` restricted to small parameters. -/
def HalfExtractionSmall : Prop :=
  ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∀ ε₀ η : ℝ, 0 < ε₀ → 0 < η → ε₀ ≤ a → η ≤ a →
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ¬ KatzTaoFurstenbergAt r (1 / 2) ε₀ η →
      ∃ (n p₀ p₁ p₂ : SP.Plane) (H Q : Finset SP.Plane) (D Qh : SP.Plane → Finset SP.Plane),
        SP.HalfConfig r (r ^ (-(A * (ε₀ + η)))) (r ^ (A * (ε₀ + η))) n p₀ p₁ p₂ H Q D Qh

/-! ### Numerics -/

/-- Absorbing a constant into a power gap at small scales. -/
lemma asm_absorb {r κ C X Y : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hCC : C ≤ 10 ^ 12) (hu : 10 ^ 12 * r ^ κ ≤ 1) (hXY : Y + κ ≤ X) : C * r ^ X ≤ r ^ Y := by
  have h1 : r ^ X = r ^ (X - Y) * r ^ Y := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have h2 : r ^ (X - Y) ≤ r ^ κ := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have h3 : 0 < r ^ Y := Real.rpow_pos_of_pos hr Y
  have h4 : 0 < r ^ (X - Y) := Real.rpow_pos_of_pos hr _
  have h5 : C * r ^ (X - Y) ≤ 1 := by
    calc C * r ^ (X - Y) ≤ 10 ^ 12 * r ^ κ := mul_le_mul hCC h2 h4.le (by norm_num)
      _ ≤ 1 := hu
  rw [h1, ← mul_assoc]
  calc C * r ^ (X - Y) * r ^ Y ≤ 1 * r ^ Y := mul_le_mul_of_nonneg_right h5 h3.le
    _ = r ^ Y := one_mul _

lemma asm_rpow_pow3 {r : ℝ} (hr : 0 < r) (a : ℝ) : (r ^ a) ^ 3 = r ^ (3 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  congr 1
  push_cast
  ring

lemma asm_rpow_cube101 {r κ : ℝ} (hr : 0 < r) : (r ^ (101 * κ)) ^ 3 = r ^ (303 * κ) := by
  rw [asm_rpow_pow3 hr]
  congr 1
  ring

lemma asm_num_near {r κ ε₀ η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hκ : 0 < κ)
    (hu : 10 ^ 12 * r ^ κ ≤ 1) (hεη : ε₀ + 8 * η ≤ 8 * κ) :
    10 ^ 9 * r ^ (-1 - ε₀ - 8 * η) * (r ^ (900 * κ) / r ^ (20 * κ)) ^ (1 / 2 : ℝ) ≤
      r ^ (-1 + 100 * κ) / 2 := by
  have e1 : r ^ (-1 - ε₀ - 8 * η) * (r ^ (900 * κ) / r ^ (20 * κ)) ^ (1 / 2 : ℝ) =
      r ^ (-1 - ε₀ - 8 * η + 440 * κ) := by
    rw [← Real.rpow_sub hr, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    congr 1
    ring
  have h2 : r ^ (-1 - ε₀ - 8 * η + 440 * κ) ≤ r ^ (-1 + 432 * κ) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have h3 := asm_absorb (C := 2 * 10 ^ 9) (X := -1 + 432 * κ) (Y := -1 + 100 * κ) hr hr1
    (by norm_num) hu (by linarith)
  rw [mul_assoc, e1]
  linarith

lemma asm_num_c {r κ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hκ1 : κ ≤ 1 / 1000)
    (hu : 10 ^ 12 * r ^ κ ≤ 1) : 64 * r ≤ r ^ (900 * κ) := by
  have h := asm_absorb (C := 64) (X := 1) (Y := 900 * κ) hr hr1 (by norm_num) hu
    (by linarith)
  rwa [Real.rpow_one] at h

lemma asm_num_big {r κ η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hκ1 : κ ≤ 1 / 1000) (hη : η ≤ κ)
    (hu : 10 ^ 12 * r ^ κ ≤ 1) :
    4 * (r ^ (-η) * (8 / r)) ≤ r ^ (-(1 / 2) + 100 * κ) / 2 * (r ^ (-1 + 100 * κ) / 4) := by
  have e1 : r ^ (-η + -1) = r ^ (-η) * r ^ (-1 : ℝ) := Real.rpow_add hr _ _
  have e2 : r ^ (-(1 / 2) + 100 * κ + (-1 + 100 * κ)) =
      r ^ (-(1 / 2) + 100 * κ) * r ^ (-1 + 100 * κ) := Real.rpow_add hr _ _
  rw [Real.rpow_neg_one] at e1
  have h := asm_absorb (C := 256) (X := -η + -1) (Y := -(1 / 2) + 100 * κ + (-1 + 100 * κ))
    hr hr1 (by norm_num) hu (by linarith)
  rw [e1, e2] at h
  have e3 : 4 * (r ^ (-η) * (8 / r)) = 32 * (r ^ (-η) * r⁻¹) := by ring
  have e4 : r ^ (-(1 / 2) + 100 * κ) / 2 * (r ^ (-1 + 100 * κ) / 4) =
      r ^ (-(1 / 2) + 100 * κ) * r ^ (-1 + 100 * κ) / 8 := by ring
  rw [e3, e4]
  linarith

lemma asm_num_theta {r κ η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : η ≤ κ) :
    r ^ (101 * κ) / 32 * (r ^ (-η) * (8 / r)) ≤ r ^ (-1 + 100 * κ) / 4 := by
  have e1 : r ^ (101 * κ + -η + -1) = r ^ (101 * κ) * r ^ (-η) * r ^ (-1 : ℝ) := by
    rw [Real.rpow_add hr, Real.rpow_add hr]
  have h2 : r ^ (101 * κ + -η + -1) ≤ r ^ (-1 + 100 * κ) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  rw [Real.rpow_neg_one] at e1
  have e3 : r ^ (101 * κ) / 32 * (r ^ (-η) * (8 / r)) = r ^ (101 * κ + -η + -1) / 4 := by
    rw [e1]; ring
  rw [e3]
  linarith

lemma asm_num_close {r κ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hκ : 0 < κ)
    (hu : 10 ^ 12 * r ^ κ ≤ 1) :
    2 * r ^ (-(100 * κ)) * (r ^ (900 * κ)) ^ (1 / 2 : ℝ) ≤ (r ^ (101 * κ) / 32) ^ 3 / 96 := by
  have e1 : r ^ (-(100 * κ)) * (r ^ (900 * κ)) ^ (1 / 2 : ℝ) = r ^ (350 * κ) := by
    rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    congr 1
    ring
  have h := asm_absorb (C := 6291456) (X := 350 * κ) (Y := 303 * κ) hr hr1 (by norm_num)
    hu (by linarith)
  have e4 : (r ^ (101 * κ) / 32) ^ 3 / 96 = r ^ (303 * κ) / 3145728 := by
    rw [div_pow, asm_rpow_cube101 hr]; ring
  rw [mul_assoc, e1, e4]
  linarith

lemma asm_num_frost {r κ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hκ : 0 < κ)
    (hu : 10 ^ 12 * r ^ κ ≤ 1) :
    2 * r ^ (-(100 * κ)) ≤ r ^ (-(1000 * κ)) * ((r ^ (101 * κ) / 32) ^ 3 / 384) := by
  have e3 : r ^ (-(1000 * κ) + 303 * κ) = r ^ (-(1000 * κ)) * r ^ (303 * κ) :=
    Real.rpow_add hr _ _
  have h := asm_absorb (C := 25165824) (X := -(100 * κ)) (Y := -(1000 * κ) + 303 * κ) hr hr1
    (by norm_num) hu (by linarith)
  have e4 : r ^ (-(1000 * κ)) * ((r ^ (101 * κ) / 32) ^ 3 / 384) =
      r ^ (-(1000 * κ) + 303 * κ) / 12582912 := by
    rw [div_pow, asm_rpow_cube101 hr, e3]; ring
  rw [e4]
  linarith

lemma asm_num_many {r κ η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hκ : 0 < κ) (hη : η ≤ κ)
    (hu : 10 ^ 12 * r ^ κ ≤ 1) :
    (r ^ (-(1000 * κ)))⁻¹ * r⁻¹ ≤ (r ^ (101 * κ) / 32) ^ 3 / 384 * r ^ (η - 1) := by
  have e1 : (r ^ (-(1000 * κ)))⁻¹ * r⁻¹ = r ^ (1000 * κ + -1) := by
    rw [Real.rpow_neg hr.le, inv_inv, Real.rpow_add hr, Real.rpow_neg_one]
  have e3 : r ^ (303 * κ + (η - 1)) = r ^ (303 * κ) * r ^ (η - 1) := Real.rpow_add hr _ _
  have e4 : (r ^ (101 * κ) / 32) ^ 3 / 384 * r ^ (η - 1) =
      r ^ (303 * κ + (η - 1)) / 12582912 := by
    rw [div_pow, asm_rpow_cube101 hr, e3]; ring
  have h := asm_absorb (C := 12582912) (X := 1000 * κ + -1) (Y := 303 * κ + (η - 1)) hr hr1
    (by norm_num) hu (by linarith)
  rw [e1, e4]
  linarith

lemma asm_num_dense {r κ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hκ : 0 < κ)
    (hu : 10 ^ 12 * r ^ κ ≤ 1) :
    (r ^ (-(1000 * κ)))⁻¹ ≤ (r ^ (101 * κ) / 32) ^ 3 / 384 := by
  have h := asm_absorb (C := 12582912) (X := 1000 * κ) (Y := 303 * κ) hr hr1
    (by norm_num) hu (by linarith)
  have e4 : (r ^ (101 * κ) / 32) ^ 3 / 384 = r ^ (303 * κ) / 12582912 := by
    rw [div_pow, asm_rpow_cube101 hr]; ring
  rw [Real.rpow_neg hr.le, inv_inv, e4]
  linarith

/-- The joined relation: `q` lies on a strip of the bush of `p`, at distance at least `d₀`
from `p`, and at height at least `c` on the side `s` of the line through `p₀`. -/
def asm_N (D : Finset (E2 × E2)) (r d₀ c : ℝ) (p₀ s p q : E2) : Prop :=
  d₀ ≤ dist q p ∧ (∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r) ∧ c ≤ inner ℝ (q - p₀) s

/-- Classical decidability of `asm_N`. -/
@[instance_reducible]
noncomputable def asm_N_dec (D : Finset (E2 × E2)) (r d₀ c : ℝ) (p₀ s p q : E2) :
    Decidable (asm_N D r d₀ c p₀ s p q) :=
  Classical.dec _

attribute [local instance] asm_N_dec

theorem asm_N_iff {D : Finset (E2 × E2)} {r d₀ c : ℝ} {p₀ s p q : E2} :
    asm_N D r d₀ c p₀ s p q ↔ d₀ ≤ dist q p ∧ (∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r) ∧
      c ≤ inner ℝ (q - p₀) s :=
  Iff.rfl

/-! ### Reversing the normal -/

theorem asm_perp_neg (v : E2) : SP.perp (-v) = -SP.perp v := by
  ext i
  fin_cases i <;> simp [SP.perp]

theorem asm_along_neg (n p₀ q : E2) : SP.alongCoord (-n) p₀ q = -SP.alongCoord n p₀ q := by
  simp only [SP.alongCoord, asm_perp_neg, inner_neg_right]

theorem asm_across_neg (n p₀ q : E2) : SP.acrossCoord (-n) p₀ q = -SP.acrossCoord n p₀ q := by
  simp only [SP.acrossCoord, inner_neg_right]

/-! ### Small facts -/

theorem asm_halfBush {r ε₀ η K : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p : E2} (hp : p ∈ P) (hKη : r ^ (-η) ≤ K) :
    SP.HalfBush r K (bushOf D p) := by
  refine ⟨fun e he => (h.D_mem _ (mem_bushOf.mp he)).2,
    fun e he e' he' hne => h.D_sep p e e' (mem_bushOf.mp he) (mem_bushOf.mp he') hne, ?_⟩
  intro u hu ρ hρ
  have h1 := h.D_kt p hp u hu ρ hρ
  have h2 : 0 ≤ (ρ / r) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (div_nonneg (h.r_pos.le.trans hρ) h.r_pos.le) _
  exact h1.trans (mul_le_mul_of_nonneg_right hKη h2)

theorem asm_nearFirst_prod {α : Type*} {x : α → ℝ} {p₁ p p₂ : α} (h : NearFirst x p₁ p p₂) :
    0 ≤ (x p - x p₁) * (x p₂ - x p) := by
  obtain ⟨h1, h2, -⟩ := h
  rcases le_total (x p₁) (x p₂) with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    exact mul_nonneg (by linarith) (by linarith)
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    nlinarith

theorem asm_nearFirst_abs {α : Type*} {x : α → ℝ} {p₁ p p₂ : α} (h : NearFirst x p₁ p p₂) :
    |x p - x p₁| ≤ |x p₂ - x p| := by
  obtain ⟨-, -, h3⟩ := h
  rwa [abs_sub_comm (x p₂) (x p)]

theorem asm_P_card_le {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hr8 : r ≤ 8) : (P.card : ℝ) ≤ r ^ (-η) * (8 / r) := by
  have h1 := h.P_kt 0 8 hr8
  have h2 : P.filter (fun p => dist p 0 ≤ 8) = P := by
    apply Finset.filter_true_of_mem
    intro p hp
    rw [dist_zero_right]
    linarith [h.P_norm p hp]
  rwa [h2] at h1

theorem asm_close_pairs {α : Type*} {A : Finset α} (x : α → ℝ) {c M : ℝ}
    (hM : ∀ a ∈ A, ((A.filter (fun b => |x b - x a| ≤ c)).card : ℝ) ≤ M) :
    (((A ×ˢ A).filter (fun ab => |x ab.1 - x ab.2| < c)).card : ℝ) ≤ A.card * M := by
  have e : ((A ×ˢ A).filter (fun ab => |x ab.1 - x ab.2| < c)).card =
      ∑ a ∈ A, (A.filter (fun b => |x a - x b| < c)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.card_filter]
  have h1 : ∀ a ∈ A, ((A.filter (fun b => |x a - x b| < c)).card : ℝ) ≤ M := by
    intro a ha
    refine le_trans ?_ (hM a ha)
    have hsub : A.filter (fun b => |x a - x b| < c) ⊆ A.filter (fun b => |x b - x a| ≤ c) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      exact ⟨hb.1, by rw [abs_sub_comm]; exact hb.2.le⟩
    exact_mod_cast Finset.card_le_card hsub
  rw [e, Nat.cast_sum]
  calc ∑ a ∈ A, ((A.filter (fun b => |x a - x b| < c)).card : ℝ) ≤ ∑ _a ∈ A, M :=
        Finset.sum_le_sum h1
    _ = A.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The configuration -/

/-- The `HalfConfig` from the output of the triple selection. -/
theorem asm_config {r ε₀ η K c c' θ B : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D)
    {s p₀ p₁ p₂ : E2} {A₁ H Q : Finset E2} {N : E2 → E2 → Prop} [∀ p q, Decidable (N p q)]
    (hs : ‖s‖ = 1) (hp₀ : ‖p₀‖ ≤ 4) (hA₁P : A₁ ⊆ P) (hp₁ : p₁ ∈ A₁) (hp₂ : p₂ ∈ A₁)
    (hQP : Q ⊆ P) (hHA : H ⊆ A₁)
    (hacross : ∀ p ∈ A₁, |SP.acrossCoord s p₀ p| ≤ 9 * r)
    (hsep : ∀ p ∈ A₁, ∀ p' ∈ A₁, p ≠ p' →
      r ≤ |SP.alongCoord s p₀ p - SP.alongCoord s p₀ p'|)
    (hfrost : ∀ x ρ : ℝ, r ≤ ρ →
      ((A₁.filter (fun p => |SP.alongCoord s p₀ p - x| ≤ ρ)).card : ℝ) ≤
        B * ρ ^ (1 / 2 : ℝ) * (A₁.card : ℝ))
    (hN : ∀ p q, N p q → (∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r) ∧
      c ≤ inner ℝ (q - p₀) s)
    (hgap : c ≤ |SP.alongCoord s p₀ p₂ - SP.alongCoord s p₀ p₁|)
    (hQN : ∀ q ∈ Q, N p₁ q ∧ N p₂ q)
    (hQcard : θ ^ 3 / 384 * (P.card : ℝ) ≤ Q.card)
    (hHcard : θ ^ 3 / 384 * (A₁.card : ℝ) ≤ H.card)
    (hH : ∀ p ∈ H, NearFirst (SP.alongCoord s p₀) p₁ p p₂ ∧
      θ ^ 3 / 384 * (Q.card : ℝ) ≤ ((Q.filter (fun q => N p q)).card : ℝ))
    (hKη : r ^ (-η) ≤ K) (hcc : c' ≤ c) (hθ : 0 < θ) (hA₁ne : A₁.Nonempty)
    (hfrostK : B ≤ K * (θ ^ 3 / 384))
    (hmany : K⁻¹ * r⁻¹ ≤ θ ^ 3 / 384 * (P.card : ℝ))
    (hdense : K⁻¹ ≤ θ ^ 3 / 384) :
    SP.HalfConfig r K c' s p₀ p₁ p₂ H Q (bushOf D) (fun p => Q.filter (fun q => N p q)) := by
  have hr := h.r_pos
  have hK : 0 < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hr _) hKη
  have hθ3 : 0 < θ ^ 3 / 384 := by positivity
  have hP : ∀ p ∈ insert p₁ (insert p₂ (H ∪ Q)), p ∈ P := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with hp | hp | hp | hp
    · rw [hp]; exact hA₁P hp₁
    · rw [hp]; exact hA₁P hp₂
    · exact hA₁P (hHA hp)
    · exact hQP hp
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- bush
    intro p hp
    exact asm_halfBush h (hP p hp) hKη
  · -- base_on_line
    exact ⟨(hacross p₁ hp₁).trans (by linarith), (hacross p₂ hp₂).trans (by linarith)⟩
  · -- base_gap
    exact hcc.trans hgap
  · -- line_pins
    intro p hp
    obtain ⟨hnf, -⟩ := hH p hp
    exact ⟨(hacross p (hHA hp)).trans (by linarith), asm_nearFirst_prod hnf,
      asm_nearFirst_abs hnf⟩
  · -- line_sep
    intro p hp p' hp' hne
    exact hsep p (hHA hp) p' (hHA hp') hne
  · -- line_frostman
    intro x ρ hρ
    have h1 : ((H.filter (fun p => |SP.alongCoord s p₀ p - x| ≤ ρ)).card : ℝ) ≤
        ((A₁.filter (fun p => |SP.alongCoord s p₀ p - x| ≤ ρ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hHA)
    have h2 := hfrost x ρ hρ
    have hρ0 : 0 ≤ ρ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (hr.le.trans hρ) _
    have hA0 : (0 : ℝ) ≤ A₁.card := Nat.cast_nonneg _
    calc ((H.filter (fun p => |SP.alongCoord s p₀ p - x| ≤ ρ)).card : ℝ)
        ≤ B * ρ ^ (1 / 2 : ℝ) * (A₁.card : ℝ) := h1.trans h2
      _ ≤ K * (θ ^ 3 / 384) * ρ ^ (1 / 2 : ℝ) * (A₁.card : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfrostK hρ0) hA0
      _ = K * ρ ^ (1 / 2 : ℝ) * (θ ^ 3 / 384 * (A₁.card : ℝ)) := by ring
      _ ≤ K * ρ ^ (1 / 2 : ℝ) * (H.card : ℝ) :=
          mul_le_mul_of_nonneg_left hHcard (mul_nonneg hK.le hρ0)
  · -- line_nonempty
    have hA₁pos : (0 : ℝ) < A₁.card := by exact_mod_cast Finset.card_pos.mpr hA₁ne
    have hHpos : (0 : ℝ) < H.card := lt_of_lt_of_le (mul_pos hθ3 hA₁pos) hHcard
    exact Finset.card_pos.mp (by exact_mod_cast hHpos)
  · -- line_bounded
    intro p hp
    have hpP : p ∈ P := by
      simp only [Finset.mem_insert] at hp
      rcases hp with hp | hp | hp
      · rw [hp]; exact hA₁P hp₁
      · rw [hp]; exact hA₁P hp₂
      · exact hA₁P (hHA hp)
    exact norm_le_eight_of_norm_le_four (h.P_norm p hpP) hp₀
  · -- pins_sep
    intro q hq q' hq' hne
    exact h.P_sep q (hQP hq) q' (hQP hq') hne
  · -- pins_bounded
    intro q hq
    exact norm_le_eight_of_norm_le_four (h.P_norm q (hQP hq)) hp₀
  · -- pins_far
    intro q hq
    exact hcc.trans (hN p₁ q (hQN q hq).1).2
  · -- pins_many
    exact hmany.trans hQcard
  · -- join₁
    intro q hq
    obtain ⟨⟨e, he, hlt⟩, -⟩ := hN p₁ q (hQN q hq).1
    exact ⟨e, he, by linarith⟩
  · -- join₂
    intro q hq
    obtain ⟨⟨e, he, hlt⟩, -⟩ := hN p₂ q (hQN q hq).2
    exact ⟨e, he, by linarith⟩
  · -- line_dense
    intro p hp
    refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
    · have h1 := (hH p hp).2
      have hQ0 : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
      calc K⁻¹ * (Q.card : ℝ) ≤ θ ^ 3 / 384 * Q.card := mul_le_mul_of_nonneg_right hdense hQ0
        _ ≤ _ := h1
    · intro q hq
      obtain ⟨-, hq'⟩ := Finset.mem_filter.mp hq
      obtain ⟨⟨e, he, hlt⟩, -⟩ := hN p q hq'
      exact ⟨e, he, by linarith⟩

/-! ### The triple selection on one side of the line -/

/-- From a rich, separated, Frostman family `A₁` on the line, each point joined to many points
on the side `s`, the `HalfConfig` with `K = r ^ (-1000 κ)` and `c = r ^ (1000 κ)`. -/
theorem asm_core {r ε₀ η κ : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hηκ : η ≤ κ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 1000)
    (hr1 : r ≤ 1) (hu : 10 ^ 12 * r ^ κ ≤ 1)
    {s p₀ : E2} {A₀ A₁ : Finset E2} {N : E2 → E2 → Prop} [∀ p q, Decidable (N p q)]
    (hs : ‖s‖ = 1) (hp₀ : ‖p₀‖ ≤ 4) (hA₁P : A₁ ⊆ P)
    (hacross : ∀ p ∈ A₁, |SP.acrossCoord s p₀ p| ≤ 9 * r)
    (hsep : ∀ p ∈ A₁, ∀ p' ∈ A₁, p ≠ p' →
      r ≤ |SP.alongCoord s p₀ p - SP.alongCoord s p₀ p'|)
    (hfrost : ∀ x ρ : ℝ, r ≤ ρ →
      ((A₁.filter (fun p => |SP.alongCoord s p₀ p - x| ≤ ρ)).card : ℝ) ≤
        r ^ (-(100 * κ)) * ρ ^ (1 / 2 : ℝ) * (A₀.card : ℝ))
    (hA₀card : r ^ (-(1 / 2) + 100 * κ) ≤ (A₀.card : ℝ))
    (hA₀A₁ : (A₀.card : ℝ) ≤ 2 * (A₁.card : ℝ))
    (hN : ∀ p q, N p q → (∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r) ∧
      r ^ (900 * κ) ≤ inner ℝ (q - p₀) s)
    (hdeg : ∀ p ∈ A₁, r ^ (-1 + 100 * κ) / 4 ≤ ((P.filter (fun q => N p q)).card : ℝ)) :
    ∃ (p₁ p₂ : E2) (H Q : Finset E2) (Qh : E2 → Finset E2),
      SP.HalfConfig r (r ^ (-(1000 * κ))) (r ^ (1000 * κ)) s p₀ p₁ p₂ H Q (bushOf D) Qh := by
  have hr := h.r_pos
  -- the size of `P`
  have hPle : (P.card : ℝ) ≤ r ^ (-η) * (8 / r) := asm_P_card_le h (by linarith)
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr h.P_ne
  -- the degree `τ`
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = r ^ (-1 + 100 * κ) / 4 := ⟨_, rfl⟩
  rw [← hτ] at hdeg
  have hτpos : 0 < τ := by rw [hτ]; positivity
  -- `A₁` is large
  have hA₀pos : (0 : ℝ) < A₀.card := lt_of_lt_of_le (Real.rpow_pos_of_pos hr _) hA₀card
  have hA₁pos : (0 : ℝ) < A₁.card := by linarith
  have hA₁ne : A₁.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA₁pos)
  -- Frostman relative to `A₁`
  have hfrost₁ : ∀ x ρ : ℝ, r ≤ ρ →
      ((A₁.filter (fun p => |SP.alongCoord s p₀ p - x| ≤ ρ)).card : ℝ) ≤
        (2 * r ^ (-(100 * κ))) * ρ ^ (1 / 2 : ℝ) * (A₁.card : ℝ) := by
    intro x ρ hρ
    have h1 := hfrost x ρ hρ
    have h2 : 0 ≤ r ^ (-(100 * κ)) * ρ ^ (1 / 2 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg (hr.le.trans hρ) _)
    calc _ ≤ _ := h1
      _ ≤ r ^ (-(100 * κ)) * ρ ^ (1 / 2 : ℝ) * (2 * (A₁.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hA₀A₁ h2
      _ = _ := by ring
  -- the separation `c`
  have hc64 : 64 * r ≤ r ^ (900 * κ) := asm_num_c hr hr1 hκ1 hu
  -- `hbig`
  have hbig : 4 * (P.card : ℝ) ≤ A₁.card * τ := by
    have h1 := asm_num_big hr hr1 hκ1 hηκ hu
    have h2 : r ^ (-(1 / 2) + 100 * κ) / 2 ≤ A₁.card := by linarith
    calc 4 * (P.card : ℝ) ≤ 4 * (r ^ (-η) * (8 / r)) := by linarith
      _ ≤ r ^ (-(1 / 2) + 100 * κ) / 2 * (r ^ (-1 + 100 * κ) / 4) := h1
      _ ≤ A₁.card * τ := by rw [hτ]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
  -- the density `θ = τ / #P`
  have hθ₀ : r ^ (101 * κ) / 32 ≤ τ / P.card := by
    rw [le_div_iff₀ hPpos]
    have h1 := asm_num_theta hr hr1 hηκ
    have h2 : 0 ≤ r ^ (101 * κ) / 32 := by positivity
    calc r ^ (101 * κ) / 32 * P.card ≤ r ^ (101 * κ) / 32 * (r ^ (-η) * (8 / r)) :=
          mul_le_mul_of_nonneg_left hPle h2
      _ ≤ r ^ (-1 + 100 * κ) / 4 := h1
      _ = τ := hτ.symm
  have hθ₀3 : (r ^ (101 * κ) / 32) ^ 3 / 384 ≤ (τ / P.card) ^ 3 / 384 := by
    have := pow_le_pow_left₀ (by positivity) hθ₀ 3
    linarith
  -- `hclose`
  have hclose : (((A₁ ×ˢ A₁).filter (fun ab => |SP.alongCoord s p₀ ab.1 -
      SP.alongCoord s p₀ ab.2| < r ^ (900 * κ))).card : ℝ) ≤
        (τ / P.card) ^ 3 / 96 * (A₁.card : ℝ) ^ 2 := by
    have h1 := asm_close_pairs (SP.alongCoord s p₀)
      (fun a _ => hfrost₁ (SP.alongCoord s p₀ a) (r ^ (900 * κ)) (by linarith))
    have h2 := asm_num_close hr hr1 hκ hu
    have h3 : (r ^ (101 * κ) / 32) ^ 3 / 96 ≤ (τ / P.card) ^ 3 / 96 := by
      have := pow_le_pow_left₀ (by positivity) hθ₀ 3
      linarith
    have hA2 : (0 : ℝ) ≤ (A₁.card : ℝ) ^ 2 := by positivity
    calc _ ≤ _ := h1
      _ = (2 * r ^ (-(100 * κ)) * (r ^ (900 * κ)) ^ (1 / 2 : ℝ)) * (A₁.card : ℝ) ^ 2 := by ring
      _ ≤ (τ / P.card) ^ 3 / 96 * (A₁.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (h2.trans h3) hA2
  -- distinct positions
  have hx : ∀ a ∈ A₁, ∀ b ∈ A₁, a ≠ b → SP.alongCoord s p₀ a ≠ SP.alongCoord s p₀ b := by
    intro a ha b hb hne heq
    have := hsep a ha b hb hne
    rw [heq, sub_self, abs_zero] at this
    linarith
  obtain ⟨p₁, hp₁, p₂, hp₂, Q, hQP, H, hHA, hgap, hQN, hQcard, hHcard, hH⟩ :=
    triple_selection A₁ P (SP.alongCoord s p₀) N hτpos hA₁ne hx hdeg hbig hclose
  -- the numerical side conditions
  have hθpos : 0 < τ / P.card := div_pos hτpos hPpos
  have hKη : r ^ (-η) ≤ r ^ (-(1000 * κ)) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hcc : r ^ (1000 * κ) ≤ r ^ (900 * κ) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hfrostK : 2 * r ^ (-(100 * κ)) ≤ r ^ (-(1000 * κ)) * ((τ / P.card) ^ 3 / 384) :=
    (asm_num_frost hr hr1 hκ hu).trans
      (mul_le_mul_of_nonneg_left hθ₀3 (Real.rpow_nonneg hr.le _))
  have hmany : (r ^ (-(1000 * κ)))⁻¹ * r⁻¹ ≤ (τ / P.card) ^ 3 / 384 * (P.card : ℝ) := by
    have h1 := asm_num_many hr hr1 hκ hηκ hu
    have h2 : 0 ≤ r ^ (η - 1) := Real.rpow_nonneg hr.le _
    have h3 : 0 ≤ (τ / P.card) ^ 3 / 384 := by positivity
    calc _ ≤ (r ^ (101 * κ) / 32) ^ 3 / 384 * r ^ (η - 1) := h1
      _ ≤ (τ / P.card) ^ 3 / 384 * r ^ (η - 1) := mul_le_mul_of_nonneg_right hθ₀3 h2
      _ ≤ (τ / P.card) ^ 3 / 384 * (P.card : ℝ) := mul_le_mul_of_nonneg_left h.P_card h3
  have hdense : (r ^ (-(1000 * κ)))⁻¹ ≤ (τ / P.card) ^ 3 / 384 :=
    (asm_num_dense hr hr1 hκ hu).trans hθ₀3
  exact ⟨p₁, p₂, H, Q, fun p => Q.filter (fun q => N p q),
    asm_config h hs hp₀ hA₁P hp₁ hp₂ hQP hHA hacross hsep hfrost₁ hN hgap hQN hQcard hHcard hH
      hKη hcc hθpos hA₁ne hfrostK hmany hdense⟩

/-! ### The side of the line -/

/-- The side `s ∈ {n, -n}`: the data along `n` transfer to `s`. -/
theorem asm_side {r ε₀ η κ : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hηκ : η ≤ κ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 1000)
    (hr1 : r ≤ 1) (hu : 10 ^ 12 * r ^ κ ≤ 1)
    {n s p₀ : E2} {A₀ A₁ : Finset E2} (hsn : s = n ∨ s = -n)
    (hn : ‖n‖ = 1) (hp₀ : ‖p₀‖ ≤ 4) (hA₀P : A₀ ⊆ P) (hA₁ : A₁ ⊆ A₀)
    (hacross : ∀ p ∈ A₀, |SP.acrossCoord n p₀ p| ≤ 9 * r)
    (hsep : ∀ p ∈ A₀, ∀ p' ∈ A₀, p ≠ p' →
      r ≤ |SP.alongCoord n p₀ p - SP.alongCoord n p₀ p'|)
    (hfrost : ∀ x ρ : ℝ, r ≤ ρ →
      ((A₀.filter (fun p => |SP.alongCoord n p₀ p - x| ≤ ρ)).card : ℝ) ≤
        r ^ (-(100 * κ)) * ρ ^ (1 / 2 : ℝ) * (A₀.card : ℝ))
    (hA₀card : r ^ (-(1 / 2) + 100 * κ) ≤ (A₀.card : ℝ))
    (hA₀A₁ : (A₀.card : ℝ) ≤ 2 * (A₁.card : ℝ))
    (hdeg : ∀ p ∈ A₁, r ^ (-1 + 100 * κ) / 4 ≤
      ((P.filter (asm_N D r (r ^ (20 * κ)) (r ^ (900 * κ)) p₀ s p)).card : ℝ)) :
    ∃ (p₁ p₂ : E2) (H Q : Finset E2) (Qh : E2 → Finset E2),
      SP.HalfConfig r (r ^ (-(1000 * κ))) (r ^ (1000 * κ)) s p₀ p₁ p₂ H Q (bushOf D) Qh := by
  have hs : ‖s‖ = 1 := by
    rcases hsn with hsn | hsn
    · rw [hsn]; exact hn
    · rw [hsn, norm_neg]; exact hn
  have hacr : ∀ q, |SP.acrossCoord s p₀ q| = |SP.acrossCoord n p₀ q| := by
    intro q
    rcases hsn with hsn | hsn
    · rw [hsn]
    · rw [hsn, asm_across_neg, abs_neg]
  have hal : ∀ q q', |SP.alongCoord s p₀ q - SP.alongCoord s p₀ q'| =
      |SP.alongCoord n p₀ q - SP.alongCoord n p₀ q'| := by
    intro q q'
    rcases hsn with hsn | hsn
    · rw [hsn]
    · rw [hsn, asm_along_neg, asm_along_neg, ← abs_neg]
      congr 1
      ring
  have hwin : ∀ x : ℝ, ∃ x' : ℝ, ∀ q,
      |SP.alongCoord s p₀ q - x| = |SP.alongCoord n p₀ q - x'| := by
    intro x
    rcases hsn with hsn | hsn
    · exact ⟨x, fun q => by rw [hsn]⟩
    · refine ⟨-x, fun q => ?_⟩
      rw [hsn, asm_along_neg, ← abs_neg]
      congr 1
      ring
  refine asm_core h hηκ hκ hκ1 hr1 hu (A₀ := A₀)
    (N := asm_N D r (r ^ (20 * κ)) (r ^ (900 * κ)) p₀ s) hs hp₀ (hA₁.trans hA₀P) ?_ ?_ ?_
    hA₀card hA₀A₁ ?_ hdeg
  · intro p hp
    rw [hacr]
    exact hacross p (hA₁ hp)
  · intro p hp p' hp' hne
    rw [hal]
    exact hsep p (hA₁ hp) p' (hA₁ hp') hne
  · intro x ρ hρ
    obtain ⟨x', hx'⟩ := hwin x
    have hsub : A₁.filter (fun p => |SP.alongCoord s p₀ p - x| ≤ ρ) ⊆
        A₀.filter (fun p => |SP.alongCoord n p₀ p - x'| ≤ ρ) := by
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨hA₁ hq.1, by rw [← hx']; exact hq.2⟩
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hfrost x' ρ hρ)
  · intro p q hpq
    obtain ⟨-, h2, h3⟩ := asm_N_iff.mp hpq
    exact ⟨h2, h3⟩

/-! ### Removing the points near the line -/

/-- The far bush neighbours of a point near the line: few of them near the line, the others
on one of the two sides. -/
theorem asm_degree_split {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hr : r ≤ 1 / 100) (hη : 0 < η) (hη1 : η ≤ 1 / 100)
    {p n p₀ : E2} (hp : p ∈ P) (hn : ‖n‖ = 1) (hpl : |inner ℝ (p - p₀) n| ≤ 64 * r)
    {c d₀ : ℝ} (hd₀ : 0 < d₀) (hc : 64 * r ≤ c) :
    ((P.filter (fun q => d₀ ≤ dist q p ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r)).card : ℝ) ≤
      10 ^ 9 * r ^ (-1 - ε₀ - 8 * η) * (c / d₀) ^ (1 / 2 : ℝ) +
        (((P.filter (asm_N D r d₀ c p₀ n p)).card : ℝ) +
          ((P.filter (asm_N D r d₀ c p₀ (-n) p)).card : ℝ)) := by
  have hr0 := h.r_pos
  have hsub : P.filter (fun q => d₀ ≤ dist q p ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r) ⊆
      P.filter (fun q => d₀ ≤ dist q p ∧ |inner ℝ (q - p₀) n| < c ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 64 * r) ∪
      (P.filter (asm_N D r d₀ c p₀ n p) ∪ P.filter (asm_N D r d₀ c p₀ (-n) p)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqP, hqd, e, he, hqe⟩ := hq
    by_cases hlt : |inner ℝ (q - p₀) n| < c
    · apply Finset.mem_union_left
      rw [Finset.mem_filter]
      exact ⟨hqP, hqd, hlt, e, he, by linarith⟩
    · apply Finset.mem_union_right
      rw [not_lt, le_abs'] at hlt
      rcases hlt with hlt | hlt
      · apply Finset.mem_union_right
        rw [Finset.mem_filter]
        refine ⟨hqP, asm_N_iff.mpr ⟨hqd, ⟨e, he, hqe⟩, ?_⟩⟩
        rw [inner_neg_right]
        linarith
      · apply Finset.mem_union_left
        rw [Finset.mem_filter]
        exact ⟨hqP, asm_N_iff.mpr ⟨hqd, ⟨e, he, hqe⟩, hlt⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (P.filter (fun q => d₀ ≤ dist q p ∧
      |inner ℝ (q - p₀) n| < c ∧ ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 64 * r))
    (P.filter (asm_N D r d₀ c p₀ n p) ∪ P.filter (asm_N D r d₀ c p₀ (-n) p))
  have h3 := Finset.card_union_le (P.filter (asm_N D r d₀ c p₀ n p))
    (P.filter (asm_N D r d₀ c p₀ (-n) p))
  have hnear := h.near_line_degree hr hη hη1 p hp n p₀ hn hpl hd₀ hc
  have h4 : ((P.filter (fun q => d₀ ≤ dist q p ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r)).card : ℝ) ≤
      ((P.filter (fun q => d₀ ≤ dist q p ∧ |inner ℝ (q - p₀) n| < c ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 64 * r)).card : ℝ) +
        (((P.filter (asm_N D r d₀ c p₀ n p)).card : ℝ) +
          ((P.filter (asm_N D r d₀ c p₀ (-n) p)).card : ℝ)) := by
    exact_mod_cast h1.trans (h2.trans (Nat.add_le_add_left h3 _))
  linarith

/-! ### The assembly -/

/-- The `HalfConfig` from the output of the rich-class step. -/
theorem asm_main {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hε₀ : 0 < ε₀) (hη : 0 < η) (hκ1 : ε₀ + η ≤ 1 / 1000)
    (hr100 : r ≤ 1 / 100) (hu : 10 ^ 12 * r ^ (ε₀ + η) ≤ 1)
    {p₀ n : E2} {A₀ : Finset E2} (hn : ‖n‖ = 1) (hp₀ : ‖p₀‖ ≤ 4) (hA₀P : A₀ ⊆ P)
    (hacross : ∀ p ∈ A₀, |SP.acrossCoord n p₀ p| ≤ 9 * r)
    (hsep : ∀ p ∈ A₀, ∀ p' ∈ A₀, p ≠ p' →
      r ≤ |SP.alongCoord n p₀ p - SP.alongCoord n p₀ p'|)
    (hfrost : ∀ x ρ : ℝ, r ≤ ρ →
      ((A₀.filter (fun p => |SP.alongCoord n p₀ p - x| ≤ ρ)).card : ℝ) ≤
        r ^ (-(100 * (ε₀ + η))) * ρ ^ (1 / 2 : ℝ) * (A₀.card : ℝ))
    (hA₀card : r ^ (-(1 / 2) + 100 * (ε₀ + η)) ≤ (A₀.card : ℝ))
    (hdeg : ∀ p ∈ A₀, r ^ (-1 + 100 * (ε₀ + η)) ≤
      ((P.filter (fun q => r ^ (20 * (ε₀ + η)) ≤ dist q p ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r)).card : ℝ)) :
    ∃ (n' p₀' p₁ p₂ : SP.Plane) (H Q : Finset SP.Plane) (D' Qh : SP.Plane → Finset SP.Plane),
      SP.HalfConfig r (r ^ (-(1000 * (ε₀ + η)))) (r ^ (1000 * (ε₀ + η))) n' p₀' p₁ p₂ H Q D'
        Qh := by
  have hr := h.r_pos
  have hr1 : r ≤ 1 := by linarith
  have hκ : 0 < ε₀ + η := by linarith
  have hηκ : η ≤ ε₀ + η := by linarith
  have hd₀ : 0 < r ^ (20 * (ε₀ + η)) := Real.rpow_pos_of_pos hr _
  have hc64 : 64 * r ≤ r ^ (900 * (ε₀ + η)) := asm_num_c hr hr1 hκ1 hu
  have hnear := asm_num_near hr hr1 hκ hu (ε₀ := ε₀) (η := η) (by linarith)
  -- every point of `A₀` has many joined points on the two sides together
  have hsplit : ∀ p ∈ A₀, r ^ (-1 + 100 * (ε₀ + η)) / 2 ≤
      ((P.filter (asm_N D r (r ^ (20 * (ε₀ + η))) (r ^ (900 * (ε₀ + η))) p₀ n p)).card : ℝ) +
        ((P.filter (asm_N D r (r ^ (20 * (ε₀ + η))) (r ^ (900 * (ε₀ + η))) p₀ (-n) p)).card :
          ℝ) := by
    intro p hp
    have hpl : |inner ℝ (p - p₀) n| ≤ 64 * r := (hacross p hp).trans (by linarith)
    have h1 := hdeg p hp
    have h2 := asm_degree_split h hr100 hη (by linarith) (hA₀P hp) hn hpl hd₀ hc64
    linarith
  -- one of the two sides carries half of `A₀`
  obtain ⟨Ap, hAp⟩ : ∃ Ap : Finset E2, Ap = A₀.filter (fun p => r ^ (-1 + 100 * (ε₀ + η)) / 4 ≤
      ((P.filter (asm_N D r (r ^ (20 * (ε₀ + η))) (r ^ (900 * (ε₀ + η))) p₀ n p)).card : ℝ)) :=
    ⟨_, rfl⟩
  obtain ⟨Am, hAm⟩ : ∃ Am : Finset E2, Am = A₀.filter (fun p => r ^ (-1 + 100 * (ε₀ + η)) / 4 ≤
      ((P.filter (asm_N D r (r ^ (20 * (ε₀ + η))) (r ^ (900 * (ε₀ + η))) p₀ (-n) p)).card :
        ℝ)) := ⟨_, rfl⟩
  have hcover : (A₀.card : ℝ) ≤ Ap.card + Am.card := by
    have hsub : A₀ ⊆ Ap ∪ Am := by
      intro p hp
      rw [Finset.mem_union, hAp, hAm, Finset.mem_filter, Finset.mem_filter]
      by_contra hcon
      push Not at hcon
      have h1 := hsplit p hp
      linarith [hcon.1 hp, hcon.2 hp]
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hApA : Ap ⊆ A₀ := by rw [hAp]; exact Finset.filter_subset _ _
  have hAmA : Am ⊆ A₀ := by rw [hAm]; exact Finset.filter_subset _ _
  rcases le_total (Am.card : ℝ) (Ap.card : ℝ) with hle | hle
  · obtain ⟨p₁, p₂, H, Q, Qh, hcfg⟩ := asm_side h hηκ hκ hκ1 hr1 hu (Or.inl rfl) hn hp₀ hA₀P
      hApA hacross hsep hfrost hA₀card (by linarith) (fun p hp => by
        rw [hAp, Finset.mem_filter] at hp
        exact hp.2)
    exact ⟨n, p₀, p₁, p₂, H, Q, bushOf D, Qh, hcfg⟩
  · obtain ⟨p₁, p₂, H, Q, Qh, hcfg⟩ := asm_side h hηκ hκ hκ1 hr1 hu (Or.inr rfl) hn hp₀ hA₀P
      hAmA hacross hsep hfrost hA₀card (by linarith) (fun p hp => by
        rw [hAm, Finset.mem_filter] at hp
        exact hp.2)
    exact ⟨-n, p₀, p₁, p₂, H, Q, bushOf D, Qh, hcfg⟩

/-! ### The extraction and the fixed-exponent estimate -/

theorem halfExtractionSmall_of_richClass (hR : RichClassStep) : HalfExtractionSmall := by
  refine ⟨1000, 1 / 2000, by norm_num, by norm_num, ?_⟩
  intro ε₀ η hε₀ hη hε₀a hηa
  obtain ⟨r₁, hr₁, hrich⟩ := hR ε₀ η hε₀ hη (by linarith) (by linarith)
  have hκ : 0 < ε₀ + η := by linarith
  obtain ⟨δ₀, hδ₀, -, hδ⟩ := SP.exists_monomial_bound (10 ^ 12) (a := ε₀ + η) (b := 0) hκ
  refine ⟨min (min r₁ (1 / 100)) δ₀, by positivity, ?_⟩
  intro r hr hrr hnot
  have hrr₁ : r ≤ r₁ := hrr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr100 : r ≤ 1 / 100 := hrr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hu : 10 ^ 12 * r ^ (ε₀ + η) ≤ 1 := by
    have := hδ r hr (hrr.trans (min_le_right _ _))
    rwa [Real.rpow_zero] at this
  obtain ⟨P, D, h⟩ := halfData_of_not hr hnot
  obtain ⟨p₀, n, A₀, hn, hp₀, hA₀P, hacross, hsep, hfrost, hA₀card, hdeg⟩ :=
    hrich r hr hrr₁ P D h
  exact asm_main h hε₀ hη (by linarith) hr100 hu hn hp₀ hA₀P hacross hsep hfrost hA₀card hdeg

theorem half_core_small (hE : HalfExtractionSmall) :
    ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → KatzTaoFurstenbergAt r (1 / 2) ε₀ η := by
  obtain ⟨A, a, hA, ha, hext⟩ := hE
  obtain ⟨κ, r₁, hκ, hr₁, hend⟩ := half_endgame
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, κ' = min κ (2 * A * a) := ⟨_, rfl⟩
  have hκ'p : 0 < κ' := by rw [hκ']; exact lt_min hκ (by positivity)
  have hκ'κ : κ' ≤ κ := by rw [hκ']; exact min_le_left _ _
  have hκ'a : κ' ≤ 2 * A * a := by rw [hκ']; exact min_le_right _ _
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = κ' / (2 * A) := ⟨_, rfl⟩
  have hε₀p : 0 < ε₀ := by rw [hε₀]; positivity
  have hε₀a : ε₀ ≤ a := by
    rw [hε₀, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨r₂, hr₂, hext'⟩ := hext ε₀ ε₀ hε₀p hε₀p hε₀a hε₀a
  refine ⟨ε₀, ε₀, min (min r₁ r₂) 1, hε₀p, hε₀p, by positivity, ?_⟩
  intro r hr hrr
  have hr1 : r ≤ 1 := hrr.trans (min_le_right _ _)
  have hrr₁ : r ≤ r₁ := hrr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrr₂ : r ≤ r₂ := hrr.trans ((min_le_left _ _).trans (min_le_right _ _))
  by_contra hfail
  obtain ⟨n, p₀, p₁, p₂, H, Q, D, Qh, hcfg⟩ := hext' r hr hrr₂ hfail
  have hAe : A * (ε₀ + ε₀) = κ' := by
    rw [hε₀]
    field_simp
    ring
  rw [hAe] at hcfg
  have hcfg' : SP.HalfConfig r (r ^ (-κ)) (r ^ κ) n p₀ p₁ p₂ H Q D Qh :=
    hcfg.mono hr.le (Real.rpow_pos_of_pos hr _)
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith))
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 hκ'κ)
  exact hend r hr hrr₁ n p₀ p₁ p₂ H Q D Qh hcfg'

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
