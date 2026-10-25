-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.ConfigLeaf.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/ConfigLeaf.lean (b19b589).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Config

/-!
# The configuration leaf: assembly

`configLeaf`: `ConfigLeaf s` for `0 < s < 1` (see `High/Config.lean` for the steps). Given
`κ`, the regularization exponent is `ε = κ`, and the internal exponent is
`δ = min (κ / 100) (1 / 100)`; `η, ε₀ ≤ δ`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

attribute [local instance] cfgY.decEq

noncomputable section

theorem palScale_pos' {r : ℝ} (hr : 0 < r) (n j : ℕ) : 0 < palScale r n j :=
  Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hr _) _

theorem eight_le_rpow_neg {r δ : ℝ} (hr : 0 < r) (h : r ^ δ ≤ 1 / 8) : 8 ≤ r ^ (-δ) := by
  rw [Real.rpow_neg hr.le]
  have hpos : 0 < r ^ δ := Real.rpow_pos_of_pos hr _
  rw [le_inv_comm₀ (by norm_num) hpos]
  linarith

/-- The arithmetic of the bad-label bound: `4 · weight ≤ |S₁|²`. -/
theorem bad_arith {r δ η ε₀ s A S1 N K₀ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : η ≤ δ)
    (hε₀ : ε₀ ≤ δ) (hA : 0 ≤ A) (hK₀ : 0 ≤ K₀) (hN0 : 0 ≤ N)
    (hS1 : r ^ δ * r ^ (2 * η - 1 - s) ≤ S1) (hN : N ≤ r ^ (-(2 * s) - ε₀))
    (hlog : 4 * A * K₀ ≤ r ^ (-(13 * δ))) :
    4 * (K₀ * (A * r ^ (-2 - 4 * η)) / r ^ (-(25 * δ)) * (r ^ (-δ) * N)) ≤ S1 * S1 := by
  have hS1' : 0 ≤ r ^ δ * r ^ (2 * η - 1 - s) := by positivity
  have hRHS : r ^ (2 * δ + 4 * η - 2 - 2 * s) ≤ S1 * S1 := by
    have e : r ^ (2 * δ + 4 * η - 2 - 2 * s) =
        (r ^ δ * r ^ (2 * η - 1 - s)) * (r ^ δ * r ^ (2 * η - 1 - s)) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr]; ring_nf
    rw [e]
    exact mul_le_mul hS1 hS1 hS1' (hS1'.trans hS1)
  have e1 : 4 * (K₀ * (A * r ^ (-2 - 4 * η)) / r ^ (-(25 * δ)) * (r ^ (-δ) * N)) =
      (4 * A * K₀) * r ^ (-2 - 4 * η + 24 * δ) * N := by
    have h1 : r ^ (-2 - 4 * η + 24 * δ) = r ^ (-2 - 4 * η) / r ^ (-(25 * δ)) * r ^ (-δ) := by
      rw [← Real.rpow_sub hr, ← Real.rpow_add hr]; ring_nf
    rw [h1]; ring
  have hpow0 : 0 ≤ r ^ (-2 - 4 * η + 24 * δ) := (Real.rpow_pos_of_pos hr _).le
  have h2 : (4 * A * K₀) * r ^ (-2 - 4 * η + 24 * δ) * N ≤
      r ^ (-(13 * δ)) * r ^ (-2 - 4 * η + 24 * δ) * r ^ (-(2 * s) - ε₀) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hlog hpow0) hN hN0
    exact mul_nonneg (Real.rpow_pos_of_pos hr _).le hpow0
  have e2 : r ^ (-(13 * δ)) * r ^ (-2 - 4 * η + 24 * δ) * r ^ (-(2 * s) - ε₀) =
      r ^ (-2 - 4 * η + 11 * δ - 2 * s - ε₀) := by
    rw [← Real.rpow_add hr, ← Real.rpow_add hr]; ring_nf
  have h3 : r ^ (-2 - 4 * η + 11 * δ - 2 * s - ε₀) ≤ r ^ (2 * δ + 4 * η - 2 - 2 * s) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  rw [e1]
  linarith

/-- The pruned family is again a failed configuration, with `η₂ = 5 η + 4 δ`. -/
theorem kept_failData {r s ε₀ η δ : ℝ} {S₁ Bad : Finset (E2 × E2)}
    (hfail₁ : FailData r s ε₀ (3 * η + 2 * δ) (S₁.image Prod.fst) S₁)
    (hr1 : r ≤ 1) (hs1 : s ≤ 1) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hrδ : r ^ δ ≤ 1 / 8)
    (hS₁lb : r ^ δ * r ^ (2 * η - 1 - s) ≤ (S₁.card : ℝ))
    (hS₂card : (S₁.card : ℝ) ≤ 4 * (keptLabels S₁ Bad).card)
    (hne : (keptLabels S₁ Bad).Nonempty) :
    FailData r s ε₀ (5 * η + 4 * δ) ((keptLabels S₁ Bad).image Prod.fst)
      (keptLabels S₁ Bad) := by
  have hr := hfail₁.r_pos
  have hS₂S₁ : keptLabels S₁ Bad ⊆ S₁ := keptLabels_subset S₁ Bad
  apply FailData.prune hfail₁ hS₂S₁ hne (by linarith) hr1
  · -- the pin count
    have hM : ∀ p ∈ (keptLabels S₁ Bad).image Prod.fst,
        ((bushOf (keptLabels S₁ Bad) p).card : ℝ) ≤ 2 * r ^ (-(3 * η + 2 * δ) - s) := by
      intro p hp
      have hp1 : p ∈ S₁.image Prod.fst := Finset.image_subset_image hS₂S₁ hp
      have h1 : bushOf (keptLabels S₁ Bad) p ⊆ bushOf S₁ p := by
        intro e he; exact mem_bushOf.mpr (hS₂S₁ (mem_bushOf.mp he))
      have h2 := hfail₁.bush_le (by linarith) hp1
      have h4 : (2 : ℝ) ^ s ≤ 2 := by
        rcases le_or_gt 0 s with hs0 | hs0
        · calc (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
            _ = 2 := Real.rpow_one 2
        · have : (2 : ℝ) ^ s ≤ 2 ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hs0.le
          rw [Real.rpow_zero] at this; linarith
      have h3 : r ^ (-(3 * η + 2 * δ)) * (2 / r) ^ s ≤ 2 * r ^ (-(3 * η + 2 * δ) - s) := by
        have e : r ^ (-(3 * η + 2 * δ)) * (2 / r) ^ s =
            (2 : ℝ) ^ s * r ^ (-(3 * η + 2 * δ) - s) := by
          rw [Real.div_rpow (by norm_num) hr.le, Real.rpow_sub hr]
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_right h4 (Real.rpow_pos_of_pos hr _).le
      calc ((bushOf (keptLabels S₁ Bad) p).card : ℝ) ≤ (bushOf S₁ p).card := by
            exact_mod_cast Finset.card_le_card h1
        _ ≤ r ^ (-(3 * η + 2 * δ)) * (2 / r) ^ s := h2
        _ ≤ 2 * r ^ (-(3 * η + 2 * δ) - s) := h3
    have hsum : ((keptLabels S₁ Bad).card : ℝ) ≤
        (((keptLabels S₁ Bad).image Prod.fst).card : ℝ) * (2 * r ^ (-(3 * η + 2 * δ) - s)) := by
      rw [card_eq_sum_bushOf (fun q hq => Finset.mem_image_of_mem Prod.fst hq)]
      calc ∑ p ∈ (keptLabels S₁ Bad).image Prod.fst, ((bushOf (keptLabels S₁ Bad) p).card : ℝ)
          ≤ ∑ _p ∈ (keptLabels S₁ Bad).image Prod.fst, 2 * r ^ (-(3 * η + 2 * δ) - s) :=
            Finset.sum_le_sum hM
        _ = (((keptLabels S₁ Bad).image Prod.fst).card : ℝ) *
              (2 * r ^ (-(3 * η + 2 * δ) - s)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have e1 : r ^ (5 * η + 4 * δ - 1) * r ^ (-(3 * η + 2 * δ) - s) =
        r ^ δ * (r ^ δ * r ^ (2 * η - 1 - s)) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr]; ring_nf
    have hpos : 0 < r ^ (-(3 * η + 2 * δ) - s) := Real.rpow_pos_of_pos hr _
    have hX0 : 0 ≤ r ^ δ * r ^ (2 * η - 1 - s) := by positivity
    have h1 : r ^ (5 * η + 4 * δ - 1) * r ^ (-(3 * η + 2 * δ) - s) ≤
        (((keptLabels S₁ Bad).image Prod.fst).card : ℝ) * r ^ (-(3 * η + 2 * δ) - s) := by
      rw [e1]
      have h2 : r ^ δ * (r ^ δ * r ^ (2 * η - 1 - s)) ≤ 1 / 8 * (r ^ δ * r ^ (2 * η - 1 - s)) :=
        mul_le_mul_of_nonneg_right hrδ hX0
      linarith
    exact le_of_mul_le_mul_right h1 hpos
  · -- the bushes
    intro p hp
    have h1 := kept_bush hp
    have hp1 : p ∈ S₁.image Prod.fst := Finset.image_subset_image hS₂S₁ hp
    have h2 := hfail₁.D_card p hp1
    have h3 : r ^ (5 * η + 4 * δ - s) = r ^ (3 * η + 2 * δ - s) * r ^ (2 * η + 2 * δ) := by
      rw [← Real.rpow_add hr]; ring_nf
    have h4 : r ^ (2 * η + 2 * δ) ≤ r ^ δ :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
    have h5 : 0 ≤ r ^ (3 * η + 2 * δ - s) := (Real.rpow_pos_of_pos hr _).le
    have h6 : r ^ (3 * η + 2 * δ - s) * r ^ (2 * η + 2 * δ) ≤ r ^ (3 * η + 2 * δ - s) * (1 / 8) :=
      mul_le_mul_of_nonneg_left (h4.trans hrδ) h5
    rw [h3]
    linarith

/-- The mass of the final family. -/
theorem config_mass {r δ κ D1 S1 S2 S3 : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hδκ : 100 * δ ≤ κ)
    (hδ : 0 < δ) (hrδ : r ^ δ ≤ 1 / 8) (hD0 : 0 ≤ D1) (h1 : r ^ δ * D1 ≤ S1)
    (h2 : S1 ≤ 4 * S2) (h3 : r ^ δ * S2 ≤ S3) : r ^ κ * D1 ≤ S3 := by
  have hpos : 0 ≤ r ^ δ := (Real.rpow_pos_of_pos hr _).le
  have e : r ^ κ = r ^ δ * r ^ δ * r ^ (κ - 2 * δ) := by
    rw [← Real.rpow_add hr, ← Real.rpow_add hr]; ring_nf
  have h4 : r ^ (κ - 2 * δ) ≤ r ^ δ := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have h5 : r ^ κ ≤ r ^ δ * r ^ δ / 4 := by
    rw [e]
    have h6 : r ^ δ * r ^ δ * r ^ (κ - 2 * δ) ≤ r ^ δ * r ^ δ * (1 / 8) :=
      mul_le_mul_of_nonneg_left (h4.trans hrδ) (by positivity)
    have h7 : 0 ≤ r ^ δ * r ^ δ := by positivity
    linarith
  calc r ^ κ * D1 ≤ r ^ δ * r ^ δ / 4 * D1 := mul_le_mul_of_nonneg_right h5 hD0
    _ = r ^ δ * (r ^ δ * D1) / 4 := by ring
    _ ≤ r ^ δ * S1 / 4 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left h1 hpos
    _ ≤ r ^ δ * (4 * S2) / 4 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left h2 hpos
    _ = r ^ δ * S2 := by ring
    _ ≤ S3 := h3

/-- The line-Frostman constant. -/
theorem config_const {r δ κ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hδκ : 100 * δ ≤ κ) (hδ : 0 < δ)
    (h8δ : 8 ≤ r ^ (-δ)) :
    2 * r ^ (-(25 * δ)) * r ^ (-δ) * (4 * r ^ (-δ)) * r ^ (-δ) ≤ r ^ (-κ) := by
  have e : 2 * r ^ (-(25 * δ)) * r ^ (-δ) * (4 * r ^ (-δ)) * r ^ (-δ) =
      8 * r ^ (-(28 * δ)) := by
    have e' : r ^ (-(28 * δ)) = r ^ (-(25 * δ)) * r ^ (-δ) * r ^ (-δ) * r ^ (-δ) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr]; ring_nf
    rw [e']; ring
  have e2 : r ^ (-κ) = r ^ (-(28 * δ)) * r ^ (-(κ - 28 * δ)) := by
    rw [← Real.rpow_add hr]; ring_nf
  have h1 : r ^ (-δ) ≤ r ^ (-(κ - 28 * δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have h2 : 0 ≤ r ^ (-(28 * δ)) := (Real.rpow_pos_of_pos hr _).le
  rw [e, e2]
  have h3 : r ^ (-(28 * δ)) * 8 ≤ r ^ (-(28 * δ)) * r ^ (-(κ - 28 * δ)) :=
    mul_le_mul_of_nonneg_left (h8δ.trans h1) h2
  linarith

/-- **The configuration leaf.** -/
theorem configLeaf {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : ConfigLeaf s := by
  intro κ hκ
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (κ / 100) (1 / 100) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) (by norm_num)
  have hδκ : 100 * δ ≤ κ := by
    have : δ ≤ κ / 100 := by rw [hδ]; exact min_le_left _ _
    linarith
  have hδ1 : δ ≤ 1 / 100 := by rw [hδ]; exact min_le_right _ _
  refine ⟨κ, hκ, le_rfl, δ, hδ0, ?_⟩
  intro n _
  obtain ⟨rA, hrA, _, hregA⟩ := FailData.regularize s δ hs0.le hs1.le hδ0 1
  obtain ⟨rB, hrB, _, hregB⟩ :=
    FailData.regularize s δ hs0.le hs1.le hδ0 (12 * (n + 1) * (n + 1) * (n + 1))
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) := ⟨_, rfl⟩
  have hq : (1 / 2 : ℝ) ^ (1 - s) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hA0 : 0 < A := by rw [hA]; apply div_pos (by norm_num); linarith
  obtain ⟨rL, hrL, hlog⟩ := ceil_logb_le (C := 4 * A) (δ := 13 * δ) (by positivity)
    (by positivity) (by linarith)
  obtain ⟨r8, hr8, h8⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := δ) (B := 1 / 8) hδ0 (by norm_num)
  refine ⟨min (min (min rA rB) (min rL r8)) (1 / 100),
    lt_min (lt_min (lt_min hrA hrB) (lt_min hrL hr8)) (by norm_num), ?_⟩
  intro r ε₀ η P D hr hrr hε₀ hε₀δ hη hηδ h
  have hrA' : r ≤ rA := hrr.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hrB' : r ≤ rB := hrr.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hrL' : r ≤ rL := hrr.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hr8' : r ≤ r8 := hrr.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hr100 : r ≤ 1 / 100 := hrr.trans (min_le_right _ _)
  have hr1 : r ≤ 1 := by linarith
  have hrδ : r ^ δ ≤ 1 / 8 := h8 r hr hr8'
  have h8δ : 8 ≤ r ^ (-δ) := eight_le_rpow_neg hr hrδ
  have hlogr := hlog r hr hrL'
  -- lines and tubes
  obtain ⟨J₀, cls, hJD, hJsep, hcls, hgeo⟩ := lines_exist h
  have hJ4 : ∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4 := fun ℓ hℓ => h.P_norm _ (h.D_mem ℓ (hJD hℓ)).1
  have htubes : ∀ j : ℕ, ∃ (J₁ : Finset (E2 × E2)) (tb : E2 × E2 → E2 × E2), J₁ ⊆ J₀ ∧
      (∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep (palScale r n j) x y) ∧
      (∀ ℓ ∈ J₀, tb ℓ ∈ J₁) ∧
      (∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tb ℓ).1) (tb ℓ).2| < 9 * palScale r n j ∧
        (dist ℓ.2 (tb ℓ).2 < palScale r n j ∨ dist ℓ.2 (-(tb ℓ).2) < palScale r n j)) :=
    fun j => exists_coarse_tubes J₀ hJ4 (palScale_pos' hr n j)
  choose J₁ tb hJ₁sub hJ₁sep htbmem htbgeo using htubes
  -- first regularization: balanced classes
  obtain ⟨S₁, hS₁D, hmass₁, hfail₁, _, hbal₁⟩ := hregA r ε₀ η hrA' hη.le (by linarith) P D h
    (I := Unit) (Y := fun _ => E2 × E2) (by simp) (fun _ => cls)
  have hcls₁ : Balanced S₁ cls (r ^ (-δ)) := hbal₁ ()
  have hK0 : 0 < r ^ (-δ) := Real.rpow_pos_of_pos hr _
  -- the bad labels are at most a quarter
  obtain ⟨K₀, hK₀def⟩ : ∃ K₀ : ℕ, K₀ = ⌈Real.logb 2 (8 / r)⌉₊ := ⟨_, rfl⟩
  have hK₀ : Real.logb 2 (8 / r) ≤ K₀ := by rw [hK₀def]; exact Nat.le_ceil _
  rw [← hK₀def] at hlogr
  have hBt0 : 0 < r ^ (-(25 * δ)) := Real.rpow_pos_of_pos hr _
  have hBadsub : badLabels S₁ cls r s (r ^ (-(25 * δ))) K₀ ⊆ S₁ := Finset.filter_subset _ _
  have hbadc := badLabels_card h hs0.le hs1 hr100 hη hgeo hS₁D hcls₁ hK0.le hBt0 K₀
  rw [← hA] at hbadc
  have hD := fcls_card_D_ge h
  have hS₁lb : r ^ δ * r ^ (2 * η - 1 - s) ≤ (S₁.card : ℝ) :=
    (mul_le_mul_of_nonneg_left hD (Real.rpow_pos_of_pos hr _).le).trans hmass₁
  have hN : ((S₁.image cls).card : ℝ) ≤ r ^ (-(2 * s) - ε₀) := by
    have h1 : S₁.image cls ⊆ J₀ := by
      intro ℓ hℓ
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
      exact hcls q (hS₁D hq)
    have h2 := h.few_lines J₀ hJD hJsep
    have h3 : ((S₁.image cls).card : ℝ) ≤ J₀.card := by exact_mod_cast Finset.card_le_card h1
    linarith
  have hfour := bad_arith hr hr1 hηδ hε₀δ hA0.le (by positivity : (0 : ℝ) ≤ (K₀ : ℝ) + 1)
    (Nat.cast_nonneg _) hS₁lb hN hlogr
  have hS₁ne : S₁.Nonempty := by
    obtain ⟨p, hp⟩ := hfail₁.P_ne
    obtain ⟨q, hq, _⟩ := Finset.mem_image.mp hp
    exact ⟨q, hq⟩
  have hS₁pos : (0 : ℝ) < S₁.card := by exact_mod_cast hS₁ne.card_pos
  have hBad4 : 4 * ((badLabels S₁ cls r s (r ^ (-(25 * δ))) K₀).card : ℝ) ≤ S₁.card := by
    have h1 : 4 * ((badLabels S₁ cls r s (r ^ (-(25 * δ))) K₀).card : ℝ) * S₁.card ≤
        S₁.card * S₁.card := by linarith
    exact le_of_mul_le_mul_right h1 hS₁pos
  -- pruning
  set Bad := badLabels S₁ cls r s (r ^ (-(25 * δ))) K₀ with hBad
  set S₂ := keptLabels S₁ Bad with hS₂
  have hS₂S₁ : S₂ ⊆ S₁ := keptLabels_subset S₁ Bad
  have hS₂card : (S₁.card : ℝ) ≤ 4 * S₂.card := by
    have := prune_card S₁ Bad hBadsub
    linarith
  have hS₂ne : S₂.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S₂.card := by linarith
    exact_mod_cast this
  have hfail₂ : FailData r s ε₀ (5 * η + 4 * δ) (S₂.image Prod.fst) S₂ :=
    kept_failData hfail₁ hr1 hs1.le hη.le hδ0.le hrδ hS₁lb hS₂card hS₂ne
  -- second regularization: every palette map
  obtain ⟨S₃, hS₃S₂, hmass₃, hfail₃, hfst₃, hbal₃⟩ := hregB r ε₀ (5 * η + 4 * δ) hrB'
    (by positivity) (by linarith) _ _ hfail₂
    (I := Fin 12 × Fin (n + 1) × Fin (n + 1) × Fin (n + 1))
    (Y := cfgY n) (le_of_eq (by simp only [Fintype.card_prod, Fintype.card_fin]; ring))
    (cfgMaps r n cls tb)
  have hS₃S₁ : S₃ ⊆ S₁ := hS₃S₂.trans hS₂S₁
  have hS₃D : S₃ ⊆ D := hS₃S₁.trans hS₁D
  have hKκ : r ^ (-δ) ≤ r ^ (-κ) := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hcls₃ : Balanced S₃ cls (r ^ (-δ)) := hbal₃ (0, 0, 0, 0)
  -- sizes
  have hS₃lb : r ^ δ * (S₂.card : ℝ) ≤ S₃.card := hmass₃
  have hsize : (S₁.card : ℝ) ≤ 4 * r ^ (-δ) * S₃.card := by
    have h1 : r ^ (-δ) * r ^ δ = 1 := by rw [← Real.rpow_add hr]; simp
    have h2 : (S₂.card : ℝ) ≤ r ^ (-δ) * S₃.card := by
      calc (S₂.card : ℝ) = r ^ (-δ) * (r ^ δ * S₂.card) := by rw [← mul_assoc, h1, one_mul]
        _ ≤ r ^ (-δ) * S₃.card := mul_le_mul_of_nonneg_left hS₃lb hK0.le
    linarith
  refine ⟨S₃, J₀, cls, J₁, tb, ?_⟩
  exact {
    fail := h.mono_eta (by linarith) hr1
    sub := hS₃D
    mass := config_mass hr hr1 hδκ hδ0 hrδ (Nat.cast_nonneg _) hmass₁ hS₂card hS₃lb
    failS := hfail₃.mono_eta (by linarith) hr1
    lines_sub := hJD
    lines_sep := hJsep
    cls_mem := hcls
    cls_geo := hgeo
    line_frostman := by
      intro q hq c hc
      have hq2 : q ∈ S₂ := hS₃S₂ hq
      have hq1 : q ∈ S₁ := hS₂S₁ hq2
      have hnb : q ∉ Bad := not_mem_bad_of_kept hq2
      have hgood : ∀ k ≤ K₀, ((nearClass S₁ cls q (r * 2 ^ k)).card : ℝ) ≤
          r ^ (-(25 * δ)) * (r * 2 ^ k) ^ (1 - s) * (classSize S₁ cls q : ℝ) := by
        intro k hk
        by_contra hlt
        push Not at hlt
        exact hnb (Finset.mem_filter.mpr ⟨hq1, k, hk, hlt⟩)
      have hconst := config_const hr hr1 hδκ hδ0 h8δ
      have hκ1 : 1 ≤ r ^ (-κ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
      exact near_le_of_good hr hs0.le hs1.le hS₃S₁ hq hgood hK₀ (classSize_mul_le hcls₁ hq1)
        (card_le_balanced hcls₃ hq) hsize hBt0.le (by positivity) hK0.le hK0.le hconst hκ1 hc
    tubes_sub := hJ₁sub
    tubes_sep := fun j _ => hJ₁sep j
    tube_mem := fun j _ => htbmem j
    tube_geo := fun j _ => htbgeo j
    bal_pin := Balanced.mono hfst₃ hKκ
    bal_cls := Balanced.mono hcls₃ hKκ
    bal_cell := fun i hi => Balanced.mono (hbal₃ (1, ⟨i, Nat.lt_succ_of_le hi⟩, 0, 0)) hKκ
    bal_arc := fun j hj => Balanced.mono (hbal₃ (2, 0, ⟨j, Nat.lt_succ_of_le hj⟩, 0)) hKκ
    bal_tube := fun j hj => Balanced.mono (hbal₃ (3, 0, ⟨j, Nat.lt_succ_of_le hj⟩, 0)) hKκ
    bal_pin_arc := fun j hj => Balanced.mono (hbal₃ (4, 0, ⟨j, Nat.lt_succ_of_le hj⟩, 0)) hKκ
    bal_pin_tube := fun j hj => Balanced.mono (hbal₃ (5, 0, ⟨j, Nat.lt_succ_of_le hj⟩, 0)) hKκ
    bal_cell_cls := fun i hi => Balanced.mono (hbal₃ (6, ⟨i, Nat.lt_succ_of_le hi⟩, 0, 0)) hKκ
    bal_cell_arc := fun i hi j hj =>
      Balanced.mono (hbal₃ (7, ⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩, 0)) hKκ
    bal_cell_tube := fun i hi j hj =>
      Balanced.mono (hbal₃ (8, ⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩, 0)) hKκ
    bal_tube2 := fun h hh a ha =>
      Balanced.mono (hbal₃ (9, ⟨h, Nat.lt_succ_of_le hh⟩, ⟨a, Nat.lt_succ_of_le ha⟩, 0)) hKκ
    bal_pin_tube2 := fun h hh a ha =>
      Balanced.mono (hbal₃ (10, ⟨h, Nat.lt_succ_of_le hh⟩, ⟨a, Nat.lt_succ_of_le ha⟩, 0)) hKκ
    bal_cell_tube2 := fun i hi h hh a ha =>
      Balanced.mono (hbal₃ (11, ⟨h, Nat.lt_succ_of_le hh⟩, ⟨a, Nat.lt_succ_of_le ha⟩,
        ⟨i, Nat.lt_succ_of_le hi⟩)) hKκ }

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
