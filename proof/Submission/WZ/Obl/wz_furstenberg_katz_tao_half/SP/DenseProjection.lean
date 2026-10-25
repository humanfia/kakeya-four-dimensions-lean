-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.DenseProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PathCover
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RectangularScalarExpansion
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PopularScalarFamily

/-!
# Projection gain for dense subsets of products

`rectangular_scalar_expansion` (x0272) gives, for `σ`-Frostman sets `A`, `B` and scalars
`S`, some `t ∈ S` with `|A + t B|_δ ≥ δ ^ (-η) |A|`. Here the full product is replaced by
any `G ⊆ A × B` of density `δ ^ κ`: some `t ∈ S` has `|{a + t b : (a, b) ∈ G}|_δ ≥
δ ^ (-κ) |A|`. The graph lemma of Balog–Szemerédi–Gowers (`bsg_path_lemma`) gives
`A' × B'` whose pairs are all joined by many paths in `G`, independently of `t`, and
`path_projection_cover` transfers small projections of `G` to `A' + t B'`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- The exponent bookkeeping of `dense_rectangular_expansion`. -/
theorem dense_budget {δ κ η σ C nA nB m t a' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (_hκ : 0 < κ)
    (hκη : 100 * κ ≤ η) (hCb : C ≤ δ ^ (-κ))
    (hnA : 0 < nA) (hnB : 0 < nB) (hnAb : nA ≤ δ ^ (-σ - κ)) (hnBl : 1 ≤ nB * C * δ ^ σ)
    (hm0 : 0 ≤ m) (hm : m ≤ δ ^ (-κ) * nA) (ht : δ ^ (4 * κ) ≤ t)
    (ha' : δ ^ κ * nA / 6 ≤ a')
    (hK : 6 * 23887872 + 1 ≤ δ ^ (-(85 * κ))) :
    7776 * m ^ 3 / (δ ^ (5 * κ) * nA * nB / 3072 * t) < δ ^ (-η) * a' := by
  have hσp : 0 < δ ^ σ := Real.rpow_pos_of_pos hδ σ
  have ht0 : 0 < t := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ _) ht
  -- ratio of the two factors
  have hratio : nA ≤ δ ^ (-(2 * κ)) * nB := by
    have h1 : nA * 1 ≤ δ ^ (-σ - κ) * (nB * C * δ ^ σ) :=
      mul_le_mul hnAb hnBl zero_le_one (by positivity)
    have h2 : δ ^ (-σ - κ) * (nB * C * δ ^ σ) ≤ δ ^ (-σ - κ) * (nB * δ ^ (-κ) * δ ^ σ) := by
      gcongr
    have h3 : δ ^ (-σ - κ) * (nB * δ ^ (-κ) * δ ^ σ) = δ ^ (-(2 * κ)) * nB := by
      have e : δ ^ (-σ - κ) * δ ^ (-κ) * δ ^ σ = δ ^ (-(2 * κ)) := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1
        ring
      calc δ ^ (-σ - κ) * (nB * δ ^ (-κ) * δ ^ σ) = (δ ^ (-σ - κ) * δ ^ (-κ) * δ ^ σ) * nB := by
            ring
        _ = δ ^ (-(2 * κ)) * nB := by rw [e]
    linarith
  -- the cube of the cover size
  have hm3 : m ^ 3 ≤ δ ^ (-(3 * κ)) * nA ^ 3 := by
    have h := pow_le_pow_left₀ hm0 hm 3
    have e : (δ ^ (-κ) * nA) ^ 3 = δ ^ (-(3 * κ)) * nA ^ 3 := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 2
      push_cast
      ring
    linarith
  -- denominator
  have hden : δ ^ (9 * κ) * nA * nB / 3072 ≤ δ ^ (5 * κ) * nA * nB / 3072 * t := by
    have e : δ ^ (9 * κ) = δ ^ (5 * κ) * δ ^ (4 * κ) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [e]
    have : δ ^ (5 * κ) * δ ^ (4 * κ) * nA * nB / 3072 =
        δ ^ (5 * κ) * nA * nB / 3072 * δ ^ (4 * κ) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hden0 : 0 < δ ^ (9 * κ) * nA * nB / 3072 := by positivity
  -- left side
  have hL : 7776 * m ^ 3 / (δ ^ (5 * κ) * nA * nB / 3072 * t) ≤
      23887872 * δ ^ (-(14 * κ)) * nA := by
    calc 7776 * m ^ 3 / (δ ^ (5 * κ) * nA * nB / 3072 * t)
        ≤ 7776 * m ^ 3 / (δ ^ (9 * κ) * nA * nB / 3072) :=
          div_le_div_of_nonneg_left (by positivity) hden0 hden
      _ ≤ 7776 * (δ ^ (-(3 * κ)) * nA ^ 3) / (δ ^ (9 * κ) * nA * nB / 3072) := by
          gcongr
      _ = 23887872 * (δ ^ (-(3 * κ)) / δ ^ (9 * κ)) * nA * (nA / nB) := by
          field_simp
          ring
      _ ≤ 23887872 * (δ ^ (-(3 * κ)) / δ ^ (9 * κ)) * nA * δ ^ (-(2 * κ)) := by
          gcongr
          rw [div_le_iff₀ hnB]
          linarith
      _ = 23887872 * δ ^ (-(14 * κ)) * nA := by
          have e : δ ^ (-(3 * κ)) / δ ^ (9 * κ) * δ ^ (-(2 * κ)) = δ ^ (-(14 * κ)) := by
            rw [← Real.rpow_sub hδ, ← Real.rpow_add hδ]
            congr 1
            ring
          calc 23887872 * (δ ^ (-(3 * κ)) / δ ^ (9 * κ)) * nA * δ ^ (-(2 * κ))
              = 23887872 * (δ ^ (-(3 * κ)) / δ ^ (9 * κ) * δ ^ (-(2 * κ))) * nA := by ring
            _ = 23887872 * δ ^ (-(14 * κ)) * nA := by rw [e]
  -- right side
  have hR : δ ^ (-(99 * κ)) * nA / 6 ≤ δ ^ (-η) * a' := by
    have h1 : δ ^ (-(100 * κ)) ≤ δ ^ (-η) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h2 : δ ^ (-(100 * κ)) * (δ ^ κ * nA / 6) ≤ δ ^ (-η) * a' :=
      mul_le_mul h1 ha' (by positivity) (by positivity)
    have e : δ ^ (-(100 * κ)) * (δ ^ κ * nA / 6) = δ ^ (-(99 * κ)) * nA / 6 := by
      have e' : δ ^ (-(100 * κ)) * δ ^ κ = δ ^ (-(99 * κ)) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      calc δ ^ (-(100 * κ)) * (δ ^ κ * nA / 6) = δ ^ (-(100 * κ)) * δ ^ κ * nA / 6 := by ring
        _ = δ ^ (-(99 * κ)) * nA / 6 := by rw [e']
    linarith
  -- comparison
  have hcmp : 23887872 * δ ^ (-(14 * κ)) * nA < δ ^ (-(99 * κ)) * nA / 6 := by
    have e : δ ^ (-(99 * κ)) = δ ^ (-(85 * κ)) * δ ^ (-(14 * κ)) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [e]
    have hp : 0 < δ ^ (-(14 * κ)) * nA := by positivity
    have : 23887872 * (δ ^ (-(14 * κ)) * nA) * 6 < δ ^ (-(85 * κ)) * (δ ^ (-(14 * κ)) * nA) := by
      nlinarith
    nlinarith
  linarith

/-- **Projection gain for dense subsets of products.** For `σ`-Frostman `A`, `B`, `S`
(`1/2 ≤ σ ≤ 1 - ε`) and `G ⊆ A × B` of density `δ ^ κ`, some `t ∈ S` has
`|{a + t b : (a, b) ∈ G}|_δ ≥ δ ^ (-κ) |A|`. -/
theorem dense_rectangular_expansion (ε : ℝ) (hε : 0 < ε) :
    ∃ κ δ₀ : ℝ, 0 < κ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 2 ≤ σ → σ ≤ 1 - ε →
        1 ≤ C → C ≤ δ ^ (-κ) →
        ∀ A B S : Finset ℝ, A.Nonempty → B.Nonempty → S.Nonempty →
          (∀ s ∈ S, s ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A → RealFiniteFrostman δ C σ B →
          RealFiniteFrostman δ C σ S →
          (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') →
          (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') →
          (A.card : ℝ) ≤ δ ^ (-σ - κ) → (B.card : ℝ) ≤ δ ^ (-σ - κ) →
          ∀ G : Finset (ℝ × ℝ), G ⊆ A ×ˢ B →
            δ ^ κ * (A.card : ℝ) * (B.card : ℝ) ≤ (G.card : ℝ) →
            ∃ t ∈ S, CoverLower δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑G : Set (ℝ × ℝ)))
              (δ ^ (-κ) * (A.card : ℝ)) := by
  classical
  obtain ⟨η, δ₁, hη, hδ₁, hδ₁1, hrect⟩ := rectangular_scalar_expansion ε hε
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (η / 100) (1 / 100) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact lt_min (by positivity) (by norm_num)
  have hκη : 100 * κ ≤ η := by
    have := min_le_left (η / 100) (1 / 100)
    rw [hκdef]
    linarith
  have hκ1 : κ ≤ 1 / 100 := by rw [hκdef]; exact min_le_right _ _
  obtain ⟨d1, hd1, hd11, hc1⟩ := exists_power_bound 2 hκ
  obtain ⟨d2, hd2, hd21, hc2⟩ := exists_power_bound 6 (show 0 < η - 2 * κ by linarith)
  obtain ⟨d3, hd3, hd31, hc3⟩ :=
    exists_power_bound (6 * 23887872 + 1) (show 0 < 85 * κ by positivity)
  refine ⟨κ, min δ₁ (min d1 (min d2 d3)), hκ,
    lt_min hδ₁ (lt_min hd1 (lt_min hd2 hd3)), (min_le_left _ _).trans hδ₁1, ?_⟩
  intro δ σ C hδ hδs hσ hσmax hC hCb A B S hA hB hS hSunit hAF hBF hSF hAsep hBsep
    hAc hBc G hGAB hdense
  have hδ₁' : δ ≤ δ₁ := hδs.trans (min_le_left _ _)
  have hδd1 : δ ≤ d1 := hδs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd2 : δ ≤ d2 :=
    hδs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd3 : δ ≤ d3 :=
    hδs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ1 : δ ≤ 1 := hδ₁'.trans hδ₁1
  by_contra hnone
  push Not at hnone
  -- trim the scalars away from zero
  have hc0 : δ ≤ δ ^ (4 * κ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show 4 * κ ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have htrim : C * (δ ^ (4 * κ)) ^ σ ≤ 1 / 2 := by
    have h1 : (δ ^ (4 * κ)) ^ σ ≤ δ ^ (2 * κ) := by
      rw [← Real.rpow_mul hδ.le]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
    have h2 : C * (δ ^ (4 * κ)) ^ σ ≤ δ ^ (-κ) * δ ^ (2 * κ) :=
      mul_le_mul hCb h1 (by positivity) (by positivity)
    have h3 : δ ^ (-κ) * δ ^ (2 * κ) = δ ^ κ := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    have h4 : δ ^ κ ≤ 1 / 2 := by
      have h := hc1 δ hδ hδd1
      have hp : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
      rw [Real.rpow_neg hδ.le] at h
      rw [le_inv_comm₀ (by norm_num) hp] at h
      linarith
    linarith
  obtain ⟨S', hS'S, hS'ne, hS'low, hS'card, hS'F⟩ :=
    hSF.trim_zero hδ (by linarith) hc0 hS (fun s hs => (hSunit s hs).1) htrim
  -- the graph lemma
  have hα : (0 : ℝ) < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  obtain ⟨A', hA'A, B', hB'B, hA'card, hB'card, hpaths⟩ :=
    bsg_path_lemma A B G hGAB hA hB hα hdense
  have hnA : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hnB : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hA'pos : (0 : ℝ) < A'.card := lt_of_lt_of_le (by positivity) hA'card
  have hB'pos : (0 : ℝ) < B'.card := lt_of_lt_of_le (by positivity) hB'card
  have hA'ne : A'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA'pos)
  have hB'ne : B'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hB'pos)
  -- Frostman constants of the extracted sets
  have hC' : 6 * δ ^ (-κ) * C ≤ δ ^ (-η) := by
    have h1 : 6 * δ ^ (-κ) * C ≤ 6 * δ ^ (-κ) * δ ^ (-κ) := by gcongr
    have h2 : 6 * δ ^ (-κ) * δ ^ (-κ) = 6 * δ ^ (-(2 * κ)) := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    have h3 : 6 * δ ^ (-(2 * κ)) ≤ δ ^ (-(η - 2 * κ)) * δ ^ (-(2 * κ)) :=
      mul_le_mul_of_nonneg_right (hc2 δ hδ hδd2) (by positivity)
    have h4 : δ ^ (-(η - 2 * κ)) * δ ^ (-(2 * κ)) = δ ^ (-η) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    linarith
  have hκpos : 1 ≤ δ ^ (-κ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hC'1 : 1 ≤ 6 * δ ^ (-κ) * C := by nlinarith
  have hA'F : RealFiniteFrostman δ (6 * δ ^ (-κ) * C) σ A' := by
    have h := hAF.subset hδ (by linarith) (show 0 < δ ^ κ / 6 by positivity) hA'A
      (by linarith)
    apply RealFiniteFrostman.weaken (C := C / (δ ^ κ / 6)) h hδ
    rw [div_div_eq_mul_div, Real.rpow_neg hδ.le]
    field_simp
    rfl
  have hB'F : RealFiniteFrostman δ (6 * δ ^ (-κ) * C) σ B' := by
    have h := hBF.subset hδ (by linarith) (show 0 < δ ^ κ / 4 by positivity) hB'B
      (by linarith)
    apply RealFiniteFrostman.weaken (C := C / (δ ^ κ / 4)) h hδ
    rw [div_div_eq_mul_div, Real.rpow_neg hδ.le]
    have hp : 0 < δ ^ κ := hα
    rw [div_le_iff₀ hp]
    field_simp
    nlinarith
  have hS'F' : RealFiniteFrostman δ (6 * δ ^ (-κ) * C) σ S' := by
    apply RealFiniteFrostman.weaken (C := 2 * C) hS'F hδ
    nlinarith
  have hA'sep : ∀ a ∈ A', ∀ a' ∈ A', a ≠ a' → δ ≤ dist a a' :=
    fun a ha a' ha' hne => hAsep a (hA'A ha) a' (hA'A ha') hne
  have hB'sep : ∀ b ∈ B', ∀ b' ∈ B', b ≠ b' → δ ≤ dist b b' :=
    fun b hb b' hb' hne => hBsep b (hB'B hb) b' (hB'B hb') hne
  have hcardη (X : Finset ℝ) (hXc : (X.card : ℝ) ≤ δ ^ (-σ - κ)) :
      (X.card : ℝ) ≤ δ ^ (-σ - η) :=
    hXc.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hA'c : (A'.card : ℝ) ≤ δ ^ (-σ - η) :=
    hcardη A' ((show (A'.card : ℝ) ≤ A.card by exact_mod_cast Finset.card_le_card hA'A).trans hAc)
  have hB'c : (B'.card : ℝ) ≤ δ ^ (-σ - η) :=
    hcardη B' ((show (B'.card : ℝ) ≤ B.card by exact_mod_cast Finset.card_le_card hB'B).trans hBc)
  obtain ⟨t, htS', hlower⟩ := hrect δ σ (6 * δ ^ (-κ) * C) hδ hδ₁' hσ hσmax hC'1 hC' A' B' S'
    hA'ne hB'ne hS'ne (fun s hs => hSunit s (hS'S hs)) hA'F hB'F hS'F' hA'sep hB'sep hA'c hB'c
  -- the small projection of `G` at `t`
  have htS : t ∈ S := hS'S htS'
  have ht0 : δ ^ (4 * κ) ≤ t := hS'low t htS'
  have htpos : 0 < t := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ _) ht0
  have ht1 : t ≤ 1 := (hSunit t htS).2
  obtain ⟨m, c, hcov, hm⟩ : ∃ (m : ℕ) (c : Fin m → ℝ),
      Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑G : Set (ℝ × ℝ))) c ∧
        (m : ℝ) < δ ^ (-κ) * (A.card : ℝ) := by
    have h := hnone t htS
    unfold CoverLower at h
    push Not at h
    exact h
  have hP : 0 < δ ^ κ ^ 5 * (A.card : ℝ) * (B.card : ℝ) / 3072 := by positivity
  have hcover := path_projection_cover A B G A' B' hδ htpos ht1
    (show 0 < (δ ^ κ) ^ 5 * (A.card : ℝ) * (B.card : ℝ) / 3072 by positivity)
    hAsep hBsep hpaths c hcov
  rw [rectangular_projection_image] at hlower
  obtain ⟨n, cc, hcc, hn⟩ := hcover
  have hlow := hlower n cc hcc
  -- numeric contradiction
  have hnBl : 1 ≤ (B.card : ℝ) * C * δ ^ σ := by
    have h := hBF.grid_card_lower hδ hB
    have hle : ((B.image (realGridIndex δ)).card : ℝ) ≤ B.card := by
      exact_mod_cast Finset.card_image_le
    have : ((B.image (realGridIndex δ)).card : ℝ) * C * δ ^ σ ≤ (B.card : ℝ) * C * δ ^ σ := by
      gcongr
    linarith
  have e5 : (δ ^ κ) ^ 5 = δ ^ (5 * κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    push_cast
    ring
  rw [e5] at hn
  have hbud := dense_budget hδ hδ1 hκ hκη hCb hnA hnB hAc hnBl (Nat.cast_nonneg m) hm.le ht0
    hA'card (hc3 δ hδ hδd3)
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
