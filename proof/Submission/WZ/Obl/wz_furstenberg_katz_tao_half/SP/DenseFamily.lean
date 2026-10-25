-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.DenseFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.DenseProjection
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ProjectionTransfer
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PopularOverlap

/-!
# Projection gain for families of dense subsets of products

The dense set may depend on the scalar: if for every `t ∈ S` some `G t ⊆ A × B` of density
`δ ^ κ` has a small projection `{a + t b : (a, b) ∈ G t}`, we get a contradiction with
`rectangular_scalar_expansion`. For each `t` the graph lemma gives a product `A_t × B_t`
with a small projection (`path_projection_cover`); a popular `t₀` overlaps many of them
(`popular_overlap`), and Ruzsa's inequality moves the small projections onto the single
product `A_{t₀} × B_{t₀}` (`projection_transfer`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

theorem factor_ratio_budget {δ κ σ C nA nB : ℝ} (hδ : 0 < δ) (hCb : C ≤ δ ^ (-κ))
    (_hnA : 0 < nA) (hnB : 0 < nB) (hnAb : nA ≤ δ ^ (-σ - κ)) (hnBl : 1 ≤ nB * C * δ ^ σ) :
    nA ≤ δ ^ (-(2 * κ)) * nB := by
  have hσp : 0 < δ ^ σ := Real.rpow_pos_of_pos hδ σ
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

theorem path_cover_budget {δ κ nA nB m t : ℝ} (hδ : 0 < δ)
    (_hnA : 0 < nA) (hnB : 0 < nB) (hratio : nA ≤ δ ^ (-(2 * κ)) * nB)
    (hm0 : 0 ≤ m) (hm : m ≤ δ ^ (-κ) * nA) (ht : δ ^ (4 * κ) ≤ t) :
    7776 * m ^ 3 / (δ ^ (5 * κ) * nA * nB / 3072 * t) ≤ 23887872 * δ ^ (-(14 * κ)) * nA := by
  have hm3 : m ^ 3 ≤ δ ^ (-(3 * κ)) * nA ^ 3 := by
    have h := pow_le_pow_left₀ hm0 hm 3
    have e : (δ ^ (-κ) * nA) ^ 3 = δ ^ (-(3 * κ)) * nA ^ 3 := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 2
      push_cast
      ring
    linarith
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

/-- The constant of `transfer_budget`. -/
noncomputable def transferConst : ℝ := 241864704 * 23887872 ^ 5 * 1327104 * 24

theorem transferConst_pos : 0 < transferConst := by unfold transferConst; positivity

theorem transfer_budget {δ κ nA nB a0 b0 : ℝ} (hδ : 0 < δ)
    (hnA : 0 < nA) (hnB : 0 < nB) (hratio : nA ≤ δ ^ (-(2 * κ)) * nB)
    (ha0 : δ ^ κ * nA / 6 ≤ a0) (hb0 : δ ^ κ * nB / 4 ≤ b0) :
    241864704 * (23887872 * δ ^ (-(14 * κ)) * nA) ^ 5 /
      ((δ ^ (4 * κ)) ^ 4 * ((δ ^ (2 * κ) / 24) ^ 2 * nA / 2) *
        ((δ ^ (2 * κ) / 24) ^ 2 * nB / 2) * a0 * b0) ≤
      transferConst * δ ^ (-(100 * κ)) * nA := by
  have hD : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  -- rewrite all powers in terms of `D = δ ^ κ`
  have e14 : δ ^ (-(14 * κ)) = ((δ ^ κ) ^ 14)⁻¹ := by
    rw [Real.rpow_neg hδ.le, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 2
    push_cast
    ring
  have e4 : δ ^ (4 * κ) = (δ ^ κ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    push_cast
    ring
  have e2 : δ ^ (2 * κ) = (δ ^ κ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    push_cast
    ring
  have em2 : δ ^ (-(2 * κ)) = ((δ ^ κ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hδ.le, e2]
  have e100 : δ ^ (-(100 * κ)) = ((δ ^ κ) ^ 100)⁻¹ := by
    rw [Real.rpow_neg hδ.le, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 2
    push_cast
    ring
  rw [e14, e4, e2, e100]
  rw [em2] at hratio
  set D := δ ^ κ with hDdef
  have hD1 : 0 < D := hD
  -- lower bounds for the denominator factors
  have ha0' : 0 < a0 := lt_of_lt_of_le (by positivity) ha0
  have hb0' : 0 < b0 := lt_of_lt_of_le (by positivity) hb0
  have hnB' : D ^ 2 * nA ≤ nB := by
    have h := mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ D ^ 2)
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h
    linarith
  have hden : (D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2) *
        (D * nA / 6) * (D * nB / 4) ≤
      (D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2) * a0 * b0 := by
    have hp : 0 ≤ (D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2) := by
      positivity
    have h1 := mul_le_mul ha0 hb0 (by positivity) ha0'.le
    calc (D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2) *
          (D * nA / 6) * (D * nB / 4)
        = ((D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2)) *
          ((D * nA / 6) * (D * nB / 4)) := by ring
      _ ≤ ((D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2)) *
          (a0 * b0) := mul_le_mul_of_nonneg_left h1 hp
      _ = _ := by ring
  have hden0 : 0 < (D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2) *
      (D * nA / 6) * (D * nB / 4) := by positivity
  calc 241864704 * (23887872 * (D ^ 14)⁻¹ * nA) ^ 5 /
        ((D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2) * a0 * b0)
      ≤ 241864704 * (23887872 * (D ^ 14)⁻¹ * nA) ^ 5 /
        ((D ^ 4) ^ 4 * ((D ^ 2 / 24) ^ 2 * nA / 2) * ((D ^ 2 / 24) ^ 2 * nB / 2) *
          (D * nA / 6) * (D * nB / 4)) :=
        div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ = transferConst * (D ^ 96)⁻¹ * nA * (nA / nB) ^ 2 := by
        unfold transferConst
        field_simp
        ring
    _ ≤ transferConst * (D ^ 96)⁻¹ * nA * ((D ^ 2)⁻¹) ^ 2 := by
        have hq : nA / nB ≤ (D ^ 2)⁻¹ := by
          rw [div_le_iff₀ hnB]
          calc nA = (D ^ 2)⁻¹ * (D ^ 2 * nA) := by field_simp
            _ ≤ (D ^ 2)⁻¹ * nB := mul_le_mul_of_nonneg_left hnB' (by positivity)
        have hq0 : 0 ≤ nA / nB := by positivity
        have := pow_le_pow_left₀ hq0 hq 2
        have hc : 0 ≤ transferConst * (D ^ 96)⁻¹ * nA := by
          have := transferConst_pos
          positivity
        exact mul_le_mul_of_nonneg_left this hc
    _ = transferConst * (D ^ 100)⁻¹ * nA := by
        field_simp

theorem family_final_budget {δ κ nA : ℝ} (hδ : 0 < δ) (hnA : 0 < nA)
    (hK : 6 * transferConst + 1 ≤ δ ^ (-(99 * κ))) :
    transferConst * δ ^ (-(100 * κ)) * nA < δ ^ (-(199 * κ)) * nA / 6 := by
  have e : δ ^ (-(199 * κ)) = δ ^ (-(99 * κ)) * δ ^ (-(100 * κ)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [e]
  have hp : 0 < δ ^ (-(100 * κ)) * nA := mul_pos (Real.rpow_pos_of_pos hδ _) hnA
  have hT := transferConst_pos
  have h1 : transferConst * 6 < δ ^ (-(99 * κ)) := by linarith
  have h2 := mul_lt_mul_of_pos_right h1 hp
  have e2 : δ ^ (-(99 * κ)) * δ ^ (-(100 * κ)) * nA / 6 =
      δ ^ (-(99 * κ)) * (δ ^ (-(100 * κ)) * nA) / 6 := by ring
  rw [e2, lt_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
  calc transferConst * δ ^ (-(100 * κ)) * nA * 6 =
      transferConst * 6 * (δ ^ (-(100 * κ)) * nA) := by ring
    _ < _ := h2

set_option maxHeartbeats 1000000 in
/-- **Projection gain for families of dense subsets of products.** If for every `t ∈ S` the
set `G t ⊆ A × B` has density `δ ^ κ`, then some `t ∈ S` has
`|{a + t b : (a, b) ∈ G t}|_δ ≥ δ ^ (-κ) |A|`. -/
theorem dense_family_expansion (ε : ℝ) (hε : 0 < ε) :
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
          ∀ G : ℝ → Finset (ℝ × ℝ), (∀ t ∈ S, G t ⊆ A ×ˢ B) →
            (∀ t ∈ S, δ ^ κ * (A.card : ℝ) * (B.card : ℝ) ≤ ((G t).card : ℝ)) →
            ∃ t ∈ S, CoverLower δ
              ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(G t) : Set (ℝ × ℝ)))
              (δ ^ (-κ) * (A.card : ℝ)) := by
  classical
  obtain ⟨η, δ₁, hη, hδ₁, hδ₁1, hrect⟩ := rectangular_scalar_expansion ε hε
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (η / 200) (1 / 100) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact lt_min (by positivity) (by norm_num)
  have hκη : 200 * κ ≤ η := by
    have := min_le_left (η / 200) (1 / 100)
    rw [hκdef]
    linarith
  have hκ1 : κ ≤ 1 / 100 := by rw [hκdef]; exact min_le_right _ _
  obtain ⟨d1, hd1, hd11, hc1⟩ := exists_power_bound 2 hκ
  obtain ⟨d2, hd2, hd21, hc2⟩ := exists_power_bound 2304 (show 0 < η - 5 * κ by linarith)
  obtain ⟨d3, hd3, hd31, hc3⟩ :=
    exists_power_bound (6 * transferConst + 1) (show 0 < 99 * κ by positivity)
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
  have hα : (0 : ℝ) < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  have hnA : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hnB : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hnBl : 1 ≤ (B.card : ℝ) * C * δ ^ σ := by
    have h := hBF.grid_card_lower hδ hB
    have hle : ((B.image (realGridIndex δ)).card : ℝ) ≤ B.card := by
      exact_mod_cast Finset.card_image_le
    have : ((B.image (realGridIndex δ)).card : ℝ) * C * δ ^ σ ≤ (B.card : ℝ) * C * δ ^ σ := by
      gcongr
    linarith
  have hratio := factor_ratio_budget hδ hCb hnA hnB hAc hnBl
  -- for every scalar, a product with a small projection
  have hdata : ∀ t ∈ S', ∃ At ⊆ A, ∃ Bt ⊆ B, δ ^ κ * (A.card : ℝ) / 6 ≤ (At.card : ℝ) ∧
      δ ^ κ * (B.card : ℝ) / 4 ≤ (Bt.card : ℝ) ∧
      RealCoverBound δ (At + realScalarImage t Bt) (23887872 * δ ^ (-(14 * κ)) * A.card) := by
    intro t ht
    have htS : t ∈ S := hS'S ht
    have ht0 : δ ^ (4 * κ) ≤ t := hS'low t ht
    have htpos : 0 < t := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ _) ht0
    have ht1 : t ≤ 1 := (hSunit t htS).2
    obtain ⟨A', hA'A, B', hB'B, hA'c, hB'c, hpaths⟩ :=
      bsg_path_lemma A B (G t) (hGAB t htS) hA hB hα (hdense t htS)
    obtain ⟨m, c, hcov, hm⟩ : ∃ (m : ℕ) (c : Fin m → ℝ),
        Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(G t) : Set (ℝ × ℝ))) c ∧
          (m : ℝ) < δ ^ (-κ) * (A.card : ℝ) := by
      have h := hnone t htS
      unfold CoverLower at h
      push Not at h
      exact h
    have hcover := path_projection_cover A B (G t) A' B' hδ htpos ht1
      (show 0 < (δ ^ κ) ^ 5 * (A.card : ℝ) * (B.card : ℝ) / 3072 by positivity)
      hAsep hBsep hpaths c hcov
    refine ⟨A', hA'A, B', hB'B, hA'c, hB'c, hcover.mono subset_rfl ?_⟩
    have e5 : (δ ^ κ) ^ 5 = δ ^ (5 * κ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 1
      push_cast
      ring
    rw [e5]
    exact path_cover_budget hδ hnA hnB hratio (Nat.cast_nonneg m) hm.le ht0
  choose! Af hAfA Bf hBfB hAfc hBfc hAfcov using hdata
  -- a popular scalar
  have hfam : ∀ t ∈ S', δ ^ (2 * κ) / 24 * (A.card : ℝ) * (B.card : ℝ) ≤
      ((Af t).card : ℝ) * ((Bf t).card : ℝ) := by
    intro t ht
    have h := mul_le_mul (hAfc t ht) (hBfc t ht) (by positivity) (Nat.cast_nonneg _)
    have e : δ ^ (2 * κ) = δ ^ κ * δ ^ κ := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [e]
    calc δ ^ κ * δ ^ κ / 24 * (A.card : ℝ) * (B.card : ℝ) =
        δ ^ κ * (A.card : ℝ) / 6 * (δ ^ κ * (B.card : ℝ) / 4) := by ring
      _ ≤ _ := h
  obtain ⟨t₀, ht₀, S'', hS''S', hS''card, hover⟩ := popular_overlap S' A B Af Bf hS'ne hA hB
    hAfA hBfB (show 0 < δ ^ (2 * κ) / 24 by positivity) hfam
  have hA₀ne : (Af t₀).Nonempty := Finset.card_pos.mp (by
    have h := hAfc t₀ ht₀
    have h' : (0 : ℝ) < (Af t₀).card := lt_of_lt_of_le (by positivity) h
    exact_mod_cast h')
  have hB₀ne : (Bf t₀).Nonempty := Finset.card_pos.mp (by
    have h := hBfc t₀ ht₀
    have h' : (0 : ℝ) < (Bf t₀).card := lt_of_lt_of_le (by positivity) h
    exact_mod_cast h')
  have hA₀sep : ∀ x ∈ Af t₀, ∀ y ∈ Af t₀, x ≠ y → δ ≤ dist x y :=
    fun x hx y hy hne => hAsep x (hAfA t₀ ht₀ hx) y (hAfA t₀ ht₀ hy) hne
  have hB₀sep : ∀ x ∈ Bf t₀, ∀ y ∈ Bf t₀, x ≠ y → δ ≤ dist x y :=
    fun x hx y hy hne => hBsep x (hBfB t₀ ht₀ hx) y (hBfB t₀ ht₀ hy) hne
  -- transfer the small projections to `Af t₀ × Bf t₀`
  have htrans : ∀ t ∈ S'', RealCoverBound δ (Af t₀ + realScalarImage t (Bf t₀))
      (transferConst * δ ^ (-(100 * κ)) * A.card) := by
    intro t ht
    have htS' : t ∈ S' := hS''S' ht
    have hτ : 0 < δ ^ (4 * κ) := Real.rpow_pos_of_pos hδ _
    have hab := hover t ht
    have h := projection_transfer hδ hτ (hS'low t₀ ht₀) (hSunit t₀ (hS'S ht₀)).2
      (hS'low t htS') (hSunit t (hS'S htS')).2
      (show 0 < (δ ^ (2 * κ) / 24) ^ 2 * (A.card : ℝ) / 2 by positivity)
      (show 0 < (δ ^ (2 * κ) / 24) ^ 2 * (B.card : ℝ) / 2 by positivity)
      hA₀ne hB₀ne hA₀sep hB₀sep (hAfcov t₀ ht₀) (hAfcov t htS') hab.1 hab.2
    apply h.mono subset_rfl
    have hb := transfer_budget hδ hnA hnB hratio (hAfc t₀ ht₀) (hBfc t₀ ht₀)
    have hpos : 0 < (δ ^ (4 * κ)) ^ 4 * ((δ ^ (2 * κ) / 24) ^ 2 * (A.card : ℝ) / 2) *
        ((δ ^ (2 * κ) / 24) ^ 2 * (B.card : ℝ) / 2) := by positivity
    calc 241864704 * (23887872 * δ ^ (-(14 * κ)) * (A.card : ℝ)) ^ 5 /
          ((δ ^ (4 * κ)) ^ 4 * ((δ ^ (2 * κ) / 24) ^ 2 * (A.card : ℝ) / 2) *
            ((δ ^ (2 * κ) / 24) ^ 2 * (B.card : ℝ) / 2) * ((Af t₀).card : ℝ) *
              ((Bf t₀).card : ℝ))
        ≤ transferConst * δ ^ (-(100 * κ)) * (A.card : ℝ) := hb
      _ = _ := rfl
  -- the frostman constants of the popular product and scalars
  have hκpos : 1 ≤ δ ^ (-κ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hκ4pos : 1 ≤ δ ^ (-(4 * κ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hκle : δ ^ (-κ) ≤ δ ^ (-(4 * κ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  set C' := 2304 * C * δ ^ (-(4 * κ)) with hC'def
  have hC'1 : 1 ≤ C' := by
    rw [hC'def]
    nlinarith
  have hC'η : C' ≤ δ ^ (-η) := by
    have h1 : C' ≤ 2304 * δ ^ (-κ) * δ ^ (-(4 * κ)) := by
      rw [hC'def]
      gcongr
    have h2 : 2304 * δ ^ (-κ) * δ ^ (-(4 * κ)) = 2304 * δ ^ (-(5 * κ)) := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    have h3 : 2304 * δ ^ (-(5 * κ)) ≤ δ ^ (-(η - 5 * κ)) * δ ^ (-(5 * κ)) :=
      mul_le_mul_of_nonneg_right (hc2 δ hδ hδd2) (by positivity)
    have h4 : δ ^ (-(η - 5 * κ)) * δ ^ (-(5 * κ)) = δ ^ (-η) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    linarith
  have hAF₀ : RealFiniteFrostman δ C' σ (Af t₀) := by
    have h := hAF.subset hδ (by linarith) (show 0 < δ ^ κ / 6 by positivity) (hAfA t₀ ht₀)
      (by have := hAfc t₀ ht₀; linarith)
    apply RealFiniteFrostman.weaken (C := C / (δ ^ κ / 6)) h hδ
    have e1 : C / (δ ^ κ / 6) = 6 * C * δ ^ (-κ) := by
      rw [Real.rpow_neg hδ.le]
      field_simp
    rw [e1, hC'def]
    have h1 : 6 * C * δ ^ (-κ) ≤ 6 * C * δ ^ (-(4 * κ)) :=
      mul_le_mul_of_nonneg_left hκle (by positivity)
    nlinarith
  have hBF₀ : RealFiniteFrostman δ C' σ (Bf t₀) := by
    have h := hBF.subset hδ (by linarith) (show 0 < δ ^ κ / 4 by positivity) (hBfB t₀ ht₀)
      (by have := hBfc t₀ ht₀; linarith)
    apply RealFiniteFrostman.weaken (C := C / (δ ^ κ / 4)) h hδ
    have e1 : C / (δ ^ κ / 4) = 4 * C * δ ^ (-κ) := by
      rw [Real.rpow_neg hδ.le]
      field_simp
    rw [e1, hC'def]
    have h1 : 4 * C * δ ^ (-κ) ≤ 4 * C * δ ^ (-(4 * κ)) :=
      mul_le_mul_of_nonneg_left hκle (by positivity)
    nlinarith
  have hSF'' : RealFiniteFrostman δ C' σ S'' := by
    have hc2' : (δ ^ (2 * κ) / 24) ^ 2 / 2 = δ ^ (4 * κ) / 1152 := by
      have e : (δ ^ (2 * κ)) ^ 2 = δ ^ (4 * κ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
        congr 1
        push_cast
        ring
      rw [div_pow, e]
      ring
    have h := hS'F.subset hδ (by linarith) (show 0 < δ ^ (4 * κ) / 1152 by positivity) hS''S'
      (by rw [← hc2']; linarith)
    apply RealFiniteFrostman.weaken (C := 2 * C / (δ ^ (4 * κ) / 1152)) h hδ
    apply le_of_eq
    rw [hC'def, Real.rpow_neg hδ.le]
    field_simp
    ring
  have hS''ne : S''.Nonempty := by
    apply Finset.card_pos.mp
    have h1 : (0 : ℝ) < S'.card := by exact_mod_cast hS'ne.card_pos
    have : (0 : ℝ) < S''.card := lt_of_lt_of_le (by positivity) hS''card
    exact_mod_cast this
  have hcardη (X : Finset ℝ) (hXA : (X.card : ℝ) ≤ δ ^ (-σ - κ)) :
      (X.card : ℝ) ≤ δ ^ (-σ - η) :=
    hXA.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  obtain ⟨t, htS'', hlower⟩ := hrect δ σ C' hδ hδ₁' hσ hσmax hC'1 hC'η (Af t₀) (Bf t₀) S''
    hA₀ne hB₀ne hS''ne (fun s hs => hSunit s (hS'S (hS''S' hs))) hAF₀ hBF₀ hSF''
    hA₀sep hB₀sep
    (hcardη _ ((show ((Af t₀).card : ℝ) ≤ A.card by
      exact_mod_cast Finset.card_le_card (hAfA t₀ ht₀)).trans hAc))
    (hcardη _ ((show ((Bf t₀).card : ℝ) ≤ B.card by
      exact_mod_cast Finset.card_le_card (hBfB t₀ ht₀)).trans hBc))
  rw [rectangular_projection_image] at hlower
  obtain ⟨n, cc, hcc, hn⟩ := htrans t htS''
  have hlow := hlower n cc hcc
  -- numeric contradiction
  have hA₀c := hAfc t₀ ht₀
  have hR : δ ^ (-(199 * κ)) * (A.card : ℝ) / 6 ≤ δ ^ (-η) * ((Af t₀).card : ℝ) := by
    have h1 : δ ^ (-(200 * κ)) ≤ δ ^ (-η) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h2 : δ ^ (-(200 * κ)) * (δ ^ κ * (A.card : ℝ) / 6) ≤ δ ^ (-η) * ((Af t₀).card : ℝ) :=
      mul_le_mul h1 hA₀c (by positivity) (by positivity)
    have e : δ ^ (-(200 * κ)) * (δ ^ κ * (A.card : ℝ) / 6) =
        δ ^ (-(199 * κ)) * (A.card : ℝ) / 6 := by
      have e' : δ ^ (-(200 * κ)) * δ ^ κ = δ ^ (-(199 * κ)) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      calc δ ^ (-(200 * κ)) * (δ ^ κ * (A.card : ℝ) / 6) =
          δ ^ (-(200 * κ)) * δ ^ κ * (A.card : ℝ) / 6 := by ring
        _ = δ ^ (-(199 * κ)) * (A.card : ℝ) / 6 := by rw [e']
    linarith
  have hcmp := family_final_budget hδ hnA (hc3 δ hδ hδd3)
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
