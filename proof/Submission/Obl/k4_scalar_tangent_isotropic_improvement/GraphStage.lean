import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphNumerics

/-!
# The velocity-graph stage in one world, with explicit parameters

`graph_stage_world` instantiates `graph_world` with fine cells `N^-B`, coarse cubes
`⌊N^((B-1)/2)⌋ N^-B`, slab `N^-L`, plane window `N^-b'/2` and light threshold
`N^(-(2+d)B)/(100 H₀²)`, under five explicit numerical conditions.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Filter Submission.Lib.K4ContinuousKakeya
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- The graph bound of the velocity-graph stage. -/
def graphBd (H₀ N b' : ℝ) : ℝ := 2 * ((3 * H₀ + 1) * (2 * (3 * H₀) / (N ^ (-b') / 2) + 1))

lemma nnreal_smul_eq_ofReal_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (H : ℝ) :
    H.toNNReal • μ = ENNReal.ofReal H • μ := by
  ext s _
  simp [ENNReal.ofReal]

/-- The basic size facts of the stage parameters. -/
lemma stage_scales {N : ℝ} {B : ℕ} (hN : 2 ≤ N) (hB : 3 ≤ B) :
    0 < N ^ (-(B : ℝ)) ∧ N ^ (-(B : ℝ)) ≤ 1 ∧ 1 ≤ ⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ ∧
      (⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)) ≤ N ^ (-(((B : ℝ) + 1) / 2)) ∧
      N ^ (-(((B : ℝ) + 1) / 2)) / 2 ≤ (⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast hB
  have hb := Real.rpow_pos_of_pos hN0 (-(B : ℝ))
  have hX1 : 2 ≤ N ^ (((B : ℝ) - 1) / 2) := by
    calc (2 : ℝ) ≤ N := hN
      _ = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ (((B : ℝ) - 1) / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsplit : N ^ (-(((B : ℝ) + 1) / 2)) = N ^ (((B : ℝ) - 1) / 2) * N ^ (-(B : ℝ)) := by
    rw [← Real.rpow_add hN0]; ring_nf
  refine ⟨hb, Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith), ?_, ?_, ?_⟩
  · exact Nat.le_floor (by push_cast; linarith)
  · rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) hb.le
  · rw [hsplit]
    have := Nat.lt_floor_add_one (N ^ (((B : ℝ) - 1) / 2))
    nlinarith

/-- The visited-cube count of the stage parameters. -/
lemma stage_mc_le {N H₀ : ℝ} {B : ℕ} (hN : 2 ≤ N) (hB : 3 ≤ B) (hH₀ : 1 ≤ H₀) :
    (((⌊1 / ((⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)))⌋₊ + 1) *
      (2 * (⌈H₀⌉₊ + 1) + 1) * (2 * (⌈3 * H₀⌉₊ + 1) + 1) : ℕ) : ℝ) ≤
      231 * H₀ ^ 2 * N ^ (((B : ℝ) + 1) / 2) := by
  obtain ⟨hb, hb1, hM₀1, hw₀le, hw₀ge⟩ := stage_scales hN hB
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hH0 : 0 ≤ H₀ := by linarith
  set w₀ : ℝ := (⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)) with hw₀
  set X : ℝ := N ^ (((B : ℝ) + 1) / 2) with hX
  have hXinv : N ^ (-(((B : ℝ) + 1) / 2)) = X⁻¹ := Real.rpow_neg hN0.le _
  rw [hXinv] at hw₀le hw₀ge
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 (by positivity)
  have hX0 : 0 < X := by linarith
  have hw₀pos : 0 < w₀ := lt_of_lt_of_le (by positivity) hw₀ge
  clear_value w₀ X
  have hinv : 1 / w₀ ≤ 2 * X := by
    rw [div_le_iff₀ hw₀pos]
    have := mul_le_mul_of_nonneg_left hw₀ge (by linarith : (0 : ℝ) ≤ 2 * X)
    have e : 2 * X * (X⁻¹ / 2) = 1 := by field_simp
    linarith only [this, e]
  have f1 : ((⌊1 / w₀⌋₊ : ℝ) + 1) ≤ 3 * X := by
    have := Nat.floor_le (le_of_lt (one_div_pos.mpr hw₀pos))
    linarith only [this, hinv, hX1]
  have f2 : (2 * ((⌈H₀⌉₊ : ℝ) + 1) + 1) ≤ 7 * H₀ := by
    have := Nat.ceil_lt_add_one hH0
    linarith only [this, hH₀]
  have f3 : (2 * ((⌈3 * H₀⌉₊ : ℝ) + 1) + 1) ≤ 11 * H₀ := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 3 * H₀)
    linarith only [this, hH₀]
  push_cast
  calc ((⌊1 / w₀⌋₊ : ℝ) + 1) * (2 * ((⌈H₀⌉₊ : ℝ) + 1) + 1) * (2 * ((⌈3 * H₀⌉₊ : ℝ) + 1) + 1)
      ≤ (3 * X) * (7 * H₀) * (11 * H₀) := by
        apply mul_le_mul (mul_le_mul f1 f2 (by positivity) (by positivity)) f3 (by positivity)
          (by positivity)
    _ = 231 * H₀ ^ 2 * X := by ring

/-- The Kakeya contradiction hypothesis of `graph_world` holds for the stage parameters. -/
lemma stage_hcontr {C N H₀ K d L b r₀ lam ε : ℝ} {B M₀ mc : ℕ} {τ₀ : ℝ≥0}
    (hC0 : 0 ≤ C) (hN : 2 ≤ N) (hH₀ : 1 ≤ H₀) (hK : 1 ≤ K) (hd : 0 ≤ d) (hB : 3 ≤ B)
    (hbdef : b = N ^ (-(B : ℝ))) (hr₀ : r₀ = ((B : ℝ) + 1) / 2)
    (hM₀ : M₀ = ⌊N ^ (((B : ℝ) - 1) / 2)⌋₊)
    (hlam : lam = N ^ (-(2 + d) * B) / (100 * H₀ ^ 2)) (hε : ε = N ^ (-L))
    (hmc : mc = (⌊1 / ((M₀ : ℝ) * b)⌋₊ + 1) * (2 * (⌈H₀⌉₊ + 1) + 1) * (2 * (⌈3 * H₀⌉₊ + 1) + 1))
    (hτ₀ : (τ₀ : ℝ) = 1 / (288 * H₀ ^ 2 * mc))
    (n1 : H₀ ≤ N) (n2 : 144 * H₀ * N ^ (-(((B : ℝ) + 1) / 2)) ≤ N ^ (-2 * L))
    (n5 : 10 ^ 25 * K * (C ^ 2 + 1) * H₀ ^ 20 ≤ N ^ ((1 - d) * ((B : ℝ) - 1) / 2 - 2 * L)) :
    0 < ε ^ 2 - (Nat.factorial 3) * (3 : ℕ) * (4 * H₀ * ((M₀ : ℝ) * b)) ∧
    ((⌊27 * (K * N ^ (-(2 + d) * r₀)) / lam⌋₊ : ℕ) : ℝ) ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1)) *
      (2 ^ (3 : ℕ) * C * (2 * b + H₀ * ((M₀ : ℝ) * b) ^ 2) ^ (3 : ℕ) / b ^ 3 *
        ((H₀.toNNReal * b.toNNReal : ℝ≥0) : ℝ) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1)) /
        ((ε ^ 2 - (Nat.factorial 3) * (3 : ℕ) * (4 * H₀ * ((M₀ : ℝ) * b))) *
          ((1 / 2 : ℝ) ^ 2 - (3 : ℕ) * (1 / 24 : ℝ))) ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1)) *
        ((H₀.toNNReal : ℝ) / τ₀) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1))) ≤
      (1 / 2) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1)) := by
  obtain ⟨hb, hb1, hM₀1, hw₀le, hw₀ge⟩ := stage_scales hN hB
  have hmcb := stage_mc_le hN hB hH₀
  rw [← hM₀, ← hbdef, ← hmc, ← hr₀] at hmcb
  rw [← hM₀, ← hbdef, ← hr₀] at hw₀le hw₀ge
  rw [← hbdef] at hb hb1
  rw [← hr₀] at n2
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hH0 : 0 ≤ H₀ := by linarith
  have hNB : 0 < N ^ (-(2 + d) * B) := Real.rpow_pos_of_pos hN0 _
  have hr₀pos : 0 < N ^ (-r₀) := Real.rpow_pos_of_pos hN0 _
  have hmc1 : (1 : ℝ) ≤ mc := by
    have : 1 ≤ mc := by rw [hmc]; apply Nat.one_le_iff_ne_zero.mpr; positivity
    exact_mod_cast this
  have hε2 : ε ^ 2 = N ^ (-2 * L) := by
    rw [hε, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hNL : 0 < N ^ (-2 * L) := Real.rpow_pos_of_pos hN0 _
  have h72 : (Nat.factorial 3 : ℝ) * ((3 : ℕ) : ℝ) * (4 * H₀ * ((M₀ : ℝ) * b)) ≤
      N ^ (-2 * L) / 2 := by
    have e : (Nat.factorial 3 : ℝ) * ((3 : ℕ) : ℝ) * (4 * H₀ * ((M₀ : ℝ) * b)) =
        72 * H₀ * ((M₀ : ℝ) * b) := by norm_num [Nat.factorial]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hw₀le (by positivity : (0 : ℝ) ≤ 72 * H₀)
    linarith only [this, n2]
  have hβlow : N ^ (-2 * L) / 2 ≤
      ε ^ 2 - (Nat.factorial 3 : ℝ) * ((3 : ℕ) : ℝ) * (4 * H₀ * ((M₀ : ℝ) * b)) := by
    rw [hε2]; linarith only [h72]
  refine ⟨lt_of_lt_of_le (by positivity) hβlow, ?_⟩
  have hp8 : ((1 / 2 : ℝ) ^ 2 - (3 : ℕ) * (1 / 24 : ℝ)) = 1 / 8 := by norm_num
  have hβp : 0 < (ε ^ 2 - (Nat.factorial 3) * (3 : ℕ) * (4 * H₀ * ((M₀ : ℝ) * b))) *
      ((1 / 2 : ℝ) ^ 2 - (3 : ℕ) * (1 / 24 : ℝ)) := by
    rw [hp8]; exact mul_pos (lt_of_lt_of_le (by positivity) hβlow) (by norm_num)
  apply hcontr_of_poly (Nat.cast_nonneg _) (by positivity) (by positivity) (by positivity) hβp
  have hS₀ : ((⌊27 * (K * N ^ (-(2 + d) * r₀)) / lam⌋₊ : ℕ) : ℝ) ≤
      2700 * K * H₀ ^ 2 * (N ^ (-(2 + d) * r₀) * N ^ ((2 + d) * B)) := by
    have hlam0 : 0 < lam := by rw [hlam]; positivity
    refine le_trans (Nat.floor_le (by positivity)) (le_of_eq ?_)
    rw [hlam]
    have : N ^ ((2 + d) * (B : ℝ)) = (N ^ (-(2 + d) * (B : ℝ)))⁻¹ := by
      rw [← Real.rpow_neg hN0.le]; ring_nf
    rw [this]; field_simp; ring
  have hAb : H₀ * ((M₀ : ℝ) * b) ^ 2 ≤ b := by
    have h1 : ((M₀ : ℝ) * b) ^ 2 ≤ (N ^ (-r₀)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hw₀le 2
    have h2 : (N ^ (-r₀)) ^ 2 = N ^ (-(1 : ℝ)) * b := by
      rw [hbdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, hr₀]
      ring_nf
    have h3 : H₀ * N ^ (-(1 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_one hN0]; exact n1
    calc H₀ * ((M₀ : ℝ) * b) ^ 2 ≤ H₀ * (N ^ (-(1 : ℝ)) * b) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hH0
      _ = (H₀ * N ^ (-(1 : ℝ))) * b := by ring
      _ ≤ 1 * b := mul_le_mul_of_nonneg_right h3 hb.le
      _ = b := one_mul b
  have hP : 2 ^ (3 : ℕ) * C * (2 * b + H₀ * ((M₀ : ℝ) * b) ^ 2) ^ (3 : ℕ) / b ^ 3 ≤ 216 * C := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 * b + H₀ * ((M₀ : ℝ) * b) ^ 2) ^ 3 ≤ (3 * b) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hAb]) 3
    calc 2 ^ (3 : ℕ) * C * (2 * b + H₀ * ((M₀ : ℝ) * b) ^ 2) ^ (3 : ℕ)
        ≤ 2 ^ (3 : ℕ) * C * (3 * b) ^ 3 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 216 * C * b ^ 3 := by ring
  have hHb : ((H₀.toNNReal * b.toNNReal : ℝ≥0) : ℝ) = H₀ * b := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hH0, Real.coe_toNNReal _ hb.le]
  have hHτ : (H₀.toNNReal : ℝ) / τ₀ ≤ 66528 * H₀ ^ 5 * N ^ r₀ := by
    rw [Real.coe_toNNReal _ hH0, hτ₀]
    have : H₀ / (1 / (288 * H₀ ^ 2 * mc)) = 288 * H₀ ^ 3 * mc := by field_simp
    rw [this]
    calc 288 * H₀ ^ 3 * (mc : ℝ) ≤ 288 * H₀ ^ 3 * (231 * H₀ ^ 2 * N ^ r₀) :=
          mul_le_mul_of_nonneg_left hmcb (by positivity)
      _ = 66528 * H₀ ^ 5 * N ^ r₀ := by ring
  have hNid : N ^ (-(2 + d) * r₀) * N ^ ((2 + d) * B) * b ^ 3 * (N ^ r₀) ^ 3 =
      N ^ (-((1 - d) * ((B : ℝ) - 1) / 2)) := by
    rw [hbdef, ← Real.rpow_natCast (N ^ (-(B : ℝ))) 3, ← Real.rpow_mul hN0.le,
      ← Real.rpow_natCast (N ^ r₀) 3, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
      ← Real.rpow_add hN0, ← Real.rpow_add hN0, hr₀]
    congr 1; push_cast; ring
  have hT : 0 < N ^ (((1 - d) * ((B : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hN0 _
  have hn5 : 10 ^ 25 * K * (C ^ 2 + 1) * H₀ ^ 20 * N ^ (-((1 - d) * ((B : ℝ) - 1) / 2)) ≤
      N ^ (-2 * L) := by
    have e1 : N ^ ((1 - d) * ((B : ℝ) - 1) / 2 - 2 * L) =
        N ^ ((1 - d) * ((B : ℝ) - 1) / 2) * N ^ (-2 * L) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have e2 : N ^ (-((1 - d) * ((B : ℝ) - 1) / 2)) =
        (N ^ ((1 - d) * ((B : ℝ) - 1) / 2))⁻¹ := Real.rpow_neg hN0.le _
    rw [e1] at n5
    rw [e2, ← div_eq_mul_inv, div_le_iff₀ hT]
    linarith only [n5]
  have hP0 : 0 ≤ 2 ^ (3 : ℕ) * C * (2 * b + H₀ * ((M₀ : ℝ) * b) ^ 2) ^ (3 : ℕ) / b ^ 3 := by
    positivity
  have hτ0 : 0 ≤ (H₀.toNNReal : ℝ) / τ₀ := by positivity
  have hfin : ((⌊27 * (K * N ^ (-(2 + d) * r₀)) / lam⌋₊ : ℕ) : ℝ) *
      (2 ^ (3 : ℕ) * C * (2 * b + H₀ * ((M₀ : ℝ) * b) ^ 2) ^ (3 : ℕ) / b ^ 3) ^ 2 *
      ((H₀.toNNReal * b.toNNReal : ℝ≥0) : ℝ) ^ 3 * ((H₀.toNNReal : ℝ) / τ₀) ^ 3 ≤
      (2700 * K * H₀ ^ 2 * (N ^ (-(2 + d) * r₀) * N ^ ((2 + d) * B))) * (216 * C) ^ 2 *
        (H₀ * b) ^ 3 * (66528 * H₀ ^ 5 * N ^ r₀) ^ 3 := by
    rw [hHb]
    gcongr
  calc _ ≤ _ := hfin
    _ = (2700 * 216 ^ 2 * 66528 ^ 3) * K * C ^ 2 * H₀ ^ 20 *
          (N ^ (-(2 + d) * r₀) * N ^ ((2 + d) * B) * b ^ 3 * (N ^ r₀) ^ 3) := by ring
    _ = (2700 * 216 ^ 2 * 66528 ^ 3) * K * C ^ 2 * H₀ ^ 20 *
          N ^ (-((1 - d) * ((B : ℝ) - 1) / 2)) := by rw [hNid]
    _ ≤ (10 ^ 25 / 128) * K * (C ^ 2 + 1) * H₀ ^ 20 * N ^ (-((1 - d) * ((B : ℝ) - 1) / 2)) := by
        have hK0 : 0 ≤ K := by linarith
        have hpos : 0 ≤ N ^ (-((1 - d) * ((B : ℝ) - 1) / 2)) := by positivity
        gcongr
        · norm_num
        · linarith only []
    _ ≤ N ^ (-2 * L) / 128 := by linarith only [hn5]
    _ ≤ _ := by rw [hp8]; linarith only [hβlow]

/-- **The velocity graph in one world, with the stage parameters.** Fine cells of side
`b = N^-B`, coarse cubes of side `⌊N^((B-1)/2)⌋ b`, slab width `ε = N^-L`, plane window
`δ = N^-b' / 2`, light threshold `λ = N^(-(2+d)B) / (100 H₀²)`, `c = 1/2`, `η = 1/24`. -/
theorem graph_stage_world {C : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK 3 C)
    (θ : Measure (ℕ × (Fin 5 → ℝ))) [IsFiniteMeasure θ] (hθ1 : θ Set.univ ≤ 1)
    (ρ : Measure Inc) [IsFiniteMeasure ρ] (π : Measure ℝ)
    {E₀ : Set Inc} (hE₀ : MeasurableSet E₀)
    {N H₀ K d S L b' : ℝ} {B : ℕ} (hN : 2 ≤ N) (hH₀ : 1 ≤ H₀) (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hB : 3 ≤ B) (hL : 0 < L) (hb' : 0 < b')
    (hle : ρ.restrict E₀ ≤ ENNReal.ofReal H₀ • (θ.prod volume).restrict E₀)
    (hge : ENNReal.ofReal H₀⁻¹ • (θ.prod volume).restrict E₀ ≤ ρ.restrict E₀)
    (hE₀H : ∀ p ∈ E₀, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H₀)
    (hOccFin : Set.Finite
      {q : Fin 3 → ℤ | ρ.restrict E₀ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q) ≠ 0})
    (hOccCard : ({q : Fin 3 → ℤ | ρ.restrict E₀ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q) ≠ 0}.ncard :
      ℝ) ≤ H₀ * N ^ ((2 + d) * B))
    (hcoarse : ∀ q, ρ (physOf ⁻¹' cellSet (N ^ (-(((B : ℝ) + 1) / 2))) q) ≤
      ENNReal.ofReal (K * N ^ (-(2 + d) * (((B : ℝ) + 1) / 2))))
    (hjoint : ∀ (f : Fin 3 → ℤ) (c : ℤ), ρ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) f ∩
      {p | ⌊p.1.2 1 / N ^ (-b')⌋ = c}) ≤
        ENNReal.ofReal (K * N ^ (-(2 + d) * B)) * π {v | ⌊v / N ^ (-b')⌋ = c})
    (hπ : ∀ c : ℤ, π {v | ⌊v / N ^ (-b')⌋ = c} ≤ ENNReal.ofReal (K * N ^ (-S * b')))
    (n1 : H₀ ≤ N)
    (n2 : 144 * H₀ * N ^ (-(((B : ℝ) + 1) / 2)) ≤ N ^ (-2 * L))
    (n3 : N ^ (-L) * (1 + 4 * H₀) * (1 + 4 * (3 * H₀ + 1) * N ^ b') ≤ 1 / 2)
    (n4 : 600 * K ^ 2 * H₀ ^ 2 ≤ N ^ (S * b'))
    (n5 : 10 ^ 25 * K * (C ^ 2 + 1) * H₀ ^ 20 ≤ N ^ ((1 - d) * ((B : ℝ) - 1) / 2 - 2 * L)) :
    ∃ (E : Set Inc) (G : (Fin 3 → ℤ) → ℝ × ℝ), MeasurableSet E ∧ E ⊆ E₀ ∧
      (ρ.restrict E₀ Set.univ).toReal ≤
        2 * (ρ.restrict E Set.univ).toReal + 1 / (100 * H₀) + 1 / (4 * H₀) ∧
      (∀ p ∈ E, |(G (cellIdx (N ^ (-(B : ℝ))) (physOf p))).1| ≤ graphBd H₀ N b' ∧
        |(G (cellIdx (N ^ (-(B : ℝ))) (physOf p))).2| ≤ graphBd H₀ N b' ∧
        |(p.1.2 3 + 2 * p.1.2 4 * p.2) - (G (cellIdx (N ^ (-(B : ℝ))) (physOf p))).1 -
            (G (cellIdx (N ^ (-(B : ℝ))) (physOf p))).2 * p.1.2 1| ≤
          N ^ (-L) * (1 + 4 * H₀) * graphBd H₀ N b') ∧
      (∀ q, ρ.restrict E (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q) ≠ 0 →
        ENNReal.ofReal (N ^ (-(2 + d) * B) / (200 * H₀ ^ 2)) ≤
          ρ.restrict E (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q)) := by
  classical
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hH0 : 0 ≤ H₀ := by linarith
  obtain ⟨hb, hb1, hM₀1, hw₀le, hw₀ge⟩ := stage_scales hN hB
  have hw₀pos : 0 < (⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)) :=
    lt_of_lt_of_le (by positivity) hw₀ge
  have hw₀1 : (⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)) ≤ 1 :=
    le_trans hw₀le (Real.rpow_le_one_of_one_le_of_nonpos hN1
      (by have : (0 : ℝ) ≤ B := Nat.cast_nonneg B; linarith))
  have hNB : 0 < N ^ (-(2 + d) * B) := Real.rpow_pos_of_pos hN0 _
  have hW0 : 0 < N ^ (-b') := Real.rpow_pos_of_pos hN0 _
  have hmc1 : (1 : ℝ) ≤ ((⌊1 / ((⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)))⌋₊ + 1) *
      (2 * (⌈H₀⌉₊ + 1) + 1) * (2 * (⌈3 * H₀⌉₊ + 1) + 1) : ℕ) := by
    have : 1 ≤ (⌊1 / ((⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)))⌋₊ + 1) *
      (2 * (⌈H₀⌉₊ + 1) + 1) * (2 * (⌈3 * H₀⌉₊ + 1) + 1) := by
      apply Nat.one_le_iff_ne_zero.mpr; positivity
    exact_mod_cast this
  set mc : ℕ := (⌊1 / ((⌊N ^ (((B : ℝ) - 1) / 2)⌋₊ : ℝ) * N ^ (-(B : ℝ)))⌋₊ + 1) *
      (2 * (⌈H₀⌉₊ + 1) + 1) * (2 * (⌈3 * H₀⌉₊ + 1) + 1) with hmc
  set τ₀ : ℝ≥0 := (1 / (288 * H₀ ^ 2 * mc)).toNNReal with hτ₀
  have hτ₀r : (τ₀ : ℝ) = 1 / (288 * H₀ ^ 2 * mc) := Real.coe_toNNReal _ (by positivity)
  have hτ₀pos : 0 < τ₀ := by
    rw [← NNReal.coe_pos, hτ₀r]; positivity
  -- the Kakeya hypothesis
  obtain ⟨hβ', hcontr⟩ := stage_hcontr (C := C) (K := K) (d := d) (L := L)
    (lam := N ^ (-(2 + d) * B) / (100 * H₀ ^ 2)) (ε := N ^ (-L)) (τ₀ := τ₀)
    hC0 hN hH₀ hK hd hB rfl rfl rfl rfl rfl hmc hτ₀r n1 n2 n5
  -- density hypotheses in `graph_world` form
  have hle' : ρ.restrict E₀ ≤ H₀.toNNReal • (θ.prod volume).restrict E₀ := by
    rw [nnreal_smul_eq_ofReal_smul]; exact hle
  have hge' : (θ.prod volume).restrict E₀ ≤ H₀.toNNReal • ρ.restrict E₀ := by
    rw [nnreal_smul_eq_ofReal_smul]
    calc (θ.prod volume).restrict E₀
        = (ENNReal.ofReal H₀ * ENNReal.ofReal H₀⁻¹) • (θ.prod volume).restrict E₀ := by
          rw [← ENNReal.ofReal_mul hH0, mul_inv_cancel₀ (by linarith), ENNReal.ofReal_one,
            one_smul]
      _ = ENNReal.ofReal H₀ • (ENNReal.ofReal H₀⁻¹ • (θ.prod volume).restrict E₀) := by
          rw [smul_smul]
      _ ≤ ENNReal.ofReal H₀ • ρ.restrict E₀ := by
          intro s
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr; exact hge s
  -- occupied fine cells
  have hOcc : ∀ q, ρ.restrict E₀ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q) ≠ 0 →
      q ∈ hOccFin.toFinset := by
    intro q hq; rw [Set.Finite.mem_toFinset]; exact hq
  have hOccc : (hOccFin.toFinset.card : ℝ) ≤ H₀ * N ^ ((2 + d) * B) := by
    rw [← Set.ncard_eq_toFinset_card _ hOccFin]; exact hOccCard
  -- coarse caps, windows
  have hcapQ := measure_cellSet_le_of_coarser ρ hw₀pos (Real.rpow_pos_of_pos hN0 _) hw₀le hcoarse
    (by positivity)
  have hwin : ∀ q (v₀ : ℝ), ρ {p | p ∈ physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q ∧
      |p.1.2 1 - v₀| < N ^ (-b') / 2} ≤ ENNReal.ofReal ((2 * (N ^ (-b') / 2) / N ^ (-b') + 2) *
        (K * N ^ (-(2 + d) * B) * (K * N ^ (-S * b')))) := by
    intro q v₀
    apply measure_window_le ρ _ hW0 (by positivity) _ (by positivity)
    intro c
    calc ρ (physOf ⁻¹' cellSet (N ^ (-(B : ℝ))) q ∩ {p | ⌊p.1.2 1 / N ^ (-b')⌋ = c})
        ≤ ENNReal.ofReal (K * N ^ (-(2 + d) * B)) * π {v | ⌊v / N ^ (-b')⌋ = c} := hjoint q c
      _ ≤ ENNReal.ofReal (K * N ^ (-(2 + d) * B)) * ENNReal.ofReal (K * N ^ (-S * b')) := by
          gcongr; exact hπ c
      _ = ENNReal.ofReal (K * N ^ (-(2 + d) * B) * (K * N ^ (-S * b'))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hWmax : (2 * (N ^ (-b') / 2) / N ^ (-b') + 2) *
      (K * N ^ (-(2 + d) * B) * (K * N ^ (-S * b'))) ≤
      (1 - 1 / 2) * (N ^ (-(2 + d) * B) / (100 * H₀ ^ 2)) := by
    have h2 : 2 * (N ^ (-b') / 2) / N ^ (-b') + 2 = 3 := by field_simp; ring
    have hSb : N ^ (-S * b') = (N ^ (S * b'))⁻¹ := by rw [neg_mul, Real.rpow_neg hN0.le]
    have hSbpos : 0 < N ^ (S * b') := Real.rpow_pos_of_pos hN0 _
    rw [h2, hSb]
    rw [show (1 - 1 / 2 : ℝ) * (N ^ (-(2 + d) * B) / (100 * H₀ ^ 2)) =
      N ^ (-(2 + d) * B) / (200 * H₀ ^ 2) by ring]
    rw [show 3 * (K * N ^ (-(2 + d) * ↑B) * (K * (N ^ (S * b'))⁻¹)) =
      3 * K ^ 2 * N ^ (-(2 + d) * ↑B) / N ^ (S * b') by field_simp]
    rw [div_le_div_iff₀ hSbpos (by positivity)]
    have := mul_le_mul_of_nonneg_left n4 (le_of_lt hNB)
    nlinarith
  have hsmall : N ^ (-L) * (1 + 4 * H₀) * (1 + 2 * (3 * H₀ + 1) / (N ^ (-b') / 2)) ≤ 1 / 2 := by
    have hWinv : (N ^ (-b'))⁻¹ = N ^ b' := by rw [Real.rpow_neg hN0.le, inv_inv]
    have : 2 * (3 * H₀ + 1) / (N ^ (-b') / 2) = 4 * (3 * H₀ + 1) * N ^ b' := by
      rw [← hWinv]; field_simp; ring
    rw [this]; exact n3
  -- apply the one-world graph theorem
  obtain ⟨E, G, hEm, hEsub, hmass, hbd, hheavy⟩ := graph_world hC0 hC θ ρ hE₀ hH₀ hle' hge' hE₀H
    hb hb1 hM₀1 hw₀1 hOccFin.toFinset hOcc hcapQ (by positivity : (0 : ℝ) < N ^ (-b') / 2)
      (by positivity : (0 : ℝ) < N ^ (-(2 + d) * B) / (100 * H₀ ^ 2)) hwin hWmax τ₀ hτ₀pos
      (Real.rpow_pos_of_pos hN0 (-L))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hsmall hβ' hcontr
  refine ⟨E, G, hEm, hEsub, ?_, fun p hp => hbd p hp, ?_⟩
  · -- the mass bound
    have hlight : (hOccFin.toFinset.card : ℝ) * (N ^ (-(2 + d) * B) / (100 * H₀ ^ 2)) ≤
        1 / (100 * H₀) := by
      have e : N ^ ((2 + d) * (B : ℝ)) * N ^ (-(2 + d) * (B : ℝ)) = 1 := by
        rw [← Real.rpow_add hN0]; ring_nf; exact Real.rpow_zero N
      calc (hOccFin.toFinset.card : ℝ) * (N ^ (-(2 + d) * B) / (100 * H₀ ^ 2))
          ≤ (H₀ * N ^ ((2 + d) * B)) * (N ^ (-(2 + d) * B) / (100 * H₀ ^ 2)) :=
            mul_le_mul_of_nonneg_right hOccc (by positivity)
        _ = (N ^ ((2 + d) * (B : ℝ)) * N ^ (-(2 + d) * (B : ℝ))) / (100 * H₀) := by
            field_simp
        _ = 1 / (100 * H₀) := by rw [e]
    have hθr : (θ Set.univ).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hθ1)
    have hbad : 3 / (1 / 24 : ℝ) * ((H₀.toNNReal : ℝ) * (τ₀ : ℝ) * ((mc : ℝ) * (θ Set.univ).toReal)) ≤
        1 / (4 * H₀) := by
      rw [Real.coe_toNNReal _ hH0, hτ₀r]
      have hθ0 : 0 ≤ (θ Set.univ).toReal := ENNReal.toReal_nonneg
      have hmcpos : (0 : ℝ) < mc := by linarith
      calc 3 / (1 / 24 : ℝ) * (H₀ * (1 / (288 * H₀ ^ 2 * mc)) * ((mc : ℝ) * (θ Set.univ).toReal))
          = (θ Set.univ).toReal / (4 * H₀) := by field_simp; ring
        _ ≤ 1 / (4 * H₀) := by gcongr
    have := hmass
    push_cast at this
    have e2 : (ρ.restrict E Set.univ).toReal / (1 - 1 / 2) = 2 * (ρ.restrict E Set.univ).toReal := by
      ring
    rw [e2] at this
    linarith
  · intro q hq
    have := hheavy q hq
    rw [show (1 - 1 / 2 : ℝ) * (N ^ (-(2 + d) * B) / (100 * H₀ ^ 2)) =
      N ^ (-(2 + d) * B) / (200 * H₀ ^ 2) by ring] at this
    exact this

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
