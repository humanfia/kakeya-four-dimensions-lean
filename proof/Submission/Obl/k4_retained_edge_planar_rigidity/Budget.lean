import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.ScalarClosure

/-!
# The numerical budget of the final assembly

In the final assembly every parameter is a fixed power of the mesh `h`, with the loss
`K = h^(-η)`: the marginal cap `C = 2K⁴⁴`, the endpoint bound `D = K²`, the short-pair and strip
thresholds `q = p = h^e`, the wedge width `Δ = h^(1-4e)`, the flat-law bound `φ = 60 h^(1-e₀)` and
the support bound `M = closureConst (K²⁰⁰) 27 m k n / h`. This file checks the finitely many
numerical inequalities between them (`Budget`) for all sufficiently small `h`, once the fixed
exponents satisfy a few linear constraints (`eventually_budget`).
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open Filter Topology ClosureData

noncomputable section

/-- The `K`-degree of `closureConst`. -/
def closureDeg (a m k n : ℕ) : ℕ :=
  (4 * n + 2 * a + (4 * a + 8) * n + 3 * a + a) * (m * (k * 2)) + 4 * a * (2 * (m * (k * 2))) + a

/-- `closureConst` is a monomial in `K`. -/
theorem closureConst_eq (K : ℝ) (a m k n : ℕ) :
    closureConst K a m k n = closureConst 1 a m k n * K ^ closureDeg a m k n := by
  simp only [closureConst, Bn, M1, one_pow, mul_one, closureDeg]
  ring

theorem closureConst_one_pos (a m k n : ℕ) : 0 < closureConst 1 a m k n := by
  simp only [closureConst, Bn, M1, one_pow, mul_one]
  positivity

theorem rpow_npow {h : ℝ} (hh : 0 < h) (x : ℝ) (n : ℕ) :
    (h ^ x) ^ n = h ^ ((n : ℝ) * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, mul_comm]

/-! ### Eventually small powers -/

/-- Eventually `c * h ^ δ ≤ ε'`. -/
theorem eventually_mul_rpow_le (c : ℝ) {δ ε' : ℝ} (hδ : 0 < δ) (hε' : 0 < ε') :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), c * h ^ δ ≤ ε' := by
  have hc : ContinuousAt (fun h : ℝ => c * h ^ δ) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le))
  have ht := hc.tendsto
  rw [Real.zero_rpow hδ.ne', mul_zero] at ht
  exact (ht.eventually (ge_mem_nhds hε')).filter_mono nhdsWithin_le_nhds

theorem eventually_le_rpow_neg (X : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), X ≤ h ^ (-η) := by
  filter_upwards [eventually_mul_rpow_le (max X 1) hη one_pos, self_mem_nhdsWithin]
    with h h1 hpos
  have hpos' : (0 : ℝ) < h := hpos
  have hp : 0 < h ^ η := Real.rpow_pos_of_pos hpos' η
  have hX : 0 < max X 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [Real.rpow_neg hpos'.le]
  refine (le_max_left X 1).trans ?_
  rw [le_inv_comm₀ hX hp, ← one_div, le_div_iff₀ hX]
  linarith [mul_comm (max X 1) (h ^ η)]

theorem eventually_pos_le_one : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h ≤ 1 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
  exact ⟨hh.1, hh.2.le⟩

theorem eventually_lt_of_pos {h₁ : ℝ} (hh₁ : 0 < h₁) : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < h₁ := by
  filter_upwards [Ioo_mem_nhdsGT hh₁] with h hh
  exact hh.2

theorem exists_of_eventually {P : ℝ → Prop} (hP : ∀ᶠ h in 𝓝[>] (0 : ℝ), P h) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ → P h := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hP
  exact ⟨u, hu, fun h h0 h1 => hsub ⟨h0, h1⟩⟩

/-! ### The pointwise inequalities -/

theorem K_ge_one {h η : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hη : 0 ≤ η) : 1 ≤ h ^ (-η) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hh1 (by linarith)

theorem budget_le {h η e e₀ c₁ cc : ℝ} {m P : ℕ} (hh : 0 < h) (hh1 : h ≤ 1) (he1 : e ≤ 1)
    (hη : 0 ≤ η) (hm : 1 ≤ m) (hc₁ : 0 < c₁) (hcc : cc = c₁ * (h ^ (-η)) ^ P)
    (s1 : 4 ^ m * c₁ * h ^ ((m : ℝ) * (e - 44 * η) - (1 + (P : ℝ) * η)) ≤ 1 / 4)
    (s2 : (m : ℝ) * c₁ * h ^ (e * ((m : ℝ) - 1) - (1 + (P : ℝ) * η)) ≤ 1 / 4)
    (s3 : 64800 * c₁ * h ^ (4 * e - 2 * e₀ - 2 * η - (P : ℝ) * η) ≤ 1 / 4) :
    (2 * (h ^ (-η)) ^ 44 * (h ^ e + h)) ^ m + (m : ℝ) * (h ^ e) ^ (m - 1) +
      (10 + 8 * (h ^ (-η)) ^ 2) / h ^ (1 - 4 * e) * (60 * h ^ (1 - e₀)) ^ 2 <
      1 / (cc * (1 / h)) := by
  have hR : 1 / (cc * (1 / h)) = c₁⁻¹ * h ^ (1 + (P : ℝ) * η) := by
    rw [hcc, rpow_npow hh, Real.rpow_add hh, Real.rpow_one, mul_neg, Real.rpow_neg hh.le]
    field_simp
  rw [hR]
  set R := c₁⁻¹ * h ^ (1 + (P : ℝ) * η) with hRdef
  have hRpos : 0 < R := mul_pos (inv_pos.mpr hc₁) (Real.rpow_pos_of_pos hh _)
  have hsplit : ∀ δ : ℝ, h ^ (δ + (1 + (P : ℝ) * η)) = c₁ * h ^ δ * R := by
    intro δ
    rw [Real.rpow_add hh, hRdef]
    field_simp
  have hhe : h ≤ h ^ e := by
    have := Real.rpow_le_rpow_of_exponent_ge hh hh1 he1
    rwa [Real.rpow_one] at this
  have hK1 : 1 ≤ h ^ (-η) := K_ge_one hh hh1 hη
  -- the short-pair term
  have hT1 : (2 * (h ^ (-η)) ^ 44 * (h ^ e + h)) ^ m ≤
      (4 ^ m * c₁ * h ^ ((m : ℝ) * (e - 44 * η) - (1 + (P : ℝ) * η))) * R := by
    have hbase : 2 * (h ^ (-η)) ^ 44 * (h ^ e + h) ≤ 4 * h ^ (e - 44 * η) := by
      have e1 : h ^ (e - 44 * η) = (h ^ (-η)) ^ 44 * h ^ e := by
        rw [rpow_npow hh, ← Real.rpow_add hh]
        ring_nf
      rw [e1]
      have : 0 ≤ (h ^ (-η)) ^ 44 := by positivity
      nlinarith
    calc (2 * (h ^ (-η)) ^ 44 * (h ^ e + h)) ^ m ≤ (4 * h ^ (e - 44 * η)) ^ m :=
          pow_le_pow_left₀ (by positivity) hbase m
      _ = 4 ^ m * h ^ ((m : ℝ) * (e - 44 * η)) := by rw [mul_pow, rpow_npow hh]
      _ = 4 ^ m * h ^ (((m : ℝ) * (e - 44 * η) - (1 + (P : ℝ) * η)) + (1 + (P : ℝ) * η)) := by
          rw [sub_add_cancel]
      _ = _ := by rw [hsplit]; ring
  -- the strip term
  have hT2 : (m : ℝ) * (h ^ e) ^ (m - 1) =
      ((m : ℝ) * c₁ * h ^ (e * ((m : ℝ) - 1) - (1 + (P : ℝ) * η))) * R := by
    rw [rpow_npow hh, Nat.cast_sub hm, Nat.cast_one,
      show ((m : ℝ) - 1) * e = (e * ((m : ℝ) - 1) - (1 + (P : ℝ) * η)) + (1 + (P : ℝ) * η) by
        ring, hsplit]
    ring
  -- the transverse term
  have hT3 : (10 + 8 * (h ^ (-η)) ^ 2) / h ^ (1 - 4 * e) * (60 * h ^ (1 - e₀)) ^ 2 ≤
      (64800 * c₁ * h ^ (4 * e - 2 * e₀ - 2 * η - (P : ℝ) * η)) * R := by
    have h1 : 10 + 8 * (h ^ (-η)) ^ 2 ≤ 18 * (h ^ (-η)) ^ 2 := by
      nlinarith [one_le_pow₀ (n := 2) hK1]
    have e2 : 18 * (h ^ (-η)) ^ 2 / h ^ (1 - 4 * e) * (60 * h ^ (1 - e₀)) ^ 2 =
        64800 * h ^ ((4 * e - 2 * e₀ - 2 * η - (P : ℝ) * η) + (1 + (P : ℝ) * η)) := by
      rw [show 18 * (h ^ (-η)) ^ 2 / h ^ (1 - 4 * e) * (60 * h ^ (1 - e₀)) ^ 2 =
          64800 * ((h ^ (-η)) ^ 2 * (h ^ (1 - e₀)) ^ 2 / h ^ (1 - 4 * e)) by ring,
        rpow_npow hh, rpow_npow hh, ← Real.rpow_add hh, ← Real.rpow_sub hh]
      congr 2
      push_cast
      ring
    have hpos : 0 < h ^ (1 - 4 * e) := Real.rpow_pos_of_pos hh _
    calc (10 + 8 * (h ^ (-η)) ^ 2) / h ^ (1 - 4 * e) * (60 * h ^ (1 - e₀)) ^ 2
        ≤ 18 * (h ^ (-η)) ^ 2 / h ^ (1 - 4 * e) * (60 * h ^ (1 - e₀)) ^ 2 := by gcongr
      _ = _ := by rw [e2, hsplit]; ring
  have hsum := add_le_add (add_le_add hT1 hT2.le) hT3
  calc _ ≤ _ := hsum
    _ ≤ (1 / 4) * R + (1 / 4) * R + (1 / 4) * R := by gcongr
    _ < R := by linarith

theorem small_le {h η e : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (he : 0 ≤ e)
    (s4 : 16 * h ^ (1 - 6 * e - 44 * η) ≤ 1) :
    4 * (2 * (h ^ (-η)) ^ 44) * (h ^ (1 - 4 * e) / h ^ e + h) ≤ h ^ e := by
  have e1 : h ^ (1 - 4 * e) / h ^ e = h ^ (1 - 5 * e) := by
    rw [← Real.rpow_sub hh]; ring_nf
  have h2 : h ≤ h ^ (1 - 5 * e) := by
    have := Real.rpow_le_rpow_of_exponent_ge hh hh1 (show 1 - 5 * e ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have e2 : (h ^ (-η)) ^ 44 * h ^ (1 - 5 * e) = h ^ (1 - 6 * e - 44 * η) * h ^ e := by
    rw [rpow_npow hh, ← Real.rpow_add hh, ← Real.rpow_add hh]; ring_nf
  rw [e1]
  have hp : 0 ≤ (h ^ (-η)) ^ 44 := by positivity
  have hq : 0 ≤ h ^ e := (Real.rpow_pos_of_pos hh _).le
  calc 4 * (2 * (h ^ (-η)) ^ 44) * (h ^ (1 - 5 * e) + h)
      ≤ 4 * (2 * (h ^ (-η)) ^ 44) * (2 * h ^ (1 - 5 * e)) := by gcongr; linarith
    _ = 16 * ((h ^ (-η)) ^ 44 * h ^ (1 - 5 * e)) := by ring
    _ = 16 * h ^ (1 - 6 * e - 44 * η) * h ^ e := by rw [e2]; ring
    _ ≤ 1 * h ^ e := by gcongr
    _ = h ^ e := one_mul _

theorem count_le {h η e ε : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hle : e + 40 * η ≤ ε) :
    h ^ ε / h ^ 2 ≤ h ^ e * ((1 / h) ^ 2 / (h ^ (-η)) ^ 40) := by
  have e1 : h ^ e * ((1 / h) ^ 2 / (h ^ (-η)) ^ 40) = h ^ (e + 40 * η) / h ^ 2 := by
    rw [rpow_npow hh, mul_neg, Real.rpow_neg hh.le, Real.rpow_add hh]
    push_cast
    field_simp
  rw [e1]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hh hh1 hle) (by positivity)

theorem coeff_le {h η e ε : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (he : 0 ≤ e) (hη : 0 ≤ η)
    (s6 : 26 * h ^ (ε - 49 * η - e) ≤ 1) :
    h ^ (-η) * ((1 + 2 * (h ^ (-η)) ^ 2) *
      (4 * (2 * (h ^ (-η)) ^ 44) * (h ^ (-η)) ^ 2 / h ^ e) + 2 * (h ^ (-η)) ^ 2) ≤
      h ^ (-ε) := by
  have hK1 : 1 ≤ h ^ (-η) := K_ge_one hh hh1 hη
  have hpe : 0 < h ^ e := Real.rpow_pos_of_pos hh e
  have hpe1 : h ^ e ≤ 1 := Real.rpow_le_one hh.le hh1 he
  set K := h ^ (-η) with hK
  have hb : K * ((1 + 2 * K ^ 2) * (4 * (2 * K ^ 44) * K ^ 2 / h ^ e) + 2 * K ^ 2) ≤
      26 * K ^ 49 / h ^ e := by
    rw [show K * ((1 + 2 * K ^ 2) * (4 * (2 * K ^ 44) * K ^ 2 / h ^ e) + 2 * K ^ 2) =
      (8 * K ^ 47 * (1 + 2 * K ^ 2) + 2 * K ^ 3 * h ^ e) / h ^ e by field_simp; ring]
    rw [div_le_div_iff_of_pos_right hpe]
    have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK1
    have hK47 : 0 ≤ K ^ 47 := by positivity
    have h1 : 8 * K ^ 47 * (1 + 2 * K ^ 2) ≤ 24 * K ^ 49 := by
      have : 8 * K ^ 47 * (1 + 2 * K ^ 2) ≤ 8 * K ^ 47 * (3 * K ^ 2) := by gcongr; linarith
      calc _ ≤ 8 * K ^ 47 * (3 * K ^ 2) := this
        _ = 24 * K ^ 49 := by ring
    have h2 : 2 * K ^ 3 * h ^ e ≤ 2 * K ^ 49 := by
      have : K ^ 3 ≤ K ^ 49 := pow_le_pow_right₀ hK1 (by norm_num)
      have hK3 : 0 ≤ K ^ 3 := by positivity
      nlinarith
    linarith
  have e3 : 26 * K ^ 49 / h ^ e = 26 * h ^ (ε - 49 * η - e) * h ^ (-ε) := by
    rw [hK, rpow_npow hh, mul_assoc 26 (h ^ (ε - 49 * η - e)), ← Real.rpow_add hh, mul_div_assoc,
      ← Real.rpow_sub hh]
    congr 2
    push_cast
    ring
  calc _ ≤ 26 * K ^ 49 / h ^ e := hb
    _ = 26 * h ^ (ε - 49 * η - e) * h ^ (-ε) := e3
    _ ≤ 1 * h ^ (-ε) := mul_le_mul_of_nonneg_right s6 (Real.rpow_pos_of_pos hh _).le
    _ = h ^ (-ε) := one_mul _

theorem error_le {h η e ε : ℝ} (hh : 0 < h) (s7 : 32 * h ^ (ε - 6 * e - 47 * η) ≤ 1) :
    h ^ (-η) * (16 * (2 * (h ^ (-η)) ^ 44) * (h ^ (-η)) ^ 2 * h ^ (1 - 4 * e) /
      (h ^ e * h ^ e)) ≤ h ^ (1 - ε) := by
  have e1 : h ^ (-η) * (16 * (2 * (h ^ (-η)) ^ 44) * (h ^ (-η)) ^ 2 * h ^ (1 - 4 * e) /
      (h ^ e * h ^ e)) = 32 * h ^ (ε - 6 * e - 47 * η) * h ^ (1 - ε) := by
    rw [rpow_npow hh, rpow_npow hh, ← Real.rpow_add hh e e, mul_assoc 32, ← Real.rpow_add hh]
    rw [show h ^ (-η) * (16 * (2 * h ^ ((44 : ℕ) * -η)) * h ^ ((2 : ℕ) * -η) * h ^ (1 - 4 * e) /
        h ^ (e + e)) = 32 * (h ^ (-η) * h ^ ((44 : ℕ) * -η) * h ^ ((2 : ℕ) * -η) *
          h ^ (1 - 4 * e) / h ^ (e + e)) by ring]
    rw [← Real.rpow_add hh, ← Real.rpow_add hh, ← Real.rpow_add hh, ← Real.rpow_sub hh]
    congr 2
    push_cast
    ring
  rw [e1]
  calc 32 * h ^ (ε - 6 * e - 47 * η) * h ^ (1 - ε) ≤ 1 * h ^ (1 - ε) :=
        mul_le_mul_of_nonneg_right s7 (Real.rpow_pos_of_pos hh _).le
    _ = h ^ (1 - ε) := one_mul _

/-! ### The budget -/

/-- The numerical inequalities of the final assembly at the mesh `h`, with loss `K = h^(-η)`. -/
structure Budget (h η e e₀ ε η₀ h₁ c C₀ : ℝ) (m k n : ℕ) : Prop where
  pos : 0 < h
  le_one : h ≤ 1
  lt_h₁ : h < h₁
  K_ge : 2 ^ 20 ≤ h ^ (-η)
  K_ge_c : 1 / c ≤ h ^ (-η)
  K_ge_C₀ : C₀ ≤ h ^ (-η)
  K_flat : (h ^ (-η)) ^ 172 ≤ h ^ (-η₀)
  budget : (2 * (h ^ (-η)) ^ 44 * (h ^ e + h)) ^ m + (m : ℝ) * (h ^ e) ^ (m - 1) +
      (10 + 8 * (h ^ (-η)) ^ 2) / h ^ (1 - 4 * e) * (60 * h ^ (1 - e₀)) ^ 2 <
      1 / (closureConst ((h ^ (-η)) ^ 200) 27 m k n * (1 / h))
  small : 4 * (2 * (h ^ (-η)) ^ 44) * (h ^ (1 - 4 * e) / h ^ e + h) ≤ h ^ e
  count : h ^ ε / h ^ 2 ≤ h ^ e * ((1 / h) ^ 2 / (h ^ (-η)) ^ 40)
  coeff : h ^ (-η) * ((1 + 2 * (h ^ (-η)) ^ 2) *
      (4 * (2 * (h ^ (-η)) ^ 44) * (h ^ (-η)) ^ 2 / h ^ e) + 2 * (h ^ (-η)) ^ 2) ≤ h ^ (-ε)
  error : h ^ (-η) * (16 * (2 * (h ^ (-η)) ^ 44) * (h ^ (-η)) ^ 2 * h ^ (1 - 4 * e) /
      (h ^ e * h ^ e)) ≤ h ^ (1 - ε)

/-- The budget holds for all small `h`, under linear constraints on the fixed exponents. -/
theorem eventually_budget {η e e₀ ε η₀ h₁ c C₀ : ℝ} {m k n : ℕ}
    (he : 0 < e) (he1 : e ≤ 1 / 100) (heε : 100 * e ≤ ε) (he₀e : 10 * e₀ ≤ e)
    (hm : 2 ≤ m) (hme : 3 ≤ ((m : ℝ) - 1) * e) (hη : 0 < η) (hηη₀ : 172 * η ≤ η₀)
    (hηe : (((200 * closureDeg 27 m k n : ℕ) : ℝ) + 44 * m + 2) * η ≤ e) (hh₁ : 0 < h₁) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), Budget h η e e₀ ε η₀ h₁ c C₀ m k n := by
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = 200 * closureDeg 27 m k n := ⟨_, rfl⟩
  rw [← hPdef] at hηe
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = closureConst 1 27 m k n := ⟨_, rfl⟩
  have hc₁ : 0 < c₁ := hc₁def ▸ closureConst_one_pos 27 m k n
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmη : 0 ≤ (m : ℝ) * η := by positivity
  have hPη : 0 ≤ (P : ℝ) * η := by positivity
  have hδ₁ : 0 < (m : ℝ) * (e - 44 * η) - (1 + (P : ℝ) * η) := by nlinarith
  have hδ₂ : 0 < e * ((m : ℝ) - 1) - (1 + (P : ℝ) * η) := by nlinarith
  have hδ₃ : 0 < 4 * e - 2 * e₀ - 2 * η - (P : ℝ) * η := by nlinarith
  have hδ₄ : 0 < 1 - 6 * e - 44 * η := by nlinarith
  have hδ₆ : 0 < ε - 49 * η - e := by nlinarith
  have hδ₇ : 0 < ε - 6 * e - 47 * η := by nlinarith
  have hcount : e + 40 * η ≤ ε := by nlinarith
  filter_upwards [eventually_pos_le_one, eventually_lt_of_pos hh₁,
    eventually_le_rpow_neg (2 ^ 20) hη, eventually_le_rpow_neg (1 / c) hη,
    eventually_le_rpow_neg C₀ hη,
    eventually_mul_rpow_le (4 ^ m * c₁) hδ₁ (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_mul_rpow_le ((m : ℝ) * c₁) hδ₂ (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_mul_rpow_le (64800 * c₁) hδ₃ (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_mul_rpow_le 16 hδ₄ one_pos, eventually_mul_rpow_le 26 hδ₆ one_pos,
    eventually_mul_rpow_le 32 hδ₇ one_pos] with h h01 hlt hK1 hK2 hK3 s1 s2 s3 s4 s6 s7
  obtain ⟨hh, hh1⟩ := h01
  refine ⟨hh, hh1, hlt, hK1, hK2, hK3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rpow_npow hh]
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by push_cast; linarith)
  · refine budget_le hh hh1 (by linarith) hη.le (by omega) hc₁ ?_ s1 s2 s3
    rw [closureConst_eq, ← pow_mul, hc₁def, hPdef]
  · exact small_le hh hh1 he.le s4
  · exact count_le hh hh1 hcount
  · exact coeff_le hh hh1 he.le hη.le s6
  · exact error_le hh s7

end

end Submission.Obl.k4_retained_edge_planar_rigidity
