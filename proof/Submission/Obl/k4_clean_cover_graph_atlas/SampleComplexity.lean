import Submission.Obl.k4_clean_cover_graph_atlas.Entries

/-!
# Complexity budgets of one sample

One output exponent `Mc` and one threshold `N0`, depending only on fixed power caps, dominate
every polynomial size budget of the concrete assembly: the representative inverse scale
`(1 + 80 (ηfine + Jbin)/B) (A/B + A²⁰/B²)`, the scale `B A + 4 N^Mg`, the source budget
`8 N^Mg`, the number of entries `n 2^s₀ (2K+2)² 4`, and `2^s₀`, `K`. Here `ηfine = U δfine
A^(Cs+1)` with `A ≤ N^Ma`, `U ≤ N^Mu`, `δfine ≤ 1`, `B, B⁻¹ ≤ N^Mpr`, `Jbin ≤ Jconst`,
`n ≤ N^Mg`, `2^s₀ ≤ N^Ms`, `K ≤ N^Mk`. Every term is a constant times a nonnegative power of `N`;
`Mc` is the ceiling of the sum of all exponents plus slack and `N0` absorbs the constants.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- A real power below a natural power when the exponents compare and `N ≥ 1`. -/
theorem complexity_rpow_le_pow {N : ℝ} (hN : 1 ≤ N) {a : ℝ} {k : ℕ} (h : a ≤ k) :
    N ^ a ≤ N ^ k := by
  rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hN h

theorem complexity_pow_eq_rpow (N : ℝ) (k : ℕ) : N ^ k = N ^ (k : ℝ) :=
  (Real.rpow_natCast N k).symm

/-- A constant times `N^a` is at most `N^(a+1)` once `N` is at least the constant. -/
theorem complexity_const_mul_le {N c a : ℝ} (hN : 1 ≤ N) (hc : c ≤ N) (_hc0 : 0 ≤ c) :
    c * N ^ a ≤ N ^ (a + 1) := by
  have hN0 : 0 < N := by linarith
  rw [Real.rpow_add hN0, Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hN0.le _)

theorem complexity_card_entry (n s₀ K : ℕ) :
    Fintype.card (Entry n s₀ K) = n * (2 ^ s₀ * ((2 * K + 2) ^ 2 * (2 * 2))) := by
  unfold Entry
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_bool]

/-- **Complexity budgets.** -/
theorem complexity_budget (Ma Mu Ms Mk Jconst : ℝ) (Cs Mpr Mg : ℕ) (hMa : 0 ≤ Ma)
    (hMu : 0 ≤ Mu) (hMs : 0 ≤ Ms) (hMk : 0 ≤ Mk) (hJ : 0 ≤ Jconst) :
    ∃ (Mc : ℕ) (N0 : ℝ), 2 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      (∀ A U δf B Jbin : ℝ, 2 ≤ A → A ≤ N ^ Ma → 0 ≤ U → U ≤ N ^ Mu → 0 < δf → δf ≤ 1 →
        0 < B → B ≤ N ^ Mpr → B⁻¹ ≤ N ^ Mpr → 0 ≤ Jbin → Jbin ≤ Jconst →
        (1 + 80 * ((U * δf * A ^ ((Cs : ℝ) + 1) + Jbin) / B)) *
            (A / B + A ^ (20 : ℕ) / B ^ 2) ≤ N ^ Mc ∧
          B * A + 4 * N ^ Mg ≤ N ^ Mc) ∧
      8 * N ^ Mg ≤ N ^ Mc ∧
      (∀ n s₀ K : ℕ, (n : ℝ) ≤ N ^ Mg → (2 : ℝ) ^ s₀ ≤ N ^ Ms → (K : ℝ) ≤ N ^ Mk →
        (Fintype.card (Entry n s₀ K) : ℝ) ≤ N ^ Mc ∧ (2 : ℝ) ^ s₀ ≤ N ^ Mc ∧
          (K : ℝ) ≤ N ^ Mc) := by
  -- exponents
  set X : ℝ := (Mpr : ℝ) + Mu + Ma * ((Cs : ℝ) + 1) with hX
  set Y : ℝ := 20 * Ma + 2 * (Mpr : ℝ) with hY
  set E : ℝ := X + Y + (Mg : ℝ) + Ms + 2 * Mk + (Mpr : ℝ) + Ma + 10 with hE
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hE0 : 0 ≤ E := by positivity
  set c₁ : ℝ := 2 * (81 + 80 * Jconst) with hc₁
  refine ⟨⌈E⌉₊, max 2 (c₁ + 100), le_max_left _ _, fun N hN0 => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN0
  have hNc : c₁ + 100 ≤ N := (le_max_right _ _).trans hN0
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hEMc : E ≤ (⌈E⌉₊ : ℝ) := Nat.le_ceil E
  -- monotonicity of powers of `N`
  have hmono : ∀ {a b : ℝ}, a ≤ b → N ^ a ≤ N ^ b := fun h =>
    Real.rpow_le_rpow_of_exponent_le hN1 h
  have hone : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ N ^ a := fun h => Real.one_le_rpow hN1 h
  have htoMc : ∀ {a : ℝ}, a ≤ E → N ^ a ≤ N ^ ⌈E⌉₊ := fun h =>
    complexity_rpow_le_pow hN1 (h.trans hEMc)
  refine ⟨fun A U δf B Jbin hA hAN hU hUN hδ hδ1 hB hBN hBinv hJb hJbc => ?_, ?_, ?_⟩
  · have hA0 : 0 ≤ A := by linarith
    have hBN' : B ≤ N ^ (Mpr : ℝ) := by rw [Real.rpow_natCast]; exact hBN
    have hBinv' : B⁻¹ ≤ N ^ (Mpr : ℝ) := by rw [Real.rpow_natCast]; exact hBinv
    -- `ηfine ≤ N^(Mu + Ma (Cs+1))`
    have hApow : A ^ ((Cs : ℝ) + 1) ≤ N ^ (Ma * ((Cs : ℝ) + 1)) := by
      rw [Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow hA0 hAN (by positivity)
    have heta : U * δf * A ^ ((Cs : ℝ) + 1) ≤ N ^ (Mu + Ma * ((Cs : ℝ) + 1)) := by
      rw [Real.rpow_add hNpos]
      calc U * δf * A ^ ((Cs : ℝ) + 1) ≤ U * 1 * A ^ ((Cs : ℝ) + 1) := by gcongr
        _ = U * A ^ ((Cs : ℝ) + 1) := by ring
        _ ≤ N ^ Mu * N ^ (Ma * ((Cs : ℝ) + 1)) := by gcongr
    -- the first factor
    have hfirst : 1 + 80 * ((U * δf * A ^ ((Cs : ℝ) + 1) + Jbin) / B) ≤
        (81 + 80 * Jconst) * N ^ X := by
      have hdiv : (U * δf * A ^ ((Cs : ℝ) + 1) + Jbin) / B ≤
          (N ^ (Mu + Ma * ((Cs : ℝ) + 1)) + Jconst) * N ^ (Mpr : ℝ) := by
        rw [div_eq_mul_inv]
        have h0 : 0 ≤ U * δf * A ^ ((Cs : ℝ) + 1) + Jbin := by positivity
        exact mul_le_mul (by linarith) hBinv' (inv_nonneg.mpr hB.le) (by positivity)
      have hXa : N ^ (Mu + Ma * ((Cs : ℝ) + 1)) * N ^ (Mpr : ℝ) = N ^ X := by
        rw [← Real.rpow_add hNpos, hX]; ring_nf
      have hMprX : N ^ (Mpr : ℝ) ≤ N ^ X := hmono (by rw [hX]; nlinarith)
      have h1X : 1 ≤ N ^ X := hone hX0
      calc 1 + 80 * ((U * δf * A ^ ((Cs : ℝ) + 1) + Jbin) / B)
          ≤ 1 + 80 * ((N ^ (Mu + Ma * ((Cs : ℝ) + 1)) + Jconst) * N ^ (Mpr : ℝ)) := by
            gcongr
        _ = 1 + 80 * N ^ X + 80 * Jconst * N ^ (Mpr : ℝ) := by rw [← hXa]; ring
        _ ≤ N ^ X + 80 * N ^ X + 80 * Jconst * N ^ X := by gcongr
        _ = (81 + 80 * Jconst) * N ^ X := by ring
    -- the second factor
    have hsecond : A / B + A ^ (20 : ℕ) / B ^ 2 ≤ 2 * N ^ Y := by
      have h1 : A / B ≤ N ^ Y := by
        rw [div_eq_mul_inv]
        have hm := mul_le_mul hAN hBinv' (inv_nonneg.mpr hB.le) (Real.rpow_nonneg hNpos.le Ma)
        calc A * B⁻¹ ≤ N ^ Ma * N ^ (Mpr : ℝ) := hm
          _ = N ^ (Ma + Mpr) := by rw [← Real.rpow_add hNpos]
          _ ≤ N ^ Y := hmono (by rw [hY]; nlinarith)
      have h2 : A ^ (20 : ℕ) / B ^ 2 ≤ N ^ Y := by
        rw [div_eq_mul_inv, ← inv_pow]
        have hA20 : A ^ (20 : ℕ) ≤ N ^ (20 * Ma) := by
          have h1 : A ^ (20 : ℕ) ≤ (N ^ Ma) ^ (20 : ℕ) := pow_le_pow_left₀ hA0 hAN 20
          have h2 : (N ^ Ma) ^ (20 : ℕ) = N ^ (20 * Ma) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
          rw [← h2]; exact h1
        have hB2 : B⁻¹ ^ 2 ≤ N ^ (2 * (Mpr : ℝ)) := by
          rw [mul_comm, Real.rpow_mul hNpos.le]
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          exact pow_le_pow_left₀ (inv_nonneg.mpr hB.le) hBinv' 2
        calc A ^ (20 : ℕ) * B⁻¹ ^ 2 ≤ N ^ (20 * Ma) * N ^ (2 * (Mpr : ℝ)) :=
              mul_le_mul hA20 hB2 (by positivity) (by positivity)
          _ = N ^ Y := by rw [← Real.rpow_add hNpos]
      linarith
    constructor
    · calc (1 + 80 * ((U * δf * A ^ ((Cs : ℝ) + 1) + Jbin) / B)) *
            (A / B + A ^ (20 : ℕ) / B ^ 2)
          ≤ ((81 + 80 * Jconst) * N ^ X) * (2 * N ^ Y) := by
            have h0 : 0 ≤ A / B + A ^ (20 : ℕ) / B ^ 2 := by positivity
            exact mul_le_mul hfirst hsecond h0 (by positivity)
        _ = c₁ * N ^ (X + Y) := by
            rw [show N ^ (X + Y) = N ^ X * N ^ Y from Real.rpow_add hNpos X Y, hc₁]; ring
        _ ≤ N ^ (X + Y + 1) := complexity_const_mul_le hN1 (by linarith) hc₁0
        _ ≤ N ^ ⌈E⌉₊ := htoMc (by
            rw [hE]; linarith [(Nat.cast_nonneg Mpr : (0 : ℝ) ≤ Mpr),
              (Nat.cast_nonneg Mg : (0 : ℝ) ≤ Mg)])
    · have hBA : B * A ≤ N ^ ((Mpr : ℝ) + Ma) := by
        rw [Real.rpow_add hNpos]
        exact mul_le_mul hBN' hAN hA0 (by positivity)
      have hMg : N ^ Mg = N ^ (Mg : ℝ) := complexity_pow_eq_rpow N Mg
      set Z : ℝ := (Mpr : ℝ) + Ma + (Mg : ℝ) with hZ
      have hMg0 : (0 : ℝ) ≤ Mg := Nat.cast_nonneg Mg
      have hMpr0 : (0 : ℝ) ≤ Mpr := Nat.cast_nonneg Mpr
      have h1 : N ^ ((Mpr : ℝ) + Ma) ≤ N ^ Z := hmono (by rw [hZ]; linarith)
      have h2 : N ^ (Mg : ℝ) ≤ N ^ Z := hmono (by rw [hZ]; linarith)
      calc B * A + 4 * N ^ Mg ≤ N ^ Z + 4 * N ^ Z := by
            rw [hMg]; have := hBA.trans h1; linarith
        _ = 5 * N ^ Z := by ring
        _ ≤ N ^ (Z + 1) := complexity_const_mul_le hN1 (by linarith) (by norm_num)
        _ ≤ N ^ ⌈E⌉₊ := htoMc (by
            rw [hZ, hE]; linarith [(Nat.cast_nonneg Mpr : (0 : ℝ) ≤ Mpr)])
  · rw [complexity_pow_eq_rpow N Mg]
    calc 8 * N ^ (Mg : ℝ) ≤ N ^ ((Mg : ℝ) + 1) :=
          complexity_const_mul_le hN1 (by linarith) (by norm_num)
      _ ≤ N ^ ⌈E⌉₊ := htoMc (by
          rw [hE]; linarith [(Nat.cast_nonneg Mpr : (0 : ℝ) ≤ Mpr)])
  · intro n s₀ K hn hs hK
    have hMg : N ^ Mg = N ^ (Mg : ℝ) := complexity_pow_eq_rpow N Mg
    have hKN : (2 : ℝ) * K + 2 ≤ 4 * N ^ Mk := by
      have : 1 ≤ N ^ Mk := hone hMk
      linarith
    have hcard : (Fintype.card (Entry n s₀ K) : ℝ) ≤
        N ^ (Mg : ℝ) * (N ^ Ms * ((4 * N ^ Mk) ^ 2 * 4)) := by
      rw [complexity_card_entry]
      push_cast
      rw [← hMg]
      have h2K : (0 : ℝ) ≤ 2 * K + 2 := by positivity
      gcongr
    have heq : N ^ (Mg : ℝ) * (N ^ Ms * ((4 * N ^ Mk) ^ 2 * 4)) =
        64 * N ^ ((Mg : ℝ) + Ms + 2 * Mk) := by
      rw [Real.rpow_add hNpos, Real.rpow_add hNpos, mul_pow,
        ← Real.rpow_natCast (N ^ Mk) 2, ← Real.rpow_mul hNpos.le]
      push_cast
      ring_nf
    refine ⟨?_, ?_, ?_⟩
    · calc (Fintype.card (Entry n s₀ K) : ℝ) ≤ 64 * N ^ ((Mg : ℝ) + Ms + 2 * Mk) := by
            rw [← heq]; exact hcard
        _ ≤ N ^ ((Mg : ℝ) + Ms + 2 * Mk + 1) :=
            complexity_const_mul_le hN1 (by linarith) (by norm_num)
        _ ≤ N ^ ⌈E⌉₊ := htoMc (by
            rw [hE]; linarith [(Nat.cast_nonneg Mpr : (0 : ℝ) ≤ Mpr)])
    · exact hs.trans (htoMc (by
        rw [hE]; linarith [(Nat.cast_nonneg Mpr : (0 : ℝ) ≤ Mpr),
          (Nat.cast_nonneg Mg : (0 : ℝ) ≤ Mg)]))
    · exact hK.trans (htoMc (by
        rw [hE]; linarith [(Nat.cast_nonneg Mpr : (0 : ℝ) ≤ Mpr),
          (Nat.cast_nonneg Mg : (0 : ℝ) ≤ Mg)]))

end Submission.Obl.k4_clean_cover_graph_atlas
