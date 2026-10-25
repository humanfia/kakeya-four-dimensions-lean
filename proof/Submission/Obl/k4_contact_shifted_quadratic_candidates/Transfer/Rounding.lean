/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/Rounding.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.PreparedModel

/-!
# Labels on a finite depth grid

The horizontal atlas asks for true labels at every depth `s` in `[R⁻¹, U]`.
The residual model provides labels only at finitely many grid depths; a
depth is served by the labels of the grid depth just below it.

`LabelLevel` collects the label fields at one depth. `AtlasBody` is the body of
the frozen horizontal atlas at one index and depth, for given label fields
and a given subpower constant. Rounding a depth down by at most `η` costs the
factor `N ^ (2 * η + κ * η)` in that constant (`atlasBody_round`).
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

/-- The label fields of the atlas at one depth. -/
structure LabelLevel (α : Type) where
  n : ℕ
  T : ℕ
  j : Fin n → Fin (2 ^ T)
  A : Fin n → Set α
  B : Fin n → Set α
  c : Fin n → Fin 5 → ℝ
  F : Fin n → MvPolynomial (Fin 4) ℝ

/-- The horizontal atlas body at index `k` and depth `s` for the label fields
`lv` and the constant `K`; all other data are those of `cfg`. -/
def AtlasBody {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (R s : ℝ)
    (lv : LabelLevel α) (K : ℝ) : Prop :=
  (fun (q : ℝ) (a g : ℝ → ℝ) => cfg.N k ^ (cfg.κ * s) / K ≤ (2 : ℝ) ^ lv.T ∧ (2 : ℝ) ^ lv.T ≤ K * cfg.N k ^ (cfg.κ * s) ∧ (∀ i, MeasurableSet (lv.A i) ∧ MeasurableSet (lv.B i) ∧ lv.B i ⊆ lv.A i) ∧ (∀ i i', i ≠ i' → lv.j i = lv.j i' → Disjoint (lv.A i) (lv.A i')) ∧ (∀ i, ENNReal.ofReal (a s ^ cfg.d * q ^ 2 * g s / K) ≤ cfg.ν k (lv.A i) ∧ cfg.ν k (lv.A i) ≤ ENNReal.ofReal (K * a s ^ cfg.d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / K) * cfg.ν k (lv.A i) ≤ cfg.μ k (lv.B i ×ˢ Data.I lv.T (lv.j i)) ∧ (∀ e, |lv.c i e| ≤ K) ∧ (lv.F i).totalDegree ≤ 2 ∧ (∀ l ∈ lv.A i, ∀ t ∈ Data.I lv.T (lv.j i), |(cfg.x k l t) 1 - lv.c i 0 - t * lv.c i 1| ≤ K * q ∧ |(cfg.x k l t) 2 - lv.c i 2 - t * lv.c i 3 - lv.c i 4 * (cfg.x k l t) 1| ≤ K * q * g s ∧ |cfg.b k l 4 - lv.c i 3 - lv.c i 4 * cfg.b k l 3| ≤ K * g s) ∧ (∀ l ∈ lv.B i, cfg.fit k K (a s) (lv.F i) l (Data.I lv.T (lv.j i))) ∧ (∀ᵐ p ∂cfg.μ k, p.1 ∈ lv.B i → p.2 ∈ Data.I lv.T (lv.j i) → K⁻¹ ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (lv.F i))|) ∧ ((true : Bool) = true → cfg.P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) ∧ |lv.c i 3 + lv.c i 0 + ((lv.j i : ℕ) + (1 : ℝ) / 2) * q * lv.c i 1| + |lv.c i 4 - ((lv.j i : ℕ) + (1 : ℝ) / 2) * q| ≤ K * q ∧ (∃ L : Fin 4 → ℝ, lv.F i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ K * (1 + a s / q ^ 2) ∧ ∀ l ∈ lv.B i, ∀ t ∈ Data.I lv.T (lv.j i), |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ K * (1 + a s / q)))) ∧ (∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ lv.B i ∧ p.2 ∈ Data.I lv.T (lv.j i)) ∧ (∀ (i : Fin lv.n) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → cfg.μ k {p | p.1 ∈ lv.B i ∧ p.2 ∈ Data.I lv.T (lv.j i) ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K * q) * cfg.ν k (lv.A i) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(lv.T : ℤ))) (fun s => cfg.N k ^ (-s)) (fun s => cfg.N k ^ (-cfg.ℓ * s))

/-- The label fields of `cfg` at index `k` and depth `s`. -/
def levelOf {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (s : ℝ) :
    LabelLevel α :=
  ⟨cfg.n k s, cfg.T k s, cfg.j k s, cfg.A k s, cfg.B k s, cfg.c k s, cfg.F k s⟩

/-- The frozen atlas is the eventual atlas body at every depth. -/
theorem atlas_iff_body {α : Type} [MeasurableSpace α] (cfg : Data α) :
    cfg.Atlas ↔ ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U →
      AtlasBody cfg k R s (levelOf cfg k s) (cfg.K k) :=
  Iff.rfl

/-- The cost of rounding a depth down by `η`. -/
def roundCost {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (η : ℝ) : ℝ :=
  cfg.N k ^ ((1 + cfg.d + cfg.κ + cfg.ℓ) * η)

theorem one_le_roundCost {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ)
    {η : ℝ} (hN : 1 ≤ cfg.N k) (hd : 0 ≤ cfg.d) (hκ : 0 ≤ cfg.κ) (hℓ : 0 ≤ cfg.ℓ)
    (hη : 0 ≤ η) : 1 ≤ roundCost cfg k η :=
  Real.one_le_rpow hN (by positivity)

/-- Elementary comparisons for rounding a depth `s` down to `σ ≤ s ≤ σ + η`. -/
theorem rpow_round_le {N x y c η : ℝ} (hN : 1 ≤ N) (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hxy : x ≤ y) (hyx : y ≤ x + η) {C : ℝ} (hC : c ≤ C) :
    N ^ (-c * x) ≤ N ^ (C * η) * N ^ (-c * y) := by
  have hN0 : 0 < N := by linarith
  rw [← Real.rpow_add hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN
  nlinarith

/-- Rounding a depth down to the grid. -/
theorem atlasBody_round {α : Type} [MeasurableSpace α] (cfg : Data α) {k : ℕ}
    {R σ s η K : ℝ} {lv : LabelLevel α} (hN : 1 ≤ cfg.N k) (hd : 0 ≤ cfg.d)
    (hκ : 0 ≤ cfg.κ) (hℓ : 0 ≤ cfg.ℓ) (hK : 0 < K) (hη : 0 ≤ η)
    (hσs : σ ≤ s) (hsσ : s ≤ σ + η) {K' : ℝ} (hK' : K * roundCost cfg k η ≤ K')
    (h : AtlasBody cfg k R σ lv K) :
    AtlasBody cfg k R s lv K' := by
  have hN0 : 0 < cfg.N k := by linarith
  set W := roundCost cfg k η with hWdef
  have hW : 1 ≤ W := one_le_roundCost cfg k hN hd hκ hℓ hη
  have hW0 : 0 < W := by linarith
  have hKW1 : K ≤ K * W := le_mul_of_one_le_right hK.le hW
  have hKW0 : 0 < K * W := by positivity
  have hKW : K ≤ K' := hKW1.trans hK'
  -- elementary comparisons of the three scales
  have ha_le : cfg.N k ^ (-s) ≤ cfg.N k ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hg_le : cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.N k ^ (-cfg.ℓ * σ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have ha_up : cfg.N k ^ (-σ) ≤ W * cfg.N k ^ (-s) := by
    have := rpow_round_le (c := 1) hN zero_le_one hη hσs hsσ
      (C := 1 + cfg.d + cfg.κ + cfg.ℓ) (by linarith)
    simpa [W, roundCost] using this
  have hg_up : cfg.N k ^ (-cfg.ℓ * σ) ≤ W * cfg.N k ^ (-cfg.ℓ * s) :=
    rpow_round_le hN hℓ hη hσs hsσ (by linarith)
  have hadg_up : (cfg.N k ^ (-σ)) ^ cfg.d * cfg.N k ^ (-cfg.ℓ * σ) ≤
      W * ((cfg.N k ^ (-s)) ^ cfg.d * cfg.N k ^ (-cfg.ℓ * s)) := by
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
      ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
      hWdef, roundCost, ← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith
  have hadg_le : (cfg.N k ^ (-s)) ^ cfg.d * cfg.N k ^ (-cfg.ℓ * s) ≤
      (cfg.N k ^ (-σ)) ^ cfg.d * cfg.N k ^ (-cfg.ℓ * σ) := by
    have h1 : (cfg.N k ^ (-s)) ^ cfg.d ≤ (cfg.N k ^ (-σ)) ^ cfg.d :=
      Real.rpow_le_rpow (by positivity) ha_le hd
    exact mul_le_mul h1 hg_le (by positivity) (by positivity)
  have hκs : cfg.N k ^ (cfg.κ * s) ≤ W * cfg.N k ^ (cfg.κ * σ) := by
    rw [hWdef, roundCost, ← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith
  have hκσ : cfg.N k ^ (cfg.κ * σ) ≤ cfg.N k ^ (cfg.κ * s) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  set q : ℝ := (2 : ℝ) ^ (-(lv.T : ℤ)) with hq
  have hq0 : 0 < q := by positivity
  obtain ⟨hT1, hT2, hmeas, hdisj, hlab, hcov, hjoint⟩ := h
  refine ⟨?_, ?_, hmeas, hdisj, ?_, hcov, ?_⟩
  · calc
      cfg.N k ^ (cfg.κ * s) / K' ≤ cfg.N k ^ (cfg.κ * s) / (K * W) :=
        div_le_div_of_nonneg_left (by positivity) hKW0 hK'
      _ ≤ W * cfg.N k ^ (cfg.κ * σ) / (K * W) :=
        div_le_div_of_nonneg_right hκs hKW0.le
      _ = cfg.N k ^ (cfg.κ * σ) / K := by field_simp
      _ ≤ _ := hT1
  · calc
      (2 : ℝ) ^ lv.T ≤ K * cfg.N k ^ (cfg.κ * σ) := hT2
      _ ≤ K' * cfg.N k ^ (cfg.κ * s) :=
        mul_le_mul hKW hκσ (by positivity) (hKW0.le.trans hK')
  · intro i
    obtain ⟨hfl, hce, hmass, hc, hdeg, hrows, hfit, hder, hhor⟩ := hlab i
    refine ⟨?_, ?_, ?_, fun e => (hc e).trans hKW, hdeg, ?_, ?_, ?_, ?_⟩
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hfl
      have : (cfg.N k ^ (-s)) ^ cfg.d * q ^ 2 * cfg.N k ^ (-cfg.ℓ * s) ≤
          (cfg.N k ^ (-σ)) ^ cfg.d * q ^ 2 * cfg.N k ^ (-cfg.ℓ * σ) := by
        have := mul_le_mul_of_nonneg_left hadg_le (sq_nonneg q)
        nlinarith
      calc
        (cfg.N k ^ (-s)) ^ cfg.d * q ^ 2 * cfg.N k ^ (-cfg.ℓ * s) / K' ≤
            (cfg.N k ^ (-σ)) ^ cfg.d * q ^ 2 * cfg.N k ^ (-cfg.ℓ * σ) / K' :=
          div_le_div_of_nonneg_right this (hKW0.le.trans hK')
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hK hKW
    · refine hce.trans (ENNReal.ofReal_le_ofReal ?_)
      have := mul_le_mul_of_nonneg_left hadg_up (by positivity : (0 : ℝ) ≤ K * q ^ 2)
      have h2 : 0 ≤ (cfg.N k ^ (-s)) ^ cfg.d * cfg.N k ^ (-cfg.ℓ * s) * q ^ 2 := by
        positivity
      have h3 := mul_le_mul_of_nonneg_right hK' h2
      nlinarith
    · refine le_trans ?_ hmass
      gcongr
    · intro l hl t ht
      obtain ⟨r1, r2, r3⟩ := hrows l hl t ht
      refine ⟨r1.trans (by nlinarith), r2.trans ?_, r3.trans ?_⟩
      · have := mul_le_mul_of_nonneg_left hg_up (by positivity : (0 : ℝ) ≤ K * q)
        have h3 := mul_le_mul_of_nonneg_right hK'
          (by positivity : (0 : ℝ) ≤ q * cfg.N k ^ (-cfg.ℓ * s))
        nlinarith
      · have := mul_le_mul_of_nonneg_left hg_up hK.le
        have h3 := mul_le_mul_of_nonneg_right hK'
          (by positivity : (0 : ℝ) ≤ cfg.N k ^ (-cfg.ℓ * s))
        nlinarith
    · intro l hl t ht
      obtain ⟨f1, f2, f3⟩ := hfit l hl t ht
      refine ⟨f1.trans ?_, f2.trans hKW, f3.trans ?_⟩
      · have := mul_le_mul_of_nonneg_left ha_up hK.le
        have h3 := mul_le_mul_of_nonneg_right hK'
          (by positivity : (0 : ℝ) ≤ cfg.N k ^ (-s))
        nlinarith
      · have hs0 : 0 < cfg.N k ^ (-s) := by positivity
        calc
          K / cfg.N k ^ (-σ) ≤ K / cfg.N k ^ (-s) :=
            div_le_div_of_nonneg_left hK.le hs0 ha_le
          _ ≤ K' / cfg.N k ^ (-s) := div_le_div_of_nonneg_right hKW hs0.le
    · filter_upwards [hder] with p hp h1 h2
      exact (inv_anti₀ hK hKW).trans (hp h1 h2)
    · intro htrue
      obtain ⟨hP, hcon, hcs, L, hF, hL3, hL⟩ := hhor htrue
      have hone : 1 + cfg.N k ^ (-σ) / q ^ 2 ≤ W * (1 + cfg.N k ^ (-s) / q ^ 2) := by
        have h1 : cfg.N k ^ (-σ) / q ^ 2 ≤ W * (cfg.N k ^ (-s) / q ^ 2) := by
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_right ha_up (by positivity)
        rw [mul_add, mul_one]
        exact add_le_add hW h1
      have hone' : 1 + cfg.N k ^ (-σ) / q ≤ W * (1 + cfg.N k ^ (-s) / q) := by
        have h1 : cfg.N k ^ (-σ) / q ≤ W * (cfg.N k ^ (-s) / q) := by
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_right ha_up hq0.le
        rw [mul_add, mul_one]
        exact add_le_add hW h1
      refine ⟨hP, hcon, hcs.trans (mul_le_mul_of_nonneg_right hKW hq0.le), L, hF,
        hL3.trans ?_, fun l hl t ht => ?_⟩
      · calc
          K * (1 + cfg.N k ^ (-σ) / q ^ 2) ≤ K * (W * (1 + cfg.N k ^ (-s) / q ^ 2)) :=
            mul_le_mul_of_nonneg_left hone hK.le
          _ = K * W * (1 + cfg.N k ^ (-s) / q ^ 2) := by ring
          _ ≤ K' * (1 + cfg.N k ^ (-s) / q ^ 2) :=
            mul_le_mul_of_nonneg_right hK' (by positivity)
      · refine (hL l hl t ht).trans ?_
        calc
          K * (1 + cfg.N k ^ (-σ) / q) ≤ K * (W * (1 + cfg.N k ^ (-s) / q)) :=
            mul_le_mul_of_nonneg_left hone' hK.le
          _ = K * W * (1 + cfg.N k ^ (-s) / q) := by ring
          _ ≤ K' * (1 + cfg.N k ^ (-s) / q) :=
            mul_le_mul_of_nonneg_right hK' (by positivity)
  · intro i v v₀ hv1 hv2
    refine (hjoint i v v₀ hv1 hv2).trans ?_
    gcongr

/-- Every conjunct of the atlas body is weaker for a larger constant. -/
theorem atlasBody_mono {α : Type} [MeasurableSpace α] (cfg : Data α) {k : ℕ}
    {R s K K' : ℝ} {lv : LabelLevel α} (hN : 1 ≤ cfg.N k) (hd : 0 ≤ cfg.d)
    (hκ : 0 ≤ cfg.κ) (hℓ : 0 ≤ cfg.ℓ) (hK : 0 < K) (hKK : K ≤ K')
    (h : AtlasBody cfg k R s lv K) : AtlasBody cfg k R s lv K' :=
  atlasBody_round cfg hN hd hκ hℓ hK le_rfl le_rfl (by simp)
    (by simpa [roundCost] using hKK) h

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
