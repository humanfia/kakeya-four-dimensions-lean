import Mathlib
import Submission.Obl.k4_horizontal_coefficient_count.LMSetup
import Submission.Obl.k4_critical_switching_state_preparation.PreparedModel

/-!
# The single-depth data at a large index

From the frozen hypotheses (written with the field names of the accepted
`Data` record of `k4_critical_switching_state_preparation`), at a fixed depth
`s` with `0 < s ≤ U`, `s < e₀`, every sufficiently large index carries a
`DepthData` satisfying `DepthData.Hyp`.
-/

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

open Submission.Obl.k4_critical_switching_state_preparation (Data)

variable {α : Type} [MeasurableSpace α]

/-- The true time-block length at depth `s`. -/
def blockLen (cfg : Data α) (k : ℕ) (s : ℝ) : ℝ := (2 : ℝ) ^ (-(cfg.T k s : ℤ))

/-- The affine fit of a true label, exactly as the atlas states it. -/
def AtlasFit (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) : Prop :=
  cfg.F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) +
      MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) +
      MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
      MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧
    |L 3| ≤ cfg.K k * (1 + cfg.N k ^ (-s) / blockLen cfg k s ^ 2) ∧
    ∀ l ∈ cfg.B k s i, ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
      |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤
        cfg.K k * (1 + cfg.N k ^ (-s) / blockLen cfg k s)

open Classical in
/-- A choice of the affine fit coefficients of a true label. -/
def atlasL (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Fin 4 → ℝ :=
  if h : ∃ L, AtlasFit cfg k s i L then Classical.choose h else 0

theorem atlasL_spec {cfg : Data α} {k : ℕ} {s : ℝ} {i : Fin (cfg.n k s)}
    (h : ∃ L, AtlasFit cfg k s i L) : AtlasFit cfg k s i (atlasL cfg k s i) := by
  classical
  rw [atlasL, dif_pos h]
  exact Classical.choose_spec h

/-- The single-depth data at index `k`. -/
def depthDataAt (cfg : Data α) (k : ℕ) (s : ℝ) : DepthData α where
  ν := cfg.ν k
  μ := cfg.μ k
  ρ := cfg.ρ k
  π := cfg.π k
  b := cfg.b k
  K := cfg.K k
  d := cfg.d
  a := cfg.N k ^ (-s)
  χ := cfg.N k ^ (-cfg.e₀)
  q := blockLen cfg k s
  g := cfg.N k ^ (-cfg.ℓ * s)
  w := cfg.N k ^ (-(2 * cfg.κ * s))
  T := cfg.T k s
  n := cfg.n k s
  j := cfg.j k s
  A := cfg.A k s
  B := cfg.B k s
  c := cfg.c k s
  L := atlasL cfg k s

theorem I_eq_tblock (T : ℕ) (j : Fin (2 ^ T)) :
    Data.I T j = tblock ((2 : ℝ) ^ (-(T : ℤ))) j := by
  unfold Submission.Obl.k4_critical_switching_state_preparation.Data.I tblock
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv, div_eq_mul_inv]

theorem x_one (cfg : Data α) (k : ℕ) (l : α) (t : ℝ) :
    (cfg.x k l t) 1 = X1 (cfg.b k l) t := by
  simp [Submission.Obl.k4_critical_switching_state_preparation.Data.x, X1]

theorem x_two (cfg : Data α) (k : ℕ) (l : α) (t : ℝ) :
    (cfg.x k l t) 2 = X2 (cfg.b k l) t := by
  simp [Submission.Obl.k4_critical_switching_state_preparation.Data.x, X2]

theorem x_three (cfg : Data α) (k : ℕ) (l : α) (t : ℝ) :
    (cfg.x k l t) 3 = X3 (cfg.b k l) t := by
  simp [Submission.Obl.k4_critical_switching_state_preparation.Data.x, X3]

theorem z_eq_iff (cfg : Data α) (k : ℕ) (r : ℝ) (p : α × ℝ) (n0 n1 n2 : ℤ) :
    cfg.z k (cfg.N k) r p = ![n0, n1, n2] ↔
      ⌊p.2 / cfg.N k ^ (-r)⌋ = n0 ∧ ⌊X1 (cfg.b k p.1) p.2 / cfg.N k ^ (-r)⌋ = n1 ∧
        ⌊X2 (cfg.b k p.1) p.2 / cfg.N k ^ (-r)⌋ = n2 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [Submission.Obl.k4_critical_switching_state_preparation.Data.z] at h0 h1 h2
    refine ⟨by simpa using h0, ?_, ?_⟩
    · simpa [x_one] using h1
    · simpa [x_two] using h2
  · rintro ⟨h0, h1, h2⟩
    funext e
    simp only [Submission.Obl.k4_critical_switching_state_preparation.Data.z]
    fin_cases e
    · simpa using h0
    · simpa [x_one] using h1
    · simpa [x_two] using h2

/-- The real scale relations of `DepthData.Hyp`. -/
theorem scale_relations {N K κ s e₀ : ℝ} {T : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K)
    (hse : s ≤ e₀)
    (hA1 : N ^ (κ * s) / K ≤ (2 : ℝ) ^ T) (hA2 : (2 : ℝ) ^ T ≤ K * N ^ (κ * s))
    (hK2 : K ^ 2 ≤ N ^ ((1 - 2 * κ) * s)) :
    N ^ (-e₀) ≤ N ^ (-s) ∧ N ^ (-s) ≤ ((2 : ℝ) ^ (-(T : ℤ))) ^ 2 ∧
      (2 : ℝ) ^ (-(T : ℤ)) * 2 ^ T = 1 ∧
      N ^ (-κ * s) ≤ K * (2 : ℝ) ^ (-(T : ℤ)) ∧ (2 : ℝ) ^ (-(T : ℤ)) ≤ K * N ^ (-κ * s) ∧
      ((2 : ℝ) ^ (-(T : ℤ))) ^ 2 ≤ K ^ 2 * N ^ (-(2 * κ * s)) ∧
      N ^ (-(2 * κ * s)) ≤ K ^ 2 * ((2 : ℝ) ^ (-(T : ℤ))) ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hK0 : 0 < K := by linarith
  set P := N ^ (κ * s) with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hN0 _
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hq : (2 : ℝ) ^ (-(T : ℤ)) = (2 ^ T)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hg : N ^ (-κ * s) = P⁻¹ := by rw [hP, ← Real.rpow_neg hN0.le]; ring_nf
  have hw : N ^ (-(2 * κ * s)) = (P ^ 2)⁻¹ := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_neg hN0.le]
    ring_nf
  rw [hq, hg, hw]
  have hgq : P⁻¹ ≤ K * (2 ^ T)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ h2T, inv_mul_le_iff₀ hPpos]
    linarith
  have hqg : ((2 : ℝ) ^ T)⁻¹ ≤ K * P⁻¹ := by
    rw [← div_eq_mul_inv, inv_le_comm₀ h2T (div_pos hK0 hPpos), inv_div]
    exact hA1
  have hq0 : 0 ≤ ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hg0 : 0 ≤ P⁻¹ := by positivity
  refine ⟨Real.rpow_le_rpow_of_exponent_le hN1 (by linarith), ?_, by
    rw [inv_mul_cancel₀ h2T.ne'], hgq, hqg, ?_, ?_⟩
  · -- N^(-s) ≤ q²
    have h1 : (P ^ 2)⁻¹ ≤ K ^ 2 * ((2 : ℝ) ^ T)⁻¹ ^ 2 := by
      calc (P ^ 2)⁻¹ = (P⁻¹) ^ 2 := (inv_pow P 2).symm
        _ ≤ (K * ((2 : ℝ) ^ T)⁻¹) ^ 2 := by gcongr
        _ = K ^ 2 * ((2 : ℝ) ^ T)⁻¹ ^ 2 := by ring
    have h2 : K ^ 2 * N ^ (-s) ≤ (P ^ 2)⁻¹ := by
      have : (P ^ 2)⁻¹ = N ^ (-(2 * κ * s)) := by
        rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_neg hN0.le]
        ring_nf
      rw [this]
      have e : N ^ (-(2 * κ * s)) = N ^ ((1 - 2 * κ) * s) * N ^ (-s) := by
        rw [← Real.rpow_add hN0]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_right hK2 (Real.rpow_nonneg hN0.le _)
    have hK2pos : 0 < K ^ 2 := by positivity
    have : K ^ 2 * N ^ (-s) ≤ K ^ 2 * ((2 : ℝ) ^ T)⁻¹ ^ 2 := h2.trans h1
    exact le_of_mul_le_mul_left this hK2pos
  · calc (((2 : ℝ) ^ T)⁻¹) ^ 2 ≤ (K * P⁻¹) ^ 2 := by gcongr
      _ = K ^ 2 * (P ^ 2)⁻¹ := by rw [← inv_pow]; ring
  · calc (P ^ 2)⁻¹ = (P⁻¹) ^ 2 := (inv_pow P 2).symm
      _ ≤ (K * ((2 : ℝ) ^ T)⁻¹) ^ 2 := by gcongr
      _ = K ^ 2 * ((2 : ℝ) ^ T)⁻¹ ^ 2 := by ring

/-- The base cap at width `w`, summed over unit scalar bins. -/
theorem cap0_of {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ} {K w : ℝ} (hK : 1 ≤ K)
    (hcap : ∀ n0 n1 n2 m : ℤ, μ {p | (⌊p.2 / w⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / w⌋ = n1 ∧
      ⌊X2 (b p.1) p.2 / w⌋ = n2) ∧ ⌊X3 (b p.1) p.2⌋ = m} ≤ ENNReal.ofReal (K * w ^ 3))
    (hX3 : μ {p | ¬ |X3 (b p.1) p.2| ≤ K} = 0) (hw : 0 < w) :
    ∀ n0 n1 n2 : ℤ, μ {p | ⌊p.2 / w⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / w⌋ = n1 ∧
      ⌊X2 (b p.1) p.2 / w⌋ = n2} ≤ ENNReal.ofReal (4 * K ^ 2 * w ^ 3) := by
  intro n0 n1 n2
  set S := {p : α × ℝ | ⌊p.2 / w⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / w⌋ = n1 ∧
      ⌊X2 (b p.1) p.2 / w⌋ = n2} with hS
  set M := Finset.Icc ⌊-K⌋ ⌊K⌋ with hM
  have hcover : S ⊆ (⋃ m ∈ M, {p | (⌊p.2 / w⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / w⌋ = n1 ∧
      ⌊X2 (b p.1) p.2 / w⌋ = n2) ∧ ⌊X3 (b p.1) p.2⌋ = m}) ∪
        {p | ¬ |X3 (b p.1) p.2| ≤ K} := by
    intro p hp
    by_cases h : |X3 (b p.1) p.2| ≤ K
    · left
      simp only [mem_iUnion]
      refine ⟨⌊X3 (b p.1) p.2⌋, ?_, hp, rfl⟩
      rw [abs_le] at h
      rw [hM, Finset.mem_Icc]
      exact ⟨Int.floor_mono h.1, Int.floor_mono h.2⟩
    · right; exact h
  have hcard : (M.card : ℝ) ≤ 2 * K + 2 := by
    rw [hM, Int.card_Icc]
    have h1 := Int.floor_le K
    have h2 := Int.lt_floor_add_one (-K)
    have hle : ⌊-K⌋ ≤ ⌊K⌋ + 1 := by
      have := Int.floor_mono (show -K ≤ K by linarith)
      omega
    have : ((⌊K⌋ + 1 - ⌊-K⌋).toNat : ℝ) = ((⌊K⌋ + 1 - ⌊-K⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [this]
    push_cast
    linarith
  calc μ S ≤ μ ((⋃ m ∈ M, {p | (⌊p.2 / w⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / w⌋ = n1 ∧
      ⌊X2 (b p.1) p.2 / w⌋ = n2) ∧ ⌊X3 (b p.1) p.2⌋ = m}) ∪
        {p | ¬ |X3 (b p.1) p.2| ≤ K}) := measure_mono hcover
    _ ≤ μ (⋃ m ∈ M, {p | (⌊p.2 / w⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / w⌋ = n1 ∧
      ⌊X2 (b p.1) p.2 / w⌋ = n2) ∧ ⌊X3 (b p.1) p.2⌋ = m}) +
        μ {p | ¬ |X3 (b p.1) p.2| ≤ K} := measure_union_le _ _
    _ = μ (⋃ m ∈ M, {p | (⌊p.2 / w⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / w⌋ = n1 ∧
      ⌊X2 (b p.1) p.2 / w⌋ = n2) ∧ ⌊X3 (b p.1) p.2⌋ = m}) := by rw [hX3, add_zero]
    _ ≤ ∑ m ∈ M, μ {p | (⌊p.2 / w⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / w⌋ = n1 ∧
      ⌊X2 (b p.1) p.2 / w⌋ = n2) ∧ ⌊X3 (b p.1) p.2⌋ = m} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ M, ENNReal.ofReal (K * w ^ 3) := Finset.sum_le_sum (fun m _ => hcap n0 n1 n2 m)
    _ = (M.card : ℝ≥0∞) * ENNReal.ofReal (K * w ^ 3) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (2 * K + 2) * ENNReal.ofReal (K * w ^ 3) := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard
    _ ≤ ENNReal.ofReal (4 * K ^ 2 * w ^ 3) := by
        rw [← ENNReal.ofReal_mul (by linarith)]
        apply ENNReal.ofReal_le_ofReal
        have hw3 : 0 ≤ w ^ 3 := by positivity
        have hKK : (2 * K + 2) * K ≤ 4 * K ^ 2 := by nlinarith
        calc (2 * K + 2) * (K * w ^ 3) = ((2 * K + 2) * K) * w ^ 3 := by ring
          _ ≤ (4 * K ^ 2) * w ^ 3 := mul_le_mul_of_nonneg_right hKK hw3
          _ = 4 * K ^ 2 * w ^ 3 := by ring

/-- The joint cap at base width `a = N^(-s)` and every scalar width `r ∈ [a,1]`. -/
theorem capB_of {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    {N K d s χ : ℝ} (hN : 1 < N)
    (hcap : ∀ s' : ℝ, 0 ≤ s' → s' ≤ s → ∀ n0 n1 n2 m v₀ : ℤ,
      μ {p | (⌊p.2 / N ^ (-s)⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / N ^ (-s)⌋ = n1 ∧
        ⌊X2 (b p.1) p.2 / N ^ (-s)⌋ = n2) ∧ ⌊X3 (b p.1) p.2 / N ^ (-s')⌋ = m ∧
          ⌊b p.1 3 / χ⌋ = v₀} ≤
        ENNReal.ofReal (K * N ^ (-3 * s - d * s')) * π {x | ⌊x / χ⌋ = v₀}) :
    ∀ r : ℝ, N ^ (-s) ≤ r → r ≤ 1 → ∀ n0 n1 n2 m v₀ : ℤ,
      μ {p | ⌊p.2 / N ^ (-s)⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / N ^ (-s)⌋ = n1 ∧
        ⌊X2 (b p.1) p.2 / N ^ (-s)⌋ = n2 ∧ ⌊X3 (b p.1) p.2 / r⌋ = m ∧
        ⌊b p.1 3 / χ⌋ = v₀} ≤
        ENNReal.ofReal (K * (N ^ (-s)) ^ 3 * r ^ d) * π {x | ⌊x / χ⌋ = v₀} := by
  intro r hr hr1 n0 n1 n2 m v₀
  have hN0 : 0 < N := by linarith
  have hr0 : 0 < r := (Real.rpow_pos_of_pos hN0 _).trans_le hr
  set s' := -Real.logb N r with hs'
  have hNr : N ^ (-s') = r := by rw [hs', neg_neg, Real.rpow_logb hN0 hN.ne' hr0]
  have hs'0 : 0 ≤ s' := by
    rw [hs', neg_nonneg]
    exact Real.logb_nonpos hN hr0.le hr1
  have hs's : s' ≤ s := by
    rw [hs', neg_le]
    have := Real.logb_le_logb_of_le hN (Real.rpow_pos_of_pos hN0 _) hr
    rwa [Real.logb_rpow hN0 hN.ne'] at this
  have h := hcap s' hs'0 hs's n0 n1 n2 m v₀
  rw [hNr] at h
  have hset : {p : α × ℝ | ⌊p.2 / N ^ (-s)⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / N ^ (-s)⌋ = n1 ∧
        ⌊X2 (b p.1) p.2 / N ^ (-s)⌋ = n2 ∧ ⌊X3 (b p.1) p.2 / r⌋ = m ∧
        ⌊b p.1 3 / χ⌋ = v₀} = {p | (⌊p.2 / N ^ (-s)⌋ = n0 ∧ ⌊X1 (b p.1) p.2 / N ^ (-s)⌋ = n1 ∧
        ⌊X2 (b p.1) p.2 / N ^ (-s)⌋ = n2) ∧ ⌊X3 (b p.1) p.2 / r⌋ = m ∧
          ⌊b p.1 3 / χ⌋ = v₀} := by
    ext p; simp only [mem_setOf_eq, and_assoc]
  rw [hset]
  refine h.trans (le_of_eq ?_)
  congr 2
  rw [show -3 * s - d * s' = (-s) * ((3 : ℕ) : ℝ) + (-s') * d by push_cast; ring,
    Real.rpow_add hN0, Real.rpow_mul hN0.le, Real.rpow_mul hN0.le, hNr, Real.rpow_natCast]
  ring

theorem range_of_inv {R x : ℝ} (hx : 0 < x) (h1 : x ≤ R) (h2 : x⁻¹ ≤ R) :
    R⁻¹ ≤ x ∧ x ≤ R := by
  refine ⟨?_, h1⟩
  have hR : 0 < R := hx.trans_le h1
  rw [inv_le_comm₀ hR hx]
  exact h2

/-- At a fixed depth, every large index carries the single-depth data. -/
theorem eventually_depthDataAt_hyp (cfg : Data α) (hN : ∀ k, 2 ≤ cfg.N k)
    (hK : ∀ k, 1 ≤ cfg.K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε)
    (hd0 : 0 ≤ cfg.d) (hd1 : cfg.d < 1) (hκ0 : 0 < cfg.κ) (hκ : 2 * cfg.κ < 1)
    (hℓ : cfg.ℓ = cfg.κ) (he0 : 0 < cfg.e₀)
    (hbasic : cfg.Basic) (hcaps : cfg.Caps) (hatlas : cfg.Atlas)
    {s : ℝ} (hs0 : 0 < s) (hsU : s ≤ cfg.U) (hse : s < cfg.e₀) :
    ∀ᶠ k in atTop, (depthDataAt cfg k s).Hyp := by
  have hκs : 0 < 2 * cfg.κ * s := by positivity
  set R : ℝ := s + s⁻¹ + cfg.e₀ + cfg.e₀⁻¹ + 2 * cfg.κ * s + (2 * cfg.κ * s)⁻¹ + 2 with hR
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs0
  have hei : 0 < cfg.e₀⁻¹ := inv_pos.mpr he0
  have hκsi : 0 < (2 * cfg.κ * s)⁻¹ := inv_pos.mpr hκs
  have hR1 : 1 < R := by linarith
  have hsR := range_of_inv (R := R) hs0 (by linarith) (by linarith)
  have heR := range_of_inv (R := R) he0 (by linarith) (by linarith)
  have hκR := range_of_inv (R := R) hκs (by linarith) (by linarith)
  have hgap : 0 < (1 - 2 * cfg.κ) * s := mul_pos (by linarith) hs0
  have hK2 : ∀ᶠ k in atTop, cfg.K k ^ 2 ≤ cfg.N k ^ ((1 - 2 * cfg.κ) * s) := by
    filter_upwards [hsub ((1 - 2 * cfg.κ) * s / 2) (by positivity)] with k hk
    have hN0 : 0 < cfg.N k := by linarith [hN k]
    calc cfg.K k ^ 2 ≤ (cfg.N k ^ ((1 - 2 * cfg.κ) * s / 2)) ^ 2 :=
          pow_le_pow_left₀ (by linarith [hK k]) hk 2
      _ = cfg.N k ^ ((1 - 2 * cfg.κ) * s) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          norm_num
  filter_upwards [hcaps R hR1, hatlas R hR1, hK2] with k hcap hatl hK2k
  have hNk : 2 ≤ cfg.N k := hN k
  have hN0 : 0 < cfg.N k := by linarith
  have hN1 : 1 < cfg.N k := by linarith
  have hKk := hK k
  obtain ⟨hb, hν, hπ, hμν, hρμ, hμsupp, hρmass, -, -, hpoly⟩ := hbasic k
  obtain ⟨A1, A2, A3, A4, A5, A6, -⟩ := hatl s hsR.1 hsU
  obtain ⟨hχa, haq, hqT, hgq, hqg, hqw, hwq⟩ := scale_relations hNk hKk hse.le A1 A2 hK2k
  -- the index set is not empty
  have hn : 0 < cfg.n k s := by
    by_contra h0
    push_neg at h0
    have hn0 : cfg.n k s = 0 := by omega
    have hμ0 : cfg.μ k univ = 0 := by
      rw [ae_iff] at A6
      have : {p : α × ℝ | ¬∃ i, p.1 ∈ cfg.B k s i ∧
          p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i)} = univ := by
        ext p
        simp only [mem_setOf_eq, mem_univ, iff_true, not_exists, not_and]
        intro i
        exact absurd i.isLt (by omega)
      rw [this] at A6
      exact A6
    have h1 := hρmass.trans (hρμ univ)
    rw [hμ0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
    have : 0 < (cfg.K k)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  set i₀ : Fin (cfg.n k s) := ⟨0, hn⟩
  have hP : cfg.P k = MvPolynomial.X 3 := ((A5 i₀).2.2.2.2.2.2.2.2 rfl).1
  have hX3ae : cfg.μ k {p | ¬ |X3 (cfg.b k p.1) p.2| ≤ cfg.K k} = 0 := by
    have ht : ∀ᵐ p ∂cfg.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      have : {a : α × ℝ | ¬a.2 ∈ Icc (0 : ℝ) 1} = (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
        ext p; simp
      rw [this]
      exact hμsupp
    have hae : ∀ᵐ p ∂cfg.μ k, |X3 (cfg.b k p.1) p.2| ≤ cfg.K k := by
      filter_upwards [hpoly, ht] with p hp hpt
      have := (hp.1 p.2 hpt).1
      rwa [hP, MvPolynomial.eval_X, x_three] at this
    rw [ae_iff] at hae
    exact hae
  have hI : ∀ i : Fin (cfg.n k s), Data.I (cfg.T k s) (cfg.j k s i) =
      tblock (blockLen cfg k s) (cfg.j k s i) := fun i => I_eq_tblock _ _
  have hspec : ∀ i : Fin (cfg.n k s), AtlasFit cfg k s i (atlasL cfg k s i) :=
    fun i => atlasL_spec ((A5 i).2.2.2.2.2.2.2.2 rfl).2.2.2
  exact {
    hK := hKk
    hd0 := hd0
    hd1 := hd1
    ha0 := Real.rpow_pos_of_pos hN0 _
    hχ0 := Real.rpow_pos_of_pos hN0 _
    hχa := hχa
    haq := haq
    hqT := hqT
    hgq := by
      show cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * blockLen cfg k s
      rw [hℓ]; exact hgq
    hqg := by
      show blockLen cfg k s ≤ cfg.K k * cfg.N k ^ (-cfg.ℓ * s)
      rw [hℓ]; exact hqg
    hw0 := Real.rpow_pos_of_pos hN0 _
    hqw := hqw
    hwq := hwq
    hb := hb
    hν := hν
    hπ := hπ
    hμν := hμν
    hρμ := hρμ
    hμsupp := hμsupp
    cap0 := by
      apply cap0_of hKk _ hX3ae (Real.rpow_pos_of_pos hN0 _)
      intro n0 n1 n2 m
      have hc2 := (hcap (2 * cfg.κ * s) 0 cfg.e₀ hκR.1 hκR.2 le_rfl (by linarith)
        heR.1 heR.2).2.1 false ![n0, n1, n2] m
      have hset : {p : α × ℝ | (⌊p.2 / cfg.N k ^ (-(2 * cfg.κ * s))⌋ = n0 ∧
          ⌊X1 (cfg.b k p.1) p.2 / cfg.N k ^ (-(2 * cfg.κ * s))⌋ = n1 ∧
          ⌊X2 (cfg.b k p.1) p.2 / cfg.N k ^ (-(2 * cfg.κ * s))⌋ = n2) ∧
          ⌊X3 (cfg.b k p.1) p.2⌋ = m} =
          {p | cfg.z k (cfg.N k) (2 * cfg.κ * s) p = ![n0, n1, n2] ∧
            ⌊(if false = true then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k)
              else (cfg.x k p.1 p.2) 3) / cfg.N k ^ (-(0 : ℝ))⌋ = m} := by
        ext p
        simp only [mem_setOf_eq, z_eq_iff, Bool.false_eq_true, if_false, x_three, neg_zero,
          Real.rpow_zero, div_one]
      have hval : cfg.K k * cfg.N k ^ (-3 * (2 * cfg.κ * s) - cfg.d * 0) =
          cfg.K k * (cfg.N k ^ (-(2 * cfg.κ * s))) ^ 3 := by
        rw [mul_zero, sub_zero, show -3 * (2 * cfg.κ * s) = (-(2 * cfg.κ * s)) * ((3 : ℕ) : ℝ) by
          push_cast; ring, Real.rpow_mul hN0.le, Real.rpow_natCast]
      show cfg.μ k _ ≤ ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-(2 * cfg.κ * s))) ^ 3)
      rw [hset, ← hval]
      exact hc2
    capB := by
      apply capB_of hN1
      intro s' hs'0 hs's n0 n1 n2 m v₀
      dsimp only [depthDataAt]
      have hc3 := (hcap s s' cfg.e₀ hsR.1 hsR.2 hs'0 (hs's.trans hsR.2)
        heR.1 heR.2).2.2 false ![n0, n1, n2] m v₀
      have hset : {p : α × ℝ | (⌊p.2 / cfg.N k ^ (-s)⌋ = n0 ∧
          ⌊X1 (cfg.b k p.1) p.2 / cfg.N k ^ (-s)⌋ = n1 ∧
          ⌊X2 (cfg.b k p.1) p.2 / cfg.N k ^ (-s)⌋ = n2) ∧
          ⌊X3 (cfg.b k p.1) p.2 / cfg.N k ^ (-s')⌋ = m ∧
          ⌊cfg.b k p.1 3 / cfg.N k ^ (-cfg.e₀)⌋ = v₀} =
          {p | cfg.z k (cfg.N k) s p = ![n0, n1, n2] ∧
            ⌊(if false = true then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k)
              else (cfg.x k p.1 p.2) 3) / cfg.N k ^ (-s')⌋ = m ∧
            ⌊cfg.b k p.1 3 / cfg.N k ^ (-cfg.e₀)⌋ = v₀} := by
        ext p
        simp only [mem_setOf_eq, z_eq_iff, Bool.false_eq_true, if_false, x_three]
      rw [hset]
      exact hc3
    hA := fun i => (A3 i).1
    hB := fun i => (A3 i).2.1
    hBA := fun i => (A3 i).2.2
    hdisj := A4
    hνA := fun i => (A5 i).1
    hμB := fun i => by
      have := (A5 i).2.2.1
      rw [hI i] at this
      exact this
    hc := fun i => (A5 i).2.2.2.1
    h1 := by
      intro i l hl t ht
      have ht' : t ∈ Data.I (cfg.T k s) (cfg.j k s i) := by rw [hI i]; exact ht
      have := ((A5 i).2.2.2.2.2.1 l hl t ht').1
      rw [x_one] at this
      exact this
    h2 := by
      intro i l hl t ht
      have ht' : t ∈ Data.I (cfg.T k s) (cfg.j k s i) := by rw [hI i]; exact ht
      have := ((A5 i).2.2.2.2.2.1 l hl t ht').2.1
      rw [x_one, x_two] at this
      exact this
    h3 := fun i => ((A5 i).2.2.2.2.2.2.2.2 rfl).2.2.1
    hfit := by
      intro i l hl t ht
      have ht' : t ∈ Data.I (cfg.T k s) (cfg.j k s i) := by rw [hI i]; exact ht
      have hfit := ((A5 i).2.2.2.2.2.2.1 l hl t ht').1
      rw [(hspec i).1] at hfit
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X] at hfit
      have e0 : (cfg.x k l t) 0 = t := by
        simp [Submission.Obl.k4_critical_switching_state_preparation.Data.x]
      rw [e0, x_one, x_two, x_three] at hfit
      exact hfit
    hL3 := fun i => (hspec i).2.1
    hL12 := by
      intro i l hl t ht
      have ht' : t ∈ Data.I (cfg.T k s) (cfg.j k s i) := by rw [hI i]; exact ht
      have := (hspec i).2.2 l hl t ht'
      rw [x_one] at this
      exact this
    hcov := by
      have h6 := A6
      rw [ae_iff] at h6
      have : {p : α × ℝ | ¬∃ i, p.1 ∈ cfg.B k s i ∧
          p.2 ∈ tblock (blockLen cfg k s) (cfg.j k s i)} =
          {p | ¬∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i)} := by
        ext p; simp only [mem_setOf_eq, hI]
      show cfg.μ k {p | ¬∃ i, p.1 ∈ cfg.B k s i ∧
          p.2 ∈ tblock (blockLen cfg k s) (cfg.j k s i)} = 0
      rw [this]
      exact h6 }

end

end Submission.Obl.k4_horizontal_coefficient_count
