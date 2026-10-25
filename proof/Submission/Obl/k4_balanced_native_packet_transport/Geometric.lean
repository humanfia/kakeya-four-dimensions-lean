import Submission.Obl.k4_balanced_native_packet_transport.RefinedSample
import Submission.Obl.k4_balanced_native_packet_transport.RefinedFromAtlas
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

/-!
The geometric stage of the two-stage seam (x0722's `GeometricRefinementStatement`).
Outer scalar choices precede the exact problem; the formats are fixed before every
loss. For each small loss, tracked saturated packets inside the native charts are
pulled back (`RefinedFromAtlas.refined_of_atlas`) and the restricted native laws
give the uncapped sample (`Refined.uncapped_of_refined`); larger losses follow by
monotonicity.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport
namespace Geometric

open MeasureTheory Filter Set
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedPacketSystems

noncomputable section
set_option linter.unusedVariables false

/-- A power-small term below a fifth of `N ^ (-ε)`. -/
theorem rpow_neg_le_fifth {N a ε : ℝ} (hN : 0 < N) (h : 5 ≤ N ^ (a - ε)) :
    N ^ (-a) ≤ N ^ (-ε) / 5 := by
  have hpos : 0 < N ^ (a - ε) := Real.rpow_pos_of_pos hN _
  have heq : N ^ (-a) = N ^ (-ε) / N ^ (a - ε) := by
    rw [eq_div_iff hpos.ne', ← Real.rpow_add hN]
    congr 1
    ring
  rw [heq]
  exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN _).le (by norm_num) h

/-- The five terms reserved for the coverage of a refined sample. -/
theorem coverage_numeric {N loss χ a₀ c₀ S u τ w ε : ℝ} (hN : 1 ≤ N)
    (h1 : 5 ≤ N ^ (loss - ε)) (h2 : 5 ≤ N ^ (χ - ε)) (h3 : 5 ≤ N ^ (a₀ - ε))
    (h4 : 5 ≤ N ^ (c₀ - ε)) (h5 : 500 ≤ N ^ (S * u - 2 * τ - 3 * ε))
    (h6 : 2 * ε - loss + u ≤ 0) (h7 : 3 * ε - w + u ≤ 0) :
    N ^ (-loss) + N ^ (-χ) + N ^ (-a₀) +
      N ^ (-S * u + 2 * τ) * N ^ (2 * ε) *
        (2 * (2 * N ^ (2 * ε) * (N ^ (-loss) + N ^ (-w) * N ^ ε)) / δ N u + 2) ^ 2 +
      N ^ (-c₀) ≤ N ^ (-ε) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have t1 := rpow_neg_le_fifth hN0 h1
  have t2 := rpow_neg_le_fifth hN0 h2
  have t3 := rpow_neg_le_fifth hN0 h3
  have t4 := rpow_neg_le_fifth hN0 h4
  have hδ := (Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN0 u).1
  have hδpos : 0 < δ N u := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hδ
  have hinv : 1 / δ N u ≤ N ^ u := by
    rw [div_le_iff₀ hδpos]
    calc (1 : ℝ) = N ^ u * N ^ (-u) := by
          rw [← Real.rpow_add hN0]; simp
      _ ≤ N ^ u * δ N u := mul_le_mul_of_nonneg_left hδ (Real.rpow_pos_of_pos hN0 _).le
  have hA : N ^ (2 * ε) * N ^ (-loss) * N ^ u ≤ 1 := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hB : N ^ (2 * ε) * (N ^ (-w) * N ^ ε) * N ^ u ≤ 1 := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  set X := 2 * (2 * N ^ (2 * ε) * (N ^ (-loss) + N ^ (-w) * N ^ ε)) / δ N u with hX
  have hX0 : 0 ≤ X := by positivity
  have hX8 : X ≤ 8 := by
    have hnum0 : 0 ≤ 2 * (2 * N ^ (2 * ε) * (N ^ (-loss) + N ^ (-w) * N ^ ε)) := by positivity
    calc X = 2 * (2 * N ^ (2 * ε) * (N ^ (-loss) + N ^ (-w) * N ^ ε)) * (1 / δ N u) := by
          rw [hX]; ring
      _ ≤ 2 * (2 * N ^ (2 * ε) * (N ^ (-loss) + N ^ (-w) * N ^ ε)) * N ^ u :=
          mul_le_mul_of_nonneg_left hinv hnum0
      _ = 4 * (N ^ (2 * ε) * N ^ (-loss) * N ^ u + N ^ (2 * ε) * (N ^ (-w) * N ^ ε) * N ^ u) := by
          ring
      _ ≤ 4 * (1 + 1) := by gcongr
      _ = 8 := by norm_num
  have hsq : (X + 2) ^ 2 ≤ 100 := by nlinarith
  have hang : N ^ (-S * u + 2 * τ) * N ^ (2 * ε) * (X + 2) ^ 2 ≤ N ^ (-ε) / 5 := by
    have hpos5 : 0 < N ^ (S * u - 2 * τ - 3 * ε) := Real.rpow_pos_of_pos hN0 _
    have heq : N ^ (-S * u + 2 * τ) * N ^ (2 * ε) =
        N ^ (-ε) / N ^ (S * u - 2 * τ - 3 * ε) := by
      rw [eq_div_iff hpos5.ne', ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      ring
    rw [heq]
    have hfrac : N ^ (-ε) / N ^ (S * u - 2 * τ - 3 * ε) ≤ N ^ (-ε) / 500 :=
      div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN0 _).le (by norm_num) h5
    have hne : 0 ≤ N ^ (-ε) / N ^ (S * u - 2 * τ - 3 * ε) := by positivity
    calc N ^ (-ε) / N ^ (S * u - 2 * τ - 3 * ε) * (X + 2) ^ 2
        ≤ N ^ (-ε) / 500 * 100 :=
          mul_le_mul hfrac hsq (sq_nonneg _) (by positivity)
      _ = N ^ (-ε) / 5 := by ring
  linarith

/-- Positive powers of an unbounded subsequence eventually dominate every constant. -/
theorem eventually_const_le_rpow {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {b : ℝ} (hb : 0 < b) (C : ℝ) :
    ∀ᶠ n in atTop, C ≤ N (φ n) ^ b :=
  (((tendsto_rpow_atTop hb).comp hN).comp hφ).eventually_ge_atTop C

/-- The uncapped sample only weakens when its loss grows. -/
theorem uncapped_mono_loss {N K : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss loss' h χ d s m S U f₀ ξ : ℝ}
    (hN : 1 ≤ N) (hB : ∀ γ, 0 ≤ B γ) (hl : loss ≤ loss')
    (hs : UncappedNativeSample N K W ω ν E P B M D loss h χ d s m S U f₀ ξ) :
    UncappedNativeSample N K W ω ν E P B M D loss' h χ d s m S U f₀ ξ := by
  obtain ⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal,
    hK, ht, hC, hsep, hlst, hlistm, hcharts, hcoords, hbudget, hlaw, hmass, hcert, hcap⟩ := hs
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ loss ≤ N ^ loss' := Real.rpow_le_rpow_of_exponent_le hN hl
  have hpos : 0 < N ^ loss := Real.rpow_pos_of_pos hN0 _
  refine ⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal,
    hK.trans hpow, ht.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hC, hsep,
    fun w o => (hlst w o).trans hpow, hlistm, fun a => ?_, hcoords, hbudget, hlaw,
    le_trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith))) hmass, hcert, fun a => ?_⟩
  · exact Submission.Obl.k4_quadratic_atlas_normalization.chart_mono hN le_rfl le_rfl hpos hpow
      (hB _) (hcharts a) id
  · obtain ⟨hprior, htan, e, n, β, he, he1, hn1, hen, hfull, hstrip⟩ := hcap a
    refine ⟨hprior, htan, e, n, β, he, he1, hn1, hen, le_trans ?_ hfull, fun l hl => ?_⟩
    · apply div_le_div_of_nonneg_left (by positivity) hpos hpow
    · exact (hstrip l hl).trans (mul_le_mul_of_nonneg_right hpow (by positivity))

/-- The probability and weight clauses of a frozen problem at one sample. -/
theorem prob_sample_data {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal}
    (hprob : prob N K L d S η W ω ν E P B f g G) (k : ℕ) :
    (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, IsProbabilityMeasure (ν k γ)) ∧
      ∀ γ, 0 < B k γ := by
  obtain ⟨_, _, _, _, _, _, _, _, ⟨M, D, hdata⟩, _⟩ := hprob
  obtain ⟨_, hω, hω₁, hν, _⟩ := hdata k
  exact ⟨hω, hω₁, fun γ => (hν γ).1, fun γ => (hν γ).2.1⟩

/-- The format bound for retimed native offsets and tangents. -/
theorem format_power_bound {N h loss : ℝ} {M Mout : ℕ} (hN : 2 ≤ N) (hloss : loss ≤ 1) :
    4 * (N ^ M + N ^ Mout) * N ^ (h + loss) ≤ N ^ (M + Mout + Nat.ceil h + 4) := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hpow1 : N ^ M ≤ N ^ (M + Mout) := pow_le_pow_right₀ hN1 (by omega)
  have hpow2 : N ^ Mout ≤ N ^ (M + Mout) := pow_le_pow_right₀ hN1 (by omega)
  have hceil : h + loss ≤ ((Nat.ceil h + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil h; push_cast; linarith
  have hrp : N ^ (h + loss) ≤ N ^ (Nat.ceil h + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hceil
  have h8le : (8 : ℝ) ≤ N ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN 3
    norm_num at this; linarith
  calc 4 * (N ^ M + N ^ Mout) * N ^ (h + loss)
      ≤ 4 * (2 * N ^ (M + Mout)) * N ^ (Nat.ceil h + 1) := by
        apply mul_le_mul _ hrp (Real.rpow_pos_of_pos hN0 _).le (by positivity)
        linarith
    _ = 8 * N ^ (M + Mout) * N ^ (Nat.ceil h + 1) := by ring
    _ ≤ N ^ 3 * N ^ (M + Mout) * N ^ (Nat.ceil h + 1) := by gcongr
    _ = N ^ (M + Mout + Nat.ceil h + 4) := by rw [← pow_add, ← pow_add]; ring_nf

/-- One tracked sample with its saturated covered atlas gives the uncapped
intermediate sample at the same original index. -/
theorem uncapped_at_index
    {N K : ℕ → ℝ} {d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal}
    (hprob : prob N K 1 d S η W ω ν E P B f g G)
    (q : Certificate (TrackingNative.toData N K d S η W ω ν E P B f g G)) (n : ℕ)
    {M D : ℕ} {a₀ ds s m U ℓ χ U' : ℝ}
    (σ : NativeSample (W (q.sequence.index n)))
    (hσ : σ.Holds false (N (q.sequence.index n)) (K (q.sequence.index n))
      (ω (q.sequence.index n)) (ν (q.sequence.index n)) (E (q.sequence.index n))
      (P (q.sequence.index n)) (B (q.sequence.index n)) M D a₀ (U' + 1) ℓ 1 (χ / 2)
      ds s m (S / 2) U)
    (hsub : Tracking.SubOf (q.sequence.atlas n)
      (TrackingNative.nativeAtlas (TrackingNative.toData N K d S η W ω ν E P B f g G)
        (q.sequence.index n) σ (N (q.sequence.index n) ^ ℓ)))
    {M₁ D₁ : ℕ} {r ε h err : ℝ}
    (a : CPF.Atlas (normalizedData q) n) (ha : a.SaturatedAt M₁ D₁ r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hκ1 : 1 ≤ a.κ) (hκε : a.κ ≤ N (q.sequence.index n) ^ ε)
    (hT : (2 : ℝ) ^ a.T ≤ N (q.sequence.index n) ^ h)
    (hcov : ENNReal.ofReal (N (q.sequence.index n) ^ (-ε)) ≤
      CPF.OriginalPacketCoverage.originalCoveredMass q n a)
    (hband : ∀ c, N (q.sequence.index n) ^ (-ds * r - (3 * err + ε)) ≤
      originalMass q n a c /
        (N (q.sequence.index n) ^ (-f 0) * |(composedFrame q n a c).det|))
    (hPκ : (q.sequence.atlas n).κ ≤ N (q.sequence.index n) ^ ε)
    {loss ξ u τ c₀ : ℝ}
    (hε : 0 < ε) (hεloss : 2 * ε ≤ loss) (hloss : 0 < loss) (hloss₁ : loss ≤ 1)
    (hh : 0 < h) (hχ : 0 < χ) (hU' : 0 < U')
    (hξ : ds * r + 3 * err + ε ≤ ξ) (hu : 0 < u) (huη : u ≤ η)
    (hbad : ∑ γ, ENNReal.ofReal (ω (q.sequence.index n) γ) *
        (RefinedFromAtlas.uweProblem N K d W ω ν E P B f g G).incidenceMeasure
          (q.sequence.index n) γ
          (UWE.angularDensityBad (RefinedFromAtlas.uweProblem N K d W ω ν E P B f g G) S
              (q.sequence.index n) γ u τ ∪
            UWE.pureDensityBad (RefinedFromAtlas.uweProblem N K d W ω ν E P B f g G)
              (q.sequence.index n) γ 1 τ) ≤
      ENNReal.ofReal (N (q.sequence.index n) ^ (-c₀)))
    (h1 : 5 ≤ N (q.sequence.index n) ^ (loss - ε))
    (h2 : 5 ≤ N (q.sequence.index n) ^ (χ - ε))
    (h3 : 5 ≤ N (q.sequence.index n) ^ (a₀ - ε))
    (h4 : 5 ≤ N (q.sequence.index n) ^ (c₀ - ε))
    (h5 : 500 ≤ N (q.sequence.index n) ^ (S * u - 2 * τ - 3 * ε))
    (h6 : 2 * ε - loss + u ≤ 0) (h7 : 3 * ε - (U' + 1) + u ≤ 0)
    (hℓle : ℓ ≤ loss / 2) (hℓpow : 2 ≤ N (q.sequence.index n) ^ (loss / 2))
    (hc₀ : 32 ≤ N (q.sequence.index n) ^ (χ / 2))
    (hc₁ : 16 ≤ N (q.sequence.index n) ^ (χ - 2 * loss)) :
    UncappedNativeSample (N (q.sequence.index n)) (K (q.sequence.index n))
      (W (q.sequence.index n)) (ω (q.sequence.index n)) (ν (q.sequence.index n))
      (E (q.sequence.index n)) (P (q.sequence.index n)) (B (q.sequence.index n))
      (M + (q.M + M₁ + 1) + Nat.ceil h + 4) (max q.D D₁) loss h χ ds s m (S / 2) U' (f 0) ξ := by
  set Nn := N (q.sequence.index n) with hNndef
  have hNn2 : 2 ≤ Nn := hprob.1 _
  have hNn1 : 1 ≤ Nn := by linarith
  have hNn0 : 0 < Nn := by linarith
  obtain ⟨hω, hω₁, hν, -⟩ := prob_sample_data hprob (q.sequence.index n)
  have hnum := coverage_numeric (loss := loss) (χ := χ) (a₀ := a₀) (c₀ := c₀) (S := S)
    (u := u) (τ := τ) (w := U' + 1) (ε := ε) hNn1 h1 h2 h3 h4 h5 h6 h7
  have hnumE : ENNReal.ofReal (Nn ^ (-loss)) + ENNReal.ofReal (Nn ^ (-χ)) +
      ENNReal.ofReal (Nn ^ (-a₀)) +
      ENNReal.ofReal (Nn ^ (-S * u + 2 * τ) * Nn ^ (2 * ε) *
        (2 * (2 * Nn ^ (2 * ε) * (Nn ^ (-loss) + Nn ^ (-(U' + 1)) * Nn ^ ε)) /
          δ Nn u + 2) ^ 2) +
      ENNReal.ofReal (Nn ^ (-c₀)) ≤ ENNReal.ofReal (Nn ^ (-ε)) := by
    have hδpos : 0 < δ Nn u := by unfold δ; positivity
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hnum
  obtain ⟨ρ, hρ, hcover⟩ := RefinedFromAtlas.refined_of_atlas
    (Mout := q.M + M₁ + 1) (Dout := max q.D D₁) (χ := χ)
    hprob q n σ hσ hsub a ha hr0 hr1 hκ1 hκε hT hcov hband hPκ
    le_rfl le_rfl hε hεloss hloss hh.le hξ hu huη hbad hnumE
  have hℓ : 2 * Nn ^ ℓ ≤ Nn ^ loss := by
    calc 2 * Nn ^ ℓ ≤ Nn ^ (loss / 2) * Nn ^ (loss / 2) :=
          mul_le_mul hℓpow (Real.rpow_le_rpow_of_exponent_le hNn1 hℓle)
            (Real.rpow_pos_of_pos hNn0 _).le (Real.rpow_pos_of_pos hNn0 _).le
      _ = Nn ^ loss := by rw [← Real.rpow_add hNn0]; ring_nf
  have hcoeff₀ : 32 * Nn ^ (χ / 2) ≤ Nn ^ χ := by
    calc 32 * Nn ^ (χ / 2) ≤ Nn ^ (χ / 2) * Nn ^ (χ / 2) :=
          mul_le_mul_of_nonneg_right hc₀ (Real.rpow_pos_of_pos hNn0 _).le
      _ = Nn ^ χ := by rw [← Real.rpow_add hNn0]; ring_nf
  have hcoeff₁ : 16 * Nn ^ (2 * loss) ≤ Nn ^ χ := by
    calc 16 * Nn ^ (2 * loss) ≤ Nn ^ (χ - 2 * loss) * Nn ^ (2 * loss) :=
          mul_le_mul_of_nonneg_right hc₁ (Real.rpow_pos_of_pos hNn0 _).le
      _ = Nn ^ χ := by rw [← Real.rpow_add hNn0]; ring_nf
  have hw : Nn ^ (-(U' + 1)) ≤ Nn ^ (-U') :=
    Real.rpow_le_rpow_of_exponent_le hNn1 (by linarith)
  exact Refined.uncapped_of_refined (U' := U') σ hσ hω hω₁ hν ρ hρ hNn2 hloss hloss₁ hh
    (half_pos hχ) (by linarith) hℓ hcoeff₀ hcoeff₁ hw (by omega)
    (format_power_bound hNn2 hloss₁) hcover

set_option maxHeartbeats 800000 in
/-- `x0722`'s geometric stage: full-time localized native systems refine into
balanced, tangentially full native packets with uncapped restricted laws. -/
theorem geometric_refinement : GeometricRefinementStatement := by
  intro hI ds kr S η hS hη hes hloc
  obtain ⟨s, m, U, hs, hs1, hsm, hU, hUm, hL⟩ := hloc
  have hds0 : 0 ≤ ds := hes.1
  have hds1 : ds < 1 := hes.2.1
  refine ⟨s, m, min U η, hs, hs1, hsm, lt_min hU hη,
    (min_le_left _ _).trans_lt hUm, min_le_right _ _, ?_⟩
  intro χ h t ξ hχ hh ht hξ
  set U' := min U η with hU'def
  have hU'0 : 0 < U' := lt_min hU hη
  -- outer depth, saturation cap and profile tolerance
  set b : ℝ := min (1 / 4) (min (h / 4) (ξ / (8 * (ds + 1)))) with hbdef
  have hds1' : 0 < ds + 1 := by linarith
  have hb : 0 < b := lt_min (by norm_num) (lt_min (by linarith) (by positivity))
  have hb₁ : 2 * b ≤ 1 := by
    have := min_le_left (1 / 4 : ℝ) (min (h / 4) (ξ / (8 * (ds + 1)))); linarith
  have hbh : 2 * b < h := by
    have := (min_le_right (1 / 4 : ℝ) (min (h / 4) (ξ / (8 * (ds + 1))))).trans
      (min_le_left _ _)
    linarith
  have hbξ : ds * (2 * b) ≤ ξ / 4 := by
    have hb' : b ≤ ξ / (8 * (ds + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have h8 : 0 < 8 * (ds + 1) := by positivity
    have : b * (8 * (ds + 1)) ≤ ξ := (le_div_iff₀ h8).mp hb'
    nlinarith
  set Dcap : ℝ := (1 + ds) / 2 with hDcap
  have hD : 0 < Dcap := by positivity
  have hD₁ : Dcap < 1 := by rw [hDcap]; linarith
  have hdD : ds < Dcap := by rw [hDcap]; linarith
  set err : ℝ := min (ξ / 12) ((Dcap - ds) * b / 2) with herrdef
  have herr : 0 < err := lt_min (by positivity) (by
    have : 0 < Dcap - ds := by linarith
    positivity)
  have hsmall : 2 * err ≤ (Dcap - ds) * b := by
    have := min_le_right (ξ / 12) ((Dcap - ds) * b / 2); linarith
  have herrξ : err ≤ ξ / 12 := min_le_left _ _
  obtain ⟨tol, htol, hpk⟩ := TrackingNative.tracked_native_packets hI hes hb hb₁ herr hD hD₁
    hdD hsmall
  set t' : ℝ := min t tol with ht'def
  have ht' : 0 < t' := lt_min ht htol
  have ht't : t' ≤ t := min_le_left _ _
  have ht'tol : t' ≤ tol := min_le_right _ _
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hprob, hd, hH, a₀, M, D, ha₀, hsamples⟩ :=
    hL (χ / 2) (U' + 1) t' (half_pos hχ) (by linarith) ht'
  have hdtol : d < ds + tol := hd.trans_le (by linarith)
  have hHtol : kr - tol < H N K 1 W ω ν E B f := lt_of_le_of_lt (by linarith) hH
  obtain ⟨ψ, σ, hψ, hσ, hprofile, q, hθ, hnat, r, hr, hsys⟩ :=
    hpk N K d W ω ν E P B f g G hprob hdtol hHtol hsamples
  obtain ⟨M₁, D₁, hA'⟩ := hsys h hbh
  have hN2 : ∀ k, 2 ≤ N k := hprob.1
  have hNt : Tendsto N atTop atTop := hprob.2.1
  refine ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hprob, hd.trans_le (by linarith),
    lt_of_le_of_lt (by linarith) hH,
    fun x hx0 hxs => (hprofile x ⟨hx0, hxs.trans hs1.le⟩).trans (by linarith),
    M + (q.M + M₁ + 1) + Nat.ceil h + 4, max q.D D₁, ?_⟩
  intro loss hloss
  -- reduce to a small loss
  set loss' : ℝ := min loss (min (χ / 4) 1) with hloss'def
  have hloss'0 : 0 < loss' := lt_min hloss (lt_min (by positivity) one_pos)
  have hloss'le : loss' ≤ loss := min_le_left _ _
  have hloss'χ : loss' ≤ χ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hloss'1 : loss' ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  suffices hfreq : ∃ᶠ k in atTop, UncappedNativeSample (N k) (K k) (W k) (ω k) (ν k) (E k)
      (P k) (B k) (M + (q.M + M₁ + 1) + Nat.ceil h + 4) (max q.D D₁) loss' h χ ds s m (S / 2)
      U' (f 0) ξ by
    exact hfreq.mono fun k hk => uncapped_mono_loss
      (by linarith [hN2 k]) (fun γ => ((prob_sample_data hprob k).2.2.2 γ).le) hloss'le hk
  -- angular depth, mask tolerance and the density masks
  set u : ℝ := min η (loss' / 4) with hudef
  have hu0 : 0 < u := lt_min hη (by positivity)
  have huη : u ≤ η := min_le_left _ _
  have hu4 : u ≤ loss' / 4 := min_le_right _ _
  set τ : ℝ := S * u / 8 with hτdef
  have hτ : 0 < τ := by positivity
  have hvalid : (RefinedFromAtlas.uweProblem N K d W ω ν E P B f g G).Valid S η := hprob
  obtain ⟨c₀, hc₀, hbadev⟩ := hvalid.finite_density_preparation ∅ {u}
    (fun r hr => absurd hr (Finset.notMem_empty r))
    (fun u' hu' => by
      rw [Finset.mem_singleton.mp hu']
      exact ⟨hu0, by simpa [RefinedFromAtlas.uweProblem] using huη⟩) hτ
  -- inner tolerance
  set ε : ℝ := min (min (loss' / 8) (S * u / 12)) (min (min (a₀ / 2) (c₀ / 2))
    (min (ξ / 4) (χ / 2))) with hεdef
  have hε : 0 < ε := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)))
  have hε1 : ε ≤ loss' / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ S * u / 12 := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ a₀ / 2 := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hε4 : ε ≤ c₀ / 2 := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hε5 : ε ≤ ξ / 4 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hε6 : ε ≤ χ / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hidx : Tendsto q.sequence.index atTop atTop := q.sequence.strictMono.tendsto_atTop
  have hC : ∀ {e : ℝ}, 0 < e → ∀ C : ℝ, ∀ᶠ n in atTop, C ≤ N (q.sequence.index n) ^ e :=
    fun he C => eventually_const_le_rpow hNt hidx he C
  have hp1 : 0 < loss' - ε := by linarith only [hε1, hloss'0]
  have hp2 : 0 < χ - ε := by linarith only [hε6, hχ]
  have hp3 : 0 < a₀ - ε := by linarith only [hε3, ha₀]
  have hp4 : 0 < c₀ - ε := by linarith only [hε4, hc₀]
  have hp5 : 0 < S * u - 2 * τ - 3 * ε := by
    have hSu : 0 < S * u := by positivity
    rw [hτdef]; linarith only [hε2, hSu]
  have hp6 : 0 < χ - 2 * loss' := by linarith only [hloss'χ, hχ]
  -- the eventual conditions along the normalized sequence
  have hsmalln : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ loss' / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < loss' / 2))).mono fun n hn => hn.le
  have hbadn : ∀ᶠ n in atTop,
      ∑ γ, ENNReal.ofReal (ω (q.sequence.index n) γ) *
        (RefinedFromAtlas.uweProblem N K d W ω ν E P B f g G).incidenceMeasure
          (q.sequence.index n) γ
          (UWE.angularDensityBad (RefinedFromAtlas.uweProblem N K d W ω ν E P B f g G) S
              (q.sequence.index n) γ u τ ∪
            UWE.pureDensityBad (RefinedFromAtlas.uweProblem N K d W ω ν E P B f g G)
              (q.sequence.index n) γ 1 τ) ≤
        ENNReal.ofReal (N (q.sequence.index n) ^ (-c₀)) := by
    filter_upwards [hidx.eventually hbadev] with n hb'
    refine le_trans (Finset.sum_le_sum fun γ _ => mul_le_mul' le_rfl (measure_mono ?_)) hb'
    exact FullnessMass.densityBad_subset_preparation
      (RefinedFromAtlas.uweProblem N K d W ω ν E P B f g G) S ∅ {u} τ (q.sequence.index n) γ
      (Finset.mem_singleton_self u)
  have hξ' : ds * r + 3 * err + ε ≤ ξ := by
    have := mul_le_mul_of_nonneg_left hr.2 hds0
    linarith only [this, hbξ, herrξ, hε5, hξ]
  have h6 : 2 * ε - loss' + u ≤ 0 := by linarith only [hε1, hu4, hloss'0]
  have h7 : 3 * ε - (U' + 1) + u ≤ 0 := by linarith only [hε1, hu4, hloss'1, hU'0]
  apply hidx.frequently
  refine (((((((((((((hA' ε hε).and_eventually (q.sequence.slack_subpower ε hε)).and_eventually
    hbadn).and_eventually (hC hp1 5)).and_eventually (hC hp2 5)).and_eventually
    (hC hp3 5)).and_eventually (hC hp4 5)).and_eventually (hC hp5 500)).and_eventually
    hsmalln).and_eventually (hC (by positivity : 0 < loss' / 2) 2)).and_eventually
    (hC (by positivity : 0 < χ / 2) 32)).and_eventually (hC hp6 16))).mono ?_
  rintro n ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, hκ1, -, hκε, hTa, ha, hcov, hcs⟩, hPκ⟩, hbad⟩, h1⟩, h2⟩, h3⟩, h4⟩,
    h5⟩, hsn⟩, hℓpow⟩, hc₀'⟩, hc₁⟩
  obtain ⟨σ', ℓ, hℓ0, hℓn, hσ', hsub⟩ := hnat n
  exact uncapped_at_index hprob q n σ' hσ' hsub a ha (hb.le.trans hr.1) (hr.2.trans hb₁)
    hκ1 hκε hTa hcov (fun c => (hcs c).2.2.2.2.1) hPκ hε (by linarith only [hε1, hloss'0])
    hloss'0 hloss'1 hh hχ hU'0 hξ' hu0 huη hbad h1 h2 h3 h4 h5 h6 h7
    (hℓn.trans hsn) hℓpow hc₀' hc₁

end
end Geometric
end Submission.Obl.k4_balanced_native_packet_transport
