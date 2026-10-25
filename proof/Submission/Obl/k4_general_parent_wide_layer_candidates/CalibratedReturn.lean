import Submission.Obl.k4_general_parent_wide_layer_candidates.NativeGeometry
import Submission.Obl.k4_general_parent_wide_layer_candidates.Numerics

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory MvPolynomial Set Filter
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem residual_coefficient_envelope {k : ℕ} {s r : ℝ}
    (i : Fin (p.n k s)) (G : MvPolynomial (Fin 3) ℝ)
    (hN : 2 ≤ p.N k) (hr : 0 ≤ r) (hc : ∀ e, |G.coeff e| ≤ p.N k ^ r) :
    ∀ e, |(baseCalibratedTest (p.P k) G).coeff e| ≤
      p.N k ^ (r + 1) * p.nativeSize k s i ^ (r + 1) := by
  have hNp : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := by linarith
  have hsize := p.nativeSize_ge_one k s i
  have hpow : 1 ≤ p.N k ^ r := Real.one_le_rpow hN1 hr
  have hS : p.nativeSize k s i ≤ p.nativeSize k s i ^ (r + 1) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hsize (show (1 : ℝ) ≤ r + 1 by linarith)
  have hPS : coeffL1 (p.P k) ≤ p.nativeSize k s i := by
    have hF : 0 ≤ coeffL1 (p.F k s i) := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [nativeSize]
    linarith
  intro e
  calc
    _ ≤ coeffL1 (p.P k) + p.N k ^ r :=
      p.residual_coefficients k G (by positivity) hc e
    _ ≤ p.N k ^ r * p.nativeSize k s i + p.N k ^ r * p.nativeSize k s i := by
      exact add_le_add (hPS.trans (le_mul_of_one_le_left (by linarith) hpow))
        (le_mul_of_one_le_right (by positivity) hsize)
    _ = 2 * p.N k ^ r * p.nativeSize k s i := by ring
    _ ≤ p.N k * p.N k ^ r * p.nativeSize k s i ^ (r + 1) := by gcongr
    _ = p.N k ^ (r + 1) * p.nativeSize k s i ^ (r + 1) := by
      rw [Real.rpow_add hNp, Real.rpow_one]
      ring

/-- The analytic output needed from the wide-interval argument. -/
def NativePredictors (s v : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ (i : Fin (p.n k s)) (G : MvPolynomial (Fin 3) ℝ), G.totalDegree ≤ 2 ∧
      ENNReal.ofReal (p.N k ^ (-p.d * v - ε) / (2 : ℝ) ^ p.T k s) *
        p.ν k (p.A k s i) ≤ p.ρ k (p.PredictorEvent k s v ε i G)

/-- Full-block native predictors automatically have polynomial coefficients
from the primitive original grid caps. This also restores all derivative
witnesses and the exact frozen cofinal conclusion. -/
theorem candidates_of_native_predictors (h : p.Valid) {s v : ℝ}
    (hs : 0 < s) (hv : 0 < v) (hsU : s + v ≤ p.U)
    (hpred : p.NativePredictors s v) : p.Candidates := by
  let A := p.calibrationExponent s v
  have hA5 : 5 ≤ A := p.calibrationExponent_ge_five h hs.le hv.le
  have hA : 0 < A := by linarith
  let r := 32 * A
  let R := 2 + s + s⁻¹ + r
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hs]
  have hsR : R⁻¹ ≤ s := (inv_le_comm₀ (by linarith) hs).mpr (by dsimp [R]; linarith [inv_pos.mpr hs])
  have hrR : r ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs]
  have hR1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h1R : 1 ≤ R := by linarith
  have hrlo : R⁻¹ ≤ r := hR1.trans hr
  have hlate : ∀ᶠ k in atTop,
      p.AtDepth k s R ∧ p.K k ≤ p.N k ∧
      (∀ q : Fin 3 → ℤ,
        p.μ k {ω | Submission.Lib.K4CommonLocalChoice.cell (p.N k ^ (-r))
          (p.x k ω.1 ω.2 ∘ Fin.castSucc) = q} ≤
            ENNReal.ofReal (p.N k ^ A * (p.N k ^ (-r)) ^ 3)) ∧
      (∀ (σ : Measure (α × ℝ)) (Z : α × ℝ → Fin 3 → ℝ) (G : MvPolynomial (Fin 3) ℝ),
        G.totalDegree ≤ 2 → ENNReal.ofReal (p.N k ^ (-A)) ≤ σ univ →
        (∀ q : Fin 3 → ℤ,
          σ {ω | Submission.Lib.K4CommonLocalChoice.cell (p.N k ^ (-r)) (Z ω) = q} ≤
            ENNReal.ofReal (p.N k ^ A * (p.N k ^ (-r)) ^ 3)) →
        (∀ᵐ ω ∂σ, (∀ j, |Z ω j| ≤ p.N k ^ A) ∧ |eval (Z ω) G| ≤ p.N k ^ A) →
        ∀ e, |G.coeff e| ≤ p.N k ^ r) := by
    filter_upwards [h.prepared R hR, h.caps R hR, h.subpower.2 1 (by norm_num),
      eventually_quadratic_grid_calibration h.scale h.scale_limit hA] with k h_at h_caps hKN hcal
    have hN : 2 ≤ p.N k := h.scale k
    have hNp : 0 < p.N k := by linarith
    have hN1 : 1 ≤ p.N k := by linarith
    have hKN' : p.K k ≤ p.N k := by simpa only [Real.rpow_one] using hKN
    have hK0 : 0 ≤ p.K k := by linarith [h.subpower.1 k]
    have h6 : 6 * p.K k ^ 2 ≤ p.N k ^ A := by
      calc
        _ ≤ 6 * (p.N k) ^ 2 := by gcongr
        _ ≤ (p.N k) ^ 5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3]
        _ ≤ p.N k ^ A := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hN1 hA5
    refine ⟨h_at s hsR (by linarith), hKN', ?_, ?_⟩
    · intro q
      apply (p.native_base_cell_cap h.basic hN (h.subpower.1 k) (fun q a => ?_) q).trans
      · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h6 (by positivity))
      have hh := (h_caps r 0 1 hrlo hrR le_rfl (by linarith) hR1 h1R).2.1 true q a
      simp only [ite_true, neg_zero, Real.rpow_zero, div_one, mul_zero, sub_zero] at hh
      convert hh using 1
      congr 2
      rw [← Real.rpow_mul_natCast hNp.le]
      congr 1
      ring
    · intro σ Z G
      exact hcal (α × ℝ) σ Z G
  apply p.candidates_of_fixed_gain h.scale hs hv hsU (R₀ := r + 1)
  intro ε hε
  let η := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  have hηε : η ≤ ε := min_le_left _ _
  have hη1 : η ≤ 1 := min_le_right _ _
  apply ((hpred η hη).and_eventually (hlate.and (h.subpower.2 ε hε))).mono
  rintro k ⟨⟨i, G, hG, hm⟩, ⟨hat, hKN, hcap, hcal⟩, hKε⟩
  have hN := h.scale k
  have hNp : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := by linarith
  have hK1 := h.subpower.1 k
  have hKpos : 0 < p.K k := by linarith
  let E := p.PredictorEvent k s v η i G
  let σ := (p.ρ k).restrict E
  have hE : MeasurableSet E := p.measurableSet_predictorEvent h.basic hat i G
  have hσμ : σ ≤ p.μ k := Measure.restrict_le_self.trans (h.basic k).2.2.2.2.1
  have hmass : ENNReal.ofReal (p.N k ^ (-A)) ≤ σ univ := by
    rw [show σ univ = p.ρ k E by simp [σ]]
    exact (AtDepth.reference_floor_absolute p hat hN hKpos hKN hη1 i).trans hm
  have h6 : 6 * p.K k ^ 2 ≤ p.N k ^ A := by
    calc
      _ ≤ 6 * (p.N k) ^ 2 := by gcongr
      _ ≤ (p.N k) ^ 5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3]
      _ ≤ p.N k ^ A := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hN1 hA5
  have h2N : 2 * p.N k ≤ p.N k ^ A := by
    calc
      _ ≤ (p.N k) ^ 2 := by nlinarith
      _ ≤ p.N k ^ A := by
        convert Real.rpow_le_rpow_of_exponent_le hN1 (show (2 : ℝ) ≤ A by linarith) using 1 <;> norm_num
  have hcoef : ∀ e, |G.coeff e| ≤ p.N k ^ r := by
    apply hcal σ (fun ω => p.x k ω.1 ω.2 ∘ Fin.castSucc) G hG hmass
    · intro q
      exact (hσμ _).trans (hcap q)
    · have hmem : ∀ᵐ ω ∂σ, ω ∈ E := ae_restrict_mem hE
      have hgood := ae_mono hσμ (h.basic k).2.2.2.2.2.2.2.2.2
      filter_upwards [hmem, hgood] with ω hω hh
      obtain ⟨hb, ht, hfit⟩ := hω
      have ht1 := Submission.Obl.k4_balanced_native_packet_transport.Pullback.block_subset_unit
        (p.j k s i) ht
      refine ⟨fun j => (AtDepth.base_bound p hat hN hK1 h.transverse_pos hs.le i hb ht j).trans h6, ?_⟩
      have hscale : p.N k ^ (-s - v) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      have hηN : p.N k ^ η ≤ p.N k := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hη1
      have herr : p.N k ^ η * p.N k ^ (-s - v) ≤ p.N k := by
        exact (mul_le_of_le_one_right (by positivity) hscale).trans hηN
      calc
        _ = |eval (p.x k ω.1 ω.2) (p.P k) -
          (eval (p.x k ω.1 ω.2) (p.P k) - eval (p.x k ω.1 ω.2 ∘ Fin.castSucc) G)| := by congr 1; ring
        _ ≤ |eval (p.x k ω.1 ω.2) (p.P k)| +
          |eval (p.x k ω.1 ω.2) (p.P k) - eval (p.x k ω.1 ω.2 ∘ Fin.castSucc) G| := abs_sub _ _
        _ ≤ p.K k + p.N k := add_le_add (hh.1 ω.2 ht1).1 ((hfit ω.2 ht).trans herr)
        _ ≤ 2 * p.N k := by linarith
        _ ≤ p.N k ^ A := h2N
  refine ⟨i, p.native_polynomial_candidate h.basic i G hN hKpos hKε (by linarith) hG
    (p.residual_coefficient_envelope i G hN (by dsimp [r]; positivity) hcoef) ?_⟩
  apply le_trans _ (hm.trans (measure_mono ?_))
  · gcongr
  · rintro ω ⟨hb, ht, hfit⟩
    refine ⟨hb, ht, fun t ht => (hfit t ht).trans ?_⟩
    gcongr

end Parent
end
end Submission.Obl.k4_general_parent_wide_layer_candidates
