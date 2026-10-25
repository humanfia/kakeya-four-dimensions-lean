import Mathlib
import Submission.Obl.k4_finite_row_graph_assembly.Geometry
import Submission.Lib.K4ModelReduction.PowerComparison

/-! Quantitative geometry used after the row normalization. -/

namespace Submission.Obl.k4_finite_projected_horizontal_candidates

open MeasureTheory Set Filter

/-- Two separated velocity witnesses identify the contact row at a common
horizontal location. The full interpolation lemma is imported from o088. -/
theorem contact_row_comparison {K R c0 c1 t Z v1 v2 : ℝ}
    (hK : 1 ≤ K) (hv1 : |v1| ≤ K) (hv2 : |v2| ≤ K)
    (hsep : 1 / K ≤ |v2 - v1|)
    (h1 : |c0 + v1 * c1 + Z - t * v1| ≤ R)
    (h2 : |c0 + v2 * c1 + Z - t * v2| ≤ R) :
    |c0 + Z| ≤ 3 * K ^ 2 * R ∧ |c1 - t| ≤ 2 * K * R := by
  apply Submission.Obl.k4_finite_row_graph_assembly.row_error_of_two_evaluations
    hK hv1 hv2 hsep
  · convert h1 using 1 <;> congr 1 <;> ring
  · convert h2 using 1 <;> congr 1 <;> ring

/-- A contact trajectory inside a horizontal cell lies in the velocity strip
centered at that cell. -/
theorem contact_strip_at_cell {b0 b3 b4 t tc Zc K q delta : ℝ}
    (hcontact : |b4 + b0| ≤ delta)
    (hcell : |b0 + t * b3 - Zc| ≤ K * q)
    (ht : |t - tc| ≤ q) (hv : |b3| ≤ K) :
    |b4 + Zc - tc * b3| ≤ delta + 2 * K * q := by
  have hq : 0 ≤ q := (abs_nonneg _).trans ht
  calc
    _ = |(b4 + b0) - (b0 + t * b3 - Zc) + (t - tc) * b3| := by congr 1; ring
    _ ≤ |(b4 + b0) - (b0 + t * b3 - Zc)| + |(t - tc) * b3| := abs_add_le _ _
    _ ≤ (|b4 + b0| + |b0 + t * b3 - Zc|) + |(t - tc) * b3| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (delta + K * q) + q * K := by
      rw [abs_mul]
      exact add_le_add (add_le_add hcontact hcell)
        (mul_le_mul ht hv (abs_nonneg _) hq)
    _ = _ := by ring

/-- The true major-coordinate packet gives the required fixed horizontal cell
on its whole block. -/
theorem major_packet_at_center {b0 b3 c0 c1 t tc K q : ℝ}
    (hpacket : |b0 + t * b3 - c0 - t * c1| ≤ K * q)
    (ht : |t - tc| ≤ q) (hc : |c1| ≤ K) :
    |b0 + t * b3 - (c0 + tc * c1)| ≤ 2 * K * q := by
  have hq : 0 ≤ q := (abs_nonneg _).trans ht
  calc
    _ = |(b0 + t * b3 - c0 - t * c1) + (t - tc) * c1| := by congr 1; ring
    _ ≤ |b0 + t * b3 - c0 - t * c1| + |(t - tc) * c1| := abs_add_le _ _
    _ ≤ K * q + q * K := by
      rw [abs_mul]
      exact add_le_add hpacket (mul_le_mul ht hc (abs_nonneg _) hq)
    _ = _ := by ring

/-- The sharper strip estimate directly in the true packet's coordinates. -/
theorem contact_strip_in_packet {b0 b3 b4 c0 c1 t tc K q delta : ℝ}
    (hcontact : |b4 + b0| ≤ delta)
    (hpacket : |b0 + t * b3 - c0 - t * c1| ≤ K * q)
    (ht : |t - tc| ≤ q) (hc : |c1| ≤ K) (hv : |b3| ≤ K) :
    |b4 + (c0 + tc * c1) - tc * b3| ≤ delta + 3 * K * q := by
  have hq : 0 ≤ q := (abs_nonneg _).trans ht
  calc
    _ = |(b4 + b0) - (b0 + t * b3 - c0 - t * c1) + (t - tc) * (b3 - c1)| := by
      congr 1; ring
    _ ≤ |(b4 + b0) - (b0 + t * b3 - c0 - t * c1)| +
        |(t - tc) * (b3 - c1)| := abs_add_le _ _
    _ ≤ (|b4 + b0| + |b0 + t * b3 - c0 - t * c1|) +
        |t - tc| * |b3 - c1| := by
      rw [abs_mul]
      exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ (delta + K * q) + q * (K + K) :=
      add_le_add (add_le_add hcontact hpacket)
        (mul_le_mul ht ((abs_sub _ _).trans (add_le_add hv hc)) (abs_nonneg _) hq)
    _ = _ := by ring

/-- A prior-times-time lower bound prevents the active time set from fitting
inside an interval shorter than the block by more than the domination losses.
The original full assignment weight is canceled only after its positivity and
finiteness have been supplied. -/
theorem time_width_of_prior_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure (α × ℝ))
    {A : Set α} {E : Set (α × ℝ)} {C K q r tc : ℝ}
    (hC : 0 ≤ C) (hK : 0 < K) (hr : 0 ≤ r) (hA : ν A ≠ 0)
    (hdom : μ ≤ ENNReal.ofReal C • (ν.prod volume))
    (hfloor : ENNReal.ofReal (q / K) * ν A ≤ μ E)
    (htime : ∀ᵐ p ∂μ, p ∈ E → p.1 ∈ A ∧ |p.2 - tc| ≤ r) :
    q ≤ 2 * K * C * r := by
  have hsub : E ≤ᵐ[μ] A ×ˢ Icc (tc - r) (tc + r) := by
    filter_upwards [htime] with p hp hpE
    obtain ⟨hpA, hpt⟩ := hp hpE
    refine ⟨hpA, ?_⟩
    obtain ⟨hl, hu⟩ := abs_le.mp hpt
    constructor <;> linarith
  have hu : μ E ≤ ENNReal.ofReal (2 * C * r) * ν A := by
    calc
      _ ≤ μ (A ×ˢ Icc (tc - r) (tc + r)) := measure_mono_ae hsub
      _ ≤ (ENNReal.ofReal C • (ν.prod volume)) (A ×ˢ Icc (tc - r) (tc + r)) := hdom _
      _ = ENNReal.ofReal (2 * C * r) * ν A := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, Real.volume_Icc]
        rw [show tc + r - (tc - r) = 2 * r by ring]
        rw [show 2 * C * r = C * (2 * r) by ring, ENNReal.ofReal_mul hC]
        ring
  have hle : ENNReal.ofReal (q / K) ≤ ENNReal.ofReal (2 * C * r) :=
    (ENNReal.mul_le_mul_iff_left hA (measure_ne_top ν A)).mp (hfloor.trans hu)
  have hreal : q / K ≤ 2 * C * r :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have := (div_le_iff₀ hK).mp hreal
  nlinarith

/-- The preceding time-length comparison forces the contact transverse rate
to be at most the time rate, on every diverging subsequence. -/
theorem transverse_rate_le_time_rate {N L : ℕ → ℝ} {kap ell s : ℝ}
    (hN : Tendsto N atTop atTop)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L k ≤ N k ^ ε)
    (hs : 0 < s)
    (hwidth : ∀ᶠ k in atTop, N k ^ (-kap * s) ≤ L k * N k ^ (-ell * s)) :
    ell ≤ kap := by
  have hh := Submission.Lib.K4ModelReduction.exponent_le_of_subpower_loss N L hN hL hwidth
  nlinarith

end Submission.Obl.k4_finite_projected_horizontal_candidates
