/-
Adapted from this LOT tree, obligation o093, session x0535, commit 05931f40,
Submission/Obl/k4_scalar_critical_path_terminal/ActualPacketGraphs.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PacketGraphBounds
import Submission.Obl.k4_scalar_true_terminal_lifting.Step
import Submission.Obl.k4_scalar_normalized_exact_refinement.Mass
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.BinBounds

/-! Apply the accepted scalar quadratic estimate to an actual TRUE chart
under a later current law. Its full original prior and true floor supply
the calibration; the current floor and observation ceiling are separate. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ActualPacketGraphs

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

noncomputable section

def graphLambda (X B H : ℝ) : ℝ := (2 * B * H * X ^ 2 * (2 * X + 3))⁻¹

theorem graphLambda_pos {X B H : ℝ} (hX : 0 < X) (hB : 0 < B) (hH : 0 < H) :
    0 < graphLambda X B H := by
  unfold graphLambda
  positivity

/-- The predictor is bounded on its entire original time block and at
arbitrary spatial arguments, using the SAME full prior and current law. -/
theorem actual_packet_graph_bound {p : Code} (hp : Exact p)
    {B₀ k : ℕ} {r b h ε : ℝ} (Q : ChartW p B₀ r b h ε true k)
    (hr : 0 ≤ r) (d : Fin Q.n) (ρ : Measure (Coeff × ℝ))
    (B H : ℝ) (hB : 0 < B) (hH : 0 < H)
    (hcap : ρ.map (obsL (N p k ^ (-r))) ≤
      ENNReal.ofReal (B * N p k ^ (-f p r)) • (volume.prod Measure.count))
    (hfloor : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ Q.T)⁻¹) *
      ν p k (Q.γ d) (Q.A d) ≤ ρ (Q.A d ×ˢ I Q.T (Q.j d)))
    (t : ℝ) (ht : t ∈ I Q.T (Q.j d)) (y₀ : ℝ) :
    |MvPolynomial.eval ![t, y₀] (Q.P d)| ≤
      186624 * (4 * N p k ^ ε) *
        (3 + |y₀ - (Q.u d + Q.v d * t)| / (N p k ^ ε * Q.J d)) ^ 2 /
          (graphLambda (N p k ^ ε) B H) ^ 4 := by
  let X := N p k ^ ε
  let q : ℝ := ((2 : ℝ) ^ Q.T)⁻¹
  let t₀ : ℝ := ((Q.j d : ℕ) : ℝ) / (2 : ℝ) ^ Q.T
  have hN : 0 < N p k := by linarith [hp.1.1 k]
  have hN1 : 1 ≤ N p k := by linarith [hp.1.1 k]
  have hX : 0 < X := Real.rpow_pos_of_pos hN _
  have hq : 0 < q := by dsimp [q]; positivity
  have hI : I Q.T (Q.j d) = Icc t₀ (t₀ + q) := by
    dsimp [I, t₀, q]
    rw [← one_div, add_div]
  obtain ⟨_, hJ, _, _, _, hP, _, hcoeff, _, _, hfit, htrue⟩ := Q.hcd.2.2.2.2.2.1 d
  have hconf : ∀ l ∈ Q.A d, ∀ s ∈ Icc t₀ (t₀ + q),
      |spatial l s - (Q.u d + Q.v d * s)| ≤ X * Q.J d ∧
      |hidden l s - MvPolynomial.eval ![s, spatial l s] (Q.P d)| ≤ X * N p k ^ (-r) := by
    intro l hl s hs
    have hh := hfit l hl s (by rwa [hI])
    refine ⟨?_, hh.2⟩
    have heq : spatial l s - (Q.u d + Q.v d * s) =
        Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y l s - Q.u d - s * Q.v d := by
      dsimp [spatial, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y]
      ring
    rw [heq]
    exact hh.1
  have hval : ∀ l ∈ Q.A d, ∀ s ∈ Icc t₀ (t₀ + q),
      |MvPolynomial.eval ![s, spatial l s] (Q.P d)| ≤ 4 * X := by
    intro l hl s hs
    have hsI : s ∈ I Q.T (Q.j d) := by rwa [hI]
    have hx := Submission.Obl.k4_scalar_true_atlas_terminal_lists.trajectory_hidden_bound
      l s X hX.le (hcoeff l hl).2 (block_subset_unit Q.T (Q.j d) hsI)
    have hscale : N p k ^ (-r) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hdiff := (hconf l hl s hs).2
    have heq : MvPolynomial.eval ![s, spatial l s] (Q.P d) =
        (MvPolynomial.eval ![s, spatial l s] (Q.P d) - hidden l s) + hidden l s := by ring
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_sub_comm]
    change |hidden l s - MvPolynomial.eval ![s, spatial l s] (Q.P d)| + |hidden l s| ≤ _
    change |hidden l s| ≤ 3 * X at hx
    nlinarith [mul_le_mul_of_nonneg_left hscale hX.le]
  have hselected : mu p k (Q.γ d) (Q.C d) ≤
      ENNReal.ofReal q * ν p k (Q.γ d) (Q.A d) := by
    apply Submission.Obl.k4_scalar_normalized_exact_refinement.selected_mass_le_assignment
      (ν p k (Q.γ d)) (mu p k (Q.γ d)) Measure.restrict_le_self
      (Q.A d) (Q.C d) t₀ q
    rw [← hI]
    exact (Q.hcd.2.2.2.2.1 d).trans inter_subset_right
  have hcurrent : ENNReal.ofReal (N p k ^ (-f p r) * Q.J d /
      (H * X * (2 : ℝ) ^ Q.T)) ≤ ρ (Q.A d ×ˢ I Q.T (Q.j d)) := by
    calc
      _ = (ENNReal.ofReal H)⁻¹ *
          ENNReal.ofReal (N p k ^ (-f p r) * Q.J d / (X * (2 : ℝ) ^ Q.T)) := by
        rw [← ENNReal.ofReal_inv_of_pos hH, ← ENNReal.ofReal_mul (inv_nonneg.mpr hH.le)]
        congr 1
        field_simp
      _ ≤ (ENNReal.ofReal H)⁻¹ * (ENNReal.ofReal q * ν p k (Q.γ d) (Q.A d)) :=
        mul_le_mul' le_rfl ((htrue rfl).trans hselected)
      _ ≤ _ := by simpa only [mul_assoc, q] using hfloor
  have hcal : (B * N p k ^ (-f p r)) * (2 * X + 3) *
      (graphLambda X B H * (q * (2 * (X * Q.J d)))) =
      N p k ^ (-f p r) * Q.J d / (H * X * (2 : ℝ) ^ Q.T) := by
    dsimp [graphLambda, q]
    field_simp
  apply PacketGraphs.packet_graph_bound (Real.rpow_pos_of_pos hN _)
    (ENNReal.ofReal_pos.mpr (mul_pos hB (Real.rpow_pos_of_pos hN _))).ne'
    ENNReal.ofReal_ne_top hcap (isQuad2_eval (Q.P d) hP) hq (mul_pos hX hJ)
    hX.le (graphLambda_pos hX hB hH) hconf hval ?_ t (by rwa [← hI]) y₀
  calc
    _ = ENNReal.ofReal ((B * N p k ^ (-f p r)) * (2 * X + 3) *
        (graphLambda X B H * (q * (2 * (X * Q.J d))))) := by
      rw [ENNReal.ofReal_mul (mul_nonneg
        (mul_nonneg hB.le (Real.rpow_nonneg hN.le _)) (by positivity)),
        ENNReal.ofReal_mul (mul_nonneg hB.le (Real.rpow_nonneg hN.le _))]
    _ = _ := congrArg ENNReal.ofReal hcal
    _ ≤ _ := by simpa only [hI] using hcurrent

theorem graph_bound_polynomial {X B H K R : ℝ}
    (hX : 1 ≤ X) (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K)
    (hXK : X ≤ K) (hBK : B ≤ K) (hHK : H ≤ K) (hR : 0 ≤ R) (hRK : R ≤ 2 * K) :
    186624 * (4 * X) * (3 + R) ^ 2 / (graphLambda X B H) ^ 4 ≤
      186624000000 * K ^ 23 := by
  have hX0 : 0 ≤ X := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hD : 2 * B * H * X ^ 2 * (2 * X + 3) ≤ 10 * K ^ 5 := by
    calc
      _ ≤ 2 * K * K * K ^ 2 * (5 * K) := by
        gcongr
        linarith
      _ = _ := by ring
  rw [graphLambda, inv_pow, div_inv_eq_mul]
  calc
    _ ≤ 186624 * (4 * K) * (5 * K) ^ 2 * (10 * K ^ 5) ^ 4 := by
      gcongr
      linarith
    _ = _ := by ring

/-- The full fitted assignment tube has a polynomial norm even before
a width lower bound is used to compare it to other physical scales. -/
theorem actual_packet_assignment_tube_bound {p : Code} (hp : Exact p)
    {B₀ k : ℕ} {r b h ε : ℝ} (Q : ChartW p B₀ r b h ε true k)
    (hr : 0 ≤ r) (hε : 0 ≤ ε) (d : Fin Q.n) (ρ : Measure (Coeff × ℝ))
    (B H K : ℝ) (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K)
    (hXK : N p k ^ ε ≤ K) (hBK : B ≤ K) (hHK : H ≤ K)
    (hcap : ρ.map (obsL (N p k ^ (-r))) ≤
      ENNReal.ofReal (B * N p k ^ (-f p r)) • (volume.prod Measure.count))
    (hfloor : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ Q.T)⁻¹) *
      ν p k (Q.γ d) (Q.A d) ≤ ρ (Q.A d ×ˢ I Q.T (Q.j d)))
    (t : ℝ) (ht : t ∈ I Q.T (Q.j d)) (w : ℝ) (hw : w ∈ Icc (-2 : ℝ) 2) :
    |MvPolynomial.eval ![t, Q.u d + t * Q.v d + (N p k ^ ε * Q.J d) * w] (Q.P d)| ≤
      186624000000 * K ^ 23 := by
  have hN : 1 ≤ N p k := by linarith [hp.1.1 k]
  have hX : 1 ≤ N p k ^ ε := Real.one_le_rpow hN hε
  have hJ : 0 < Q.J d := (Q.hcd.2.2.2.2.2.1 d).2.1
  have hwidth : 0 < N p k ^ ε * Q.J d := mul_pos (zero_lt_one.trans_le hX) hJ
  have heq : Q.u d + t * Q.v d + (N p k ^ ε * Q.J d) * w - (Q.u d + Q.v d * t) =
      (N p k ^ ε * Q.J d) * w := by ring
  have hratio : |Q.u d + t * Q.v d + (N p k ^ ε * Q.J d) * w -
      (Q.u d + Q.v d * t)| / (N p k ^ ε * Q.J d) = |w| := by
    rw [heq, abs_mul, abs_of_pos hwidth]
    field_simp
  have h := actual_packet_graph_bound hp Q hr d ρ B H hB hH hcap hfloor t ht
    (Q.u d + t * Q.v d + (N p k ^ ε * Q.J d) * w)
  rw [hratio] at h
  exact h.trans (graph_bound_polynomial hX hB hH hK hXK hBK hHK (abs_nonneg _) (by
    have := abs_le.mpr hw
    linarith))

/-- A common subpower envelope for the loss, ceiling, restored floor
and full-width lower bound yields a fixed polynomial whole-tube norm. -/
theorem actual_packet_tube_bound {p : Code} (hp : Exact p)
    {B₀ k : ℕ} {r b h ε : ℝ} (Q : ChartW p B₀ r b h ε true k)
    (hr : 0 ≤ r) (hε : 0 ≤ ε) (d : Fin Q.n) (ρ : Measure (Coeff × ℝ))
    (B H K : ℝ) (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K)
    (hXK : N p k ^ ε ≤ K) (hBK : B ≤ K) (hHK : H ≤ K)
    (hwidth : (K * (2 : ℝ) ^ Q.T)⁻¹ ≤ Q.J d)
    (hcap : ρ.map (obsL (N p k ^ (-r))) ≤
      ENNReal.ofReal (B * N p k ^ (-f p r)) • (volume.prod Measure.count))
    (hfloor : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ Q.T)⁻¹) *
      ν p k (Q.γ d) (Q.A d) ≤ ρ (Q.A d ×ˢ I Q.T (Q.j d)))
    (t : ℝ) (ht : t ∈ I Q.T (Q.j d)) (w : ℝ) (hw : w ∈ Icc (-2 : ℝ) 2) :
    |MvPolynomial.eval ![t, Q.u d + t * Q.v d + w / (2 : ℝ) ^ Q.T] (Q.P d)| ≤
      186624000000 * K ^ 23 := by
  have hN : 1 ≤ N p k := by linarith [hp.1.1 k]
  have hX : 1 ≤ N p k ^ ε := Real.one_le_rpow hN hε
  have hX0 : 0 < N p k ^ ε := zero_lt_one.trans_le hX
  have hJ : 0 < Q.J d := (Q.hcd.2.2.2.2.2.1 d).2.1
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have htwo : (0 : ℝ) < 2 ^ Q.T := by positivity
  have hJX : (K * (2 : ℝ) ^ Q.T)⁻¹ ≤ N p k ^ ε * Q.J d :=
    hwidth.trans (le_mul_of_one_le_left hJ.le hX)
  have hmult : 1 ≤ K * (2 : ℝ) ^ Q.T * (N p k ^ ε * Q.J d) := by
    rw [← one_div] at hJX
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hK0 htwo)).mp hJX
  have hradius : (2 : ℝ) / 2 ^ Q.T ≤ 2 * K * (N p k ^ ε * Q.J d) := by
    apply (div_le_iff₀ htwo).mpr
    nlinarith
  have hw' : |w| ≤ 2 := abs_le.mpr hw
  have hdist : |Q.u d + t * Q.v d + w / (2 : ℝ) ^ Q.T - (Q.u d + Q.v d * t)| /
      (N p k ^ ε * Q.J d) ≤ 2 * K := by
    have heq : Q.u d + t * Q.v d + w / (2 : ℝ) ^ Q.T - (Q.u d + Q.v d * t) =
        w / (2 : ℝ) ^ Q.T := by ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos hX0 hJ)).mpr
    apply le_trans _ hradius
    rw [abs_div, abs_of_pos htwo]
    exact div_le_div_of_nonneg_right hw' htwo.le
  exact (actual_packet_graph_bound hp Q hr d ρ B H hB hH hcap hfloor t ht _).trans
    (graph_bound_polynomial hX hB hH hK hXK hBK hHK (by positivity) hdist)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ActualPacketGraphs
