import Submission.Obl.k4_raw_localized_native_systems.C.CSample
import Submission.Obl.k4_raw_localized_native_systems.C.LocalizationInterfaces
import Submission.Obl.k4_raw_localized_native_systems.C.OriginalAtlasStage
import Submission.Lib.K4HiddenQuadratic

/-
Adapted from this LOT tree, o178, session x0596, `NativeLaw.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The scalar law of a full-time chart

For a full-time chart with unit normal `n` (tangent coordinates `stripTangent n`,
zero offset) and assignment `A`, the native coefficients of a line of `A` are its
tangential coordinate `Y(t) = n₁ y₀(t) - n₀ y₁(t)` (affine) and its native signal
`X(t) = P(x(t))` (quadratic, interpolated exactly).  The original observation at
depth one determines `(t, Y(t))` exactly and `X(t)` up to `κ δ` (the hidden bin
centre, by the exact Taylor expansion of `P` in the hidden coordinate).  The
coefficients are bounded by eight times the chart slack.

For a measurable good set `G ⊆ A × [0,1]`, the law `ν(A)⁻¹ (ν ⊗ dt)|_G` is a
`RegularScalarLaw` dominated by the conditional prior, and its budget `ν(A)` times
it is `(ν ⊗ dt)|_G`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Lib.K4XInterface (gx)

noncomputable section

/-- The tangential base of an observation for a strip with unit normal `n`. -/
def cBase (n : Plane) (o : Observation) : Plane :=
  WithLp.toLp 2 ![o.1 0, n 1 * o.1 1 - n 0 * o.1 2]

/-- The native signal of an observation: the test at the centre of its hidden bin. -/
def cSignal (P : MvPolynomial (Fin 4) ℝ) (B δ : ℝ) (o : Observation) : ℝ :=
  MvPolynomial.eval ![o.1 0, o.1 1, o.1 2, ((o.2 : ℝ) + 1 / 2) * δ / B] P

theorem measurable_cBase (n : Plane) : Measurable (cBase n) := by
  unfold cBase
  fun_prop

theorem measurable_cSignal (P : MvPolynomial (Fin 4) ℝ) (B δ : ℝ) :
    Measurable (cSignal P B δ) := by
  have hc : Continuous fun v : Fin 4 → ℝ => MvPolynomial.eval v P := MvPolynomial.continuous_eval P
  have hm : Measurable fun o : Observation =>
      (![o.1 0, o.1 1, o.1 2, ((o.2 : ℝ) + 1 / 2) * δ / B] : Fin 4 → ℝ) := by
    refine measurable_pi_iff.2 fun i => ?_
    have h0 : Measurable fun o : Observation => o.1 := measurable_fst
    have hl : Measurable fun o : Observation => (WithLp.ofLp o.1 : Fin 3 → ℝ) :=
      (PiLp.continuous_ofLp 2 _).measurable.comp h0
    fin_cases i
    · show Measurable fun o : Observation => o.1 0
      exact (measurable_pi_apply 0).comp hl
    · show Measurable fun o : Observation => o.1 1
      exact (measurable_pi_apply 1).comp hl
    · show Measurable fun o : Observation => o.1 2
      exact (measurable_pi_apply 2).comp hl
    · show Measurable fun o : Observation => ((o.2 : ℝ) + 1 / 2) * δ / B
      have : Measurable fun o : Observation => ((o.2 : ℤ) : ℝ) :=
        (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp measurable_snd
      exact ((this.add_const _).mul_const _).div_const _
  exact hc.measurable.comp hm

/-- The base of the original observation is the time and the tangential coordinate. -/
theorem cBase_obs (n : Plane) (B δ : ℝ) (z : Point) :
    cBase n (obs B δ z) =
      WithLp.toLp 2 ![z.2, n 1 * x z.1 z.2 1 - n 0 * x z.1 z.2 2] := by
  rfl

/-- The tangential scalar coordinate of a line of the assignment. -/
theorem cCoeff_scalarY (P : MvPolynomial (Fin 4) ℝ) (n : Plane) {A : Set Line} {l : Line}
    (hl : l ∈ A) (t : ℝ) :
    scalarY (nativeCoeff P 0 1 0 (stripTangent n) A l) t = n 1 * x l t 1 - n 0 * x l t 2 := by
  rw [nativeCoeff_eq_clipped, clippedScalarCoeff_eq P 0 1 0 (stripTangent n) hl]
  have h := scalarCoeff_y P 0 1 0 (stripTangent n) l t
  simp only [scalarY]
  rw [h]
  simp [Submission.Obl.k4_raw_localized_native_systems.C.tangentBase, Fin.sum_univ_three,
    gx, x, stripTangent]
  ring

/-- The native scalar coordinate of a line of the assignment is its native signal. -/
theorem cCoeff_scalarX (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (n : Plane)
    {A : Set Line} {l : Line} (hl : l ∈ A) (t : ℝ) :
    scalarX (nativeCoeff P 0 1 0 (stripTangent n) A l) t = MvPolynomial.eval (x l t) P := by
  rw [nativeCoeff_eq_clipped, clippedScalarCoeff_eq P 0 1 0 (stripTangent n) hl]
  have h := scalarCoeff_x P hP 0 1 0 (stripTangent n) l t
  simp only [scalarX]
  rw [h]
  simp only [zero_add, one_mul]
  rfl

/-- The coefficients of a full-time chart are bounded by eight times the slack. -/
theorem cCoeff_bound (P : MvPolynomial (Fin 4) ℝ) (n : Plane) {A : Set Line} {K : ℝ}
    (hK : 0 ≤ K)
    (hY : ∀ l ∈ A, ∀ t ∈ Set.Icc (0 : ℝ) 1, |n 1 * x l t 1 - n 0 * x l t 2| ≤ K)
    (hX : ∀ l ∈ A, ∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (x l t) P| ≤ K)
    (l : Line) (i : Fin 5) :
    |nativeCoeff P 0 1 0 (stripTangent n) A l i| ≤ 8 * K := by
  rw [nativeCoeff_eq_clipped]
  refine clippedScalarCoeff_bound P 0 1 0 (stripTangent n) (by linarith) ?_ l i
  intro l hl i
  have htan : ∀ t, MvPolynomial.eval (gx l t ∘ Fin.castSucc)
      (Submission.Obl.k4_raw_localized_native_systems.C.tangentBase 0 (stripTangent n)) =
        n 1 * x l t 1 - n 0 * x l t 2 := by
    intro t
    simp [Submission.Obl.k4_raw_localized_native_systems.C.tangentBase, Fin.sum_univ_three,
      gx, x, stripTangent]
    ring
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hm : (0 + 1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine scalarCoeff_bound P 0 1 0 (stripTangent n) l hK ?_ ?_ ?_ ?_ ?_ i
  · rw [htan]; exact hY l hl 0 h0
  · rw [zero_add, htan]; exact hY l hl 1 h1
  · exact hX l hl 0 h0
  · exact hX l hl _ hm
  · rw [zero_add]; exact hX l hl 1 h1

/-- **The signal of the original observation.** The test at the centre of the hidden
bin differs from the native signal by at most `K δ`. -/
theorem cSignal_close (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) {B δ K : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) (z : Point)
    (h1 : |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv 3 P)| ≤ K * B)
    (h2 : |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤
      K * B ^ 2) :
    |MvPolynomial.eval (x z.1 z.2) P - cSignal P B δ (obs B δ z)| ≤ K * δ := by
  classical
  set w := x z.1 z.2 with hw
  set j : ℤ := ⌊B * w 3 / δ⌋ with hj
  set s : ℝ := ((j : ℝ) + 1 / 2) * δ / B - w 3 with hs
  have hpt : (![(obs B δ z).1 0, (obs B δ z).1 1, (obs B δ z).1 2,
      (((obs B δ z).2 : ℤ) + 1 / 2) * δ / B] : Fin 4 → ℝ) = Function.update w 3 (w 3 + s) := by
    ext i
    fin_cases i <;> simp [obs, hw, hs, hj, Function.update, x]
  have hsig : cSignal P B δ (obs B δ z) =
      MvPolynomial.eval (Function.update w 3 (w 3 + s)) P := by
    unfold cSignal
    rw [hpt]
  have htaylor := Submission.Lib.K4HiddenQuadratic.eval_update_add P hP w 3 s
  -- the bin centre is within half a bin of the hidden coordinate
  have hfl1 := Int.floor_le (B * w 3 / δ)
  have hfl2 := Int.lt_floor_add_one (B * w 3 / δ)
  have hsabs : |s| ≤ δ / (2 * B) := by
    have e1 : s = ((j : ℝ) + 1 / 2 - B * w 3 / δ) * (δ / B) := by
      rw [hs]; field_simp
    rw [e1, abs_mul, abs_of_pos (div_pos hδ hB)]
    have : |(j : ℝ) + 1 / 2 - B * w 3 / δ| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    calc |(j : ℝ) + 1 / 2 - B * w 3 / δ| * (δ / B) ≤ 1 / 2 * (δ / B) :=
          mul_le_mul_of_nonneg_right this (div_pos hδ hB).le
      _ = δ / (2 * B) := by field_simp
  rw [hsig, htaylor]
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have e2 : |s * MvPolynomial.eval w (MvPolynomial.pderiv 3 P)| ≤ δ / (2 * B) * (K * B) := by
    rw [abs_mul]; exact mul_le_mul hsabs h1 (abs_nonneg _) (by positivity)
  have e3 : |s ^ 2 / 2 * MvPolynomial.eval w (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤
      (δ / (2 * B)) ^ 2 / 2 * (K * B ^ 2) := by
    rw [abs_mul, abs_div, abs_pow, abs_two]
    refine mul_le_mul ?_ h2 (abs_nonneg _) (by positivity)
    have : |s| ^ 2 ≤ (δ / (2 * B)) ^ 2 := pow_le_pow_left₀ hs0 hsabs 2
    linarith
  have e4 : δ / (2 * B) * (K * B) = K * δ / 2 := by field_simp
  have e5 : (δ / (2 * B)) ^ 2 / 2 * (K * B ^ 2) = K * δ ^ 2 / 8 := by field_simp; ring
  have e6 : K * δ ^ 2 / 8 ≤ K * δ / 8 := by
    have : δ ^ 2 ≤ δ := by nlinarith
    have := mul_le_mul_of_nonneg_left this hK
    linarith
  calc |MvPolynomial.eval w P - (MvPolynomial.eval w P + s * MvPolynomial.eval w
        (MvPolynomial.pderiv 3 P) + s ^ 2 / 2 * MvPolynomial.eval w
          (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P)))|
      = |s * MvPolynomial.eval w (MvPolynomial.pderiv 3 P) + s ^ 2 / 2 *
          MvPolynomial.eval w (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| := by
        rw [← abs_neg]; congr 1; ring
    _ ≤ |s * MvPolynomial.eval w (MvPolynomial.pderiv 3 P)| + |s ^ 2 / 2 *
          MvPolynomial.eval w (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| :=
        abs_add_le _ _
    _ ≤ K * δ / 2 + K * δ / 8 := by linarith
    _ ≤ K * δ := by nlinarith [mul_nonneg hK hδ.le]

end

end Submission.Obl.k4_raw_localized_native_systems.C
