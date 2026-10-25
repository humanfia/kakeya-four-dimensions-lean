/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/NarrowWidths.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_true_terminal_lifting.Step
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem

/-! Narrow-width deletion while retaining the actual original chart labels.
The packet geometry and aggregate discard are accepted o094 estimates.
The local concentration argument is adapted from the internal narrow-packet
step of here:o094/TrueSystem.lean (accepted packets_of_trueSystem); its
public output does not retain the original chart-index injection. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowWidths

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

/-- A narrow true packet is mostly in the ORIGINAL angular exception. -/
theorem packet_concentrated {μ : Measure (Coeff × ℝ)}
    {G : (((Fin 2 → ℝ) × ℤ) × ℤ) → ℝ≥0∞} (hG : Measurable G)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmap : μ.map (obsG a b) = ((volume.prod Measure.count).prod Measure.count).withDensity G)
    {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) {A : Set Coeff}
    {s q u v J Λ β θ : ℝ} (hq : 0 < q) (hJ : 0 < J) (hΛ : 0 < Λ) (hθ : 0 ≤ θ)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc s (s + q),
      |spatial l t - (u + v * t)| ≤ Λ * J ∧
        |hidden l t - f t (spatial l t)| ≤ Λ * a)
    (hnarrow : 4 * (Λ * J) ≤ b * q)
    (hfloor : ENNReal.ofReal (β * J * q / Λ) ≤ μ (A ×ˢ Icc s (s + q)))
    (hsmall : 16 * Λ ^ 2 * (2 * Λ + 3) * θ ≤ β) :
    μ (A ×ˢ Icc s (s + q)) ≤ 2 * μ ((A ×ˢ Icc s (s + q)) ∩
      {z | ENNReal.ofReal θ < G (obsG a b z)}) := by
  have hd := narrow_packet_diff_le hG ha hb hmap hf hq (mul_pos hΛ hJ).le
    hΛ.le hconf hnarrow (ENNReal.ofReal θ)
  apply le_two_mul_inter_of_diff_le μ (by finiteness) hd
  apply le_trans _ hfloor
  rw [← ENNReal.ofReal_mul hθ, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have key := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hJ.le hq.le)
  rw [le_div_iff₀ hΛ]
  nlinarith [key]

/-- Incidences of a scalar exact-form code have no time atoms, directly
from their original product-prior domination. -/
theorem mu_time_atom (p : Code) (k : ℕ) (g : Fin (W p k)) (t : ℝ) :
    mu p k g (univ ×ˢ {t}) = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ (ν p k g).prod volume (univ ×ˢ {t}) := Measure.restrict_le_self _
    _ = 0 := by rw [Measure.prod_prod, measure_singleton, mul_zero]

/-- The literal full prior rectangles of a scalar chart are almost
disjoint in each original world, including dyadic endpoints. -/
theorem rectangles_inter_null {p : Code} {B k : ℕ} {r b h ε : ℝ} {truth : Bool}
    (Q : ChartW p B r b h ε truth k) (i i' : Fin Q.n) (hne : i ≠ i')
    (hworld : Q.γ i = Q.γ i') :
    mu p k (Q.γ i) ((Q.A i ×ˢ I Q.T (Q.j i)) ∩ (Q.A i' ×ˢ I Q.T (Q.j i'))) = 0 := by
  by_cases hblock : Q.j i = Q.j i'
  · have hA := Q.hcd.2.2.2.1 i i' hne hworld hblock
    have hempty : (Q.A i ×ˢ I Q.T (Q.j i)) ∩ (Q.A i' ×ˢ I Q.T (Q.j i')) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz, hz'⟩
      exact Set.disjoint_left.mp hA hz.1 hz'.1
    rw [hempty, measure_empty]
  · exact measure_blocks_inter_zero (mu_time_atom p k (Q.γ i)) Q.T hblock (Q.A i) (Q.A i')

/-- The full original rectangle mass of the actual narrow labels. -/
noncomputable def narrowMass {p : Code} {B k : ℕ} {r b h ε : ℝ}
    (Q : ChartW p B r b h ε true k) (vwidth : ℝ) : ℝ≥0∞ :=
  let bad := Finset.univ.filter (fun i : Fin Q.n =>
    4 * (N p k ^ ε * Q.J i) ≤ vwidth / (2 : ℝ) ^ Q.T)
  ∑ i ∈ bad, ENNReal.ofReal (ω p k (Q.γ i)) *
    mu p k (Q.γ i) (Q.A i ×ˢ I Q.T (Q.j i))

/-- The ACTUAL narrow labels have at most twice the original angular
exceptional mass. No replacement atlas or conditioned prior is chosen. -/
theorem weighted_narrow_mass_le {p : Code} {B k : ℕ} {r b₀ h ε : ℝ}
    (Q : ChartW p B r b₀ h ε true k) (hN : 0 < N p k)
    {vwidth θ : ℝ} (hb : 0 < vwidth) (hθ : 0 ≤ θ)
    (G : Fin (W p k) → (((Fin 2 → ℝ) × ℤ) × ℤ) → ℝ≥0∞)
    (hG : ∀ g, Measurable (G g))
    (hmap : ∀ g, (mu p k g).map (obsG (N p k ^ (-r)) vwidth) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (G g))
    (hsmall : 16 * (N p k ^ ε) ^ 2 * (2 * N p k ^ ε + 3) * θ ≤ N p k ^ (-f p r)) :
    let bad := Finset.univ.filter (fun i : Fin Q.n =>
      4 * (N p k ^ ε * Q.J i) ≤ vwidth / (2 : ℝ) ^ Q.T)
    (∑ i ∈ bad, ENNReal.ofReal (ω p k (Q.γ i)) *
      mu p k (Q.γ i) (Q.A i ×ˢ I Q.T (Q.j i))) ≤
      2 * ∑ g, ENNReal.ofReal (ω p k g) *
        mu p k g {z | ENNReal.ofReal θ < G g (obsG (N p k ^ (-r)) vwidth z)} := by
  classical
  intro bad
  apply weighted_bad_le (fun g => ENNReal.ofReal (ω p k g)) (mu p k) Q.γ
    (fun i => Q.A i ×ˢ I Q.T (Q.j i))
    (fun g => {z | ENNReal.ofReal θ < G g (obsG (N p k ^ (-r)) vwidth z)}) bad
    (fun i => (Q.hcd.2.2.1 i).1.prod measurableSet_Icc)
    (fun g => measurableSet_lt measurable_const ((hG g).comp (measurable_obsG _ _)))
    (fun i _ i' _ hne hw => rectangles_inter_null Q i i' hne hw)
  intro i hi
  have hnarrow := (Finset.mem_filter.mp hi).2
  obtain ⟨_, hJ, _, _, _, hP, _, _, _, _, hfit, hfloor⟩ := Q.hcd.2.2.2.2.2.1 i
  let dt : ℝ := 1 / (2 : ℝ) ^ Q.T
  let t₀ : ℝ := ((Q.j i : ℕ) : ℝ) / (2 : ℝ) ^ Q.T
  have hI : I Q.T (Q.j i) = Icc t₀ (t₀ + dt) := by
    dsimp [I, t₀, dt]
    rw [add_div]
  rw [hI]
  apply packet_concentrated (β := N p k ^ (-f p r)) (hG (Q.γ i)) (Real.rpow_pos_of_pos hN _) hb (hmap (Q.γ i))
    (isQuad2_eval (Q.P i) hP) (by dsimp [dt]; positivity) hJ
    (Real.rpow_pos_of_pos hN _) hθ
  · intro l hl t ht
    have hh := hfit l hl t (by rwa [hI])
    constructor
    · have heq : spatial l t - (Q.u i + Q.v i * t) =
          Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y l t - Q.u i - t * Q.v i := by
        dsimp [spatial, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y]
        ring
      rw [heq]
      exact hh.1
    · exact hh.2
  · simpa only [dt, div_eq_mul_inv, one_mul] using hnarrow
  · have hfloor' := (hfloor rfl).trans
      (measure_mono ((Q.hcd.2.2.2.2.1 i).trans inter_subset_right))
    rw [hI] at hfloor'
    apply le_trans _ hfloor'
    apply le_of_eq
    congr 1
    dsimp [dt]
    field_simp
  · exact hsmall

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowWidths
