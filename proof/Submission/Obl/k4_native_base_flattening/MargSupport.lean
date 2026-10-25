import Submission.Obl.k4_native_base_flattening.Observation
import Submission.Obl.k4_native_base_flattening.ObservationSupport

namespace Submission.Obl.k4_native_base_flattening

open MeasureTheory Set
open Submission.Obl.k4_profile_density_bounds (Observation reference Base width)
open scoped ENNReal

/-- The explicit observation marginal vanishes outside the finite support of its chart cube. -/
lemma marg_eq_zero_off_cube {L a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ENNReal)
    (hs : ∀ q, f q ≠ 0 → (∀ i, |q.1 i| ≤ L) ∧ (∀ i, |q.2 i| ≤ L))
    (y : Observation) (hy : y ∉ cubeObservationSupport L a b) : marg a b f y = 0 := by
  unfold marg
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro w
  by_cases hw : w ∈ tbin a b ⁻¹' {(y.1.2, y.2)}
  · rw [indicator_of_mem hw]
    by_contra hzero
    obtain ⟨hbase, htrans⟩ := hs (WithLp.ofLp y.1.1, w) hzero
    have hbin : tbin a b w = (y.1.2, y.2) := hw
    apply hy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ∀ i ∈ (univ : Set (Fin 3)), -L ≤ WithLp.ofLp y.1.1 i ∧
        WithLp.ofLp y.1.1 i ≤ L
      intro i _
      exact abs_le.mp (hbase i)
    · have hh : ⌊w 0 / a⌋ = y.1.2 := congrArg Prod.fst hbin
      rw [← hh]
      exact mem_cubeBins ha (htrans 0)
    · change y.2 ∈ Fintype.piFinset (fun _ : Fin 2 => cubeBins L b)
      rw [Fintype.mem_piFinset]
      intro i
      have hv := congrFun (congrArg Prod.snd hbin) i
      change ⌊![w 1, w 2] i / b⌋ = y.2 i at hv
      rw [← hv]
      fin_cases i
      · exact mem_cubeBins hb (htrans 1)
      · exact mem_cubeBins hb (htrans 2)
  · exact indicator_of_notMem hw _

/-- A cube-supported source marginal has polynomially bounded reference support. -/
theorem reference_support_marg_le {L a b : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (hb : 0 < b)
    (f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ENNReal)
    (hs : ∀ q, f q ≠ 0 → (∀ i, |q.1 i| ≤ L) ∧ (∀ i, |q.2 i| ≤ L)) :
    reference {y | marg a b f y ≠ 0} ≤
      ENNReal.ofReal ((2 * L) ^ 3 * (2 * L / a + 5) * (2 * L / b + 5) ^ 2) := by
  apply (measure_mono (t := cubeObservationSupport L a b) ?_).trans
    (reference_cubeObservationSupport_le hL ha hb)
  intro y hy
  by_contra hout
  exact hy (marg_eq_zero_off_cube ha hb f hs y hout)

/-- The marginal density of a source of height `c` in a transverse four-dimensional
cube is at most `c` times the volume of that cube. -/
theorem marg_le_of_cube_support {L a b : ℝ} (hL : 0 ≤ L)
    (f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ENNReal) (c : ENNReal)
    (hc : ∀ q, f q ≤ c)
    (hs : ∀ q, f q ≠ 0 → (∀ i, |q.1 i| ≤ L) ∧ (∀ i, |q.2 i| ≤ L))
    (y : Observation) : marg a b f y ≤ c * ENNReal.ofReal ((2 * L) ^ 4) := by
  let W : Set (Fin 4 → ℝ) := Icc (fun _ => -L) (fun _ => L)
  have hW : MeasurableSet W := measurableSet_Icc
  have hvol : volume W = ENNReal.ofReal ((2 * L) ^ 4) := by
    simp only [W, Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) _).symm
  unfold marg
  calc
    _ ≤ ∫⁻ w, W.indicator (fun _ => c) w := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ W
      · rw [indicator_of_mem hw]
        by_cases hbin : w ∈ tbin a b ⁻¹' {(y.1.2, y.2)}
        · rw [indicator_of_mem hbin]
          exact hc _
        · simp only [indicator_of_notMem hbin]
          exact zero_le
      · have hf0 : f (WithLp.ofLp y.1.1, w) = 0 := by
          by_contra hf0
          have hh := (hs _ hf0).2
          apply hw
          change (∀ i, -L ≤ w i) ∧ ∀ i, w i ≤ L
          exact ⟨fun i => (abs_le.mp (hh i)).1, fun i => (abs_le.mp (hh i)).2⟩
        simp only [indicator_of_notMem hw]
        by_cases hbin : w ∈ tbin a b ⁻¹' {(y.1.2, y.2)}
        · simp [indicator_of_mem hbin, hf0]
        · simp [indicator_of_notMem hbin]
    _ = c * volume W := lintegral_indicator_const hW c
    _ = _ := by rw [hvol]

/-- The reference support of a marginal, uniformly over the chosen depth rectangle. -/
theorem reference_support_marg_power_le (B d e : ℕ) {n r u : ℝ}
    (hn : 2 ≤ n) (hr : 0 ≤ r) (hrd : r ≤ (d : ℝ)) (hu : 0 ≤ u) (hue : u ≤ (e : ℝ))
    (f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ENNReal)
    (hs : ∀ q, f q ≠ 0 → (∀ i, |q.1 i| ≤ n ^ B) ∧ (∀ i, |q.2 i| ≤ n ^ B)) :
    reference {y | marg (width n r) (width n u) f y ≠ 0} ≤
      ENNReal.ofReal (n ^ (6 * B + d + 2 * e + 12)) := by
  apply (measure_mono (t := cubeObservationSupport (n ^ B) (width n r) (width n u)) ?_).trans
    (reference_cubeObservationSupport_power_le B d e hn hr hrd hu hue)
  intro y hy
  by_contra hout
  exact hy (marg_eq_zero_off_cube
    (Submission.Obl.k4_profile_density_bounds.width_pos n r)
    (Submission.Obl.k4_profile_density_bounds.width_pos n u) f hs y hout)

/-- A polynomial pointwise ceiling for every entry of the explicit observation marginal. -/
theorem marg_le_polynomial (A B : ℕ) {n a b : ℝ} (hn : 2 ≤ n)
    (f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ENNReal)
    (hc : ∀ q, f q ≤ ENNReal.ofReal (n ^ A))
    (hs : ∀ q, f q ≠ 0 → (∀ i, |q.1 i| ≤ n ^ B) ∧ (∀ i, |q.2 i| ≤ n ^ B))
    (y : Observation) : marg a b f y ≤ ENNReal.ofReal (n ^ (A + 4 * B + 4)) := by
  have hn0 : 0 < n := by linarith
  refine (marg_le_of_cube_support (by positivity) f (ENNReal.ofReal (n ^ A)) hc hs y).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  have heq : n ^ A * (2 * n ^ B) ^ 4 = 16 * n ^ (A + 4 * B) := by
    simp only [show 4 * B = B * 4 by omega, pow_add, pow_mul]
    ring
  rw [heq]
  exact ENNReal.ofReal_le_ofReal
    (Submission.Obl.k4_real_conic_restoration.absorb_constant hn (by norm_num))

end Submission.Obl.k4_native_base_flattening
