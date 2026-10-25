import Submission.Obl.k4_profile_density_bounds.Profile
import Submission.Obl.k4_profile_density_bounds.Slices

open MeasureTheory Set Filter
open scoped ENNReal

/-!
# Nonnegative coarse profile exponent

If the exponent were negative, typical observations would lie in a high-density set. Its
countable-label projection has small base volume by Markov's inequality, so spread makes its
mass small as well. Together with the exceptional mass this contradicts the `1 / K` lower bound.
-/

namespace Submission.Obl.k4_profile_density_bounds

lemma profile_nonneg_of_spread {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (ν : ℕ → Measure Line) (E : ℕ → Set State)
    (hprob : ∀ k, IsProbabilityMeasure (ν k))
    (hE : ∀ k, MeasurableSet (E k))
    (htimes : ∀ k, E k ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ selected (ν k) (E k) univ)
    (hdens : ∀ k, ∃ G, Measurable G ∧
      (selected (ν k) (E k)).map (observe (N k) 0 0) = reference.withDensity G)
    (hspread : ∀ α : ℝ, 0 < α → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ k in atTop,
      ∀ U : Set Base, volume U ≤ ENNReal.ofReal (N k ^ (-α)) →
        ((ν k).prod volume) {p : State | p.2 ∈ Icc (0 : ℝ) 1 ∧ base p ∈ U} ≤
          ENNReal.ofReal (N k ^ (-θ)))
    {e : ℝ} (htyp : Typical N (fun k => selected (ν k) (E k))
      (fun k => observe (N k) 0 0) e) : 0 ≤ e := by
  by_contra he
  have he0 : e < 0 := lt_of_not_ge he
  let α := -e / 2
  let τ := -e / 2
  have hα : 0 < α := by dsimp [α]; linarith
  have hτ : 0 < τ := hα
  have hexp : -e - τ = α := by dsimp [τ, α]; ring
  obtain ⟨c, hc, htail⟩ := htyp τ hτ
  obtain ⟨θ, hθ, hspr⟩ := hspread α hα
  have hsmall := eventually_sum_lt_inv hN hNt hK hsub 0 hθ hc (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨k, hktyp, hkspr, hksmall⟩ := (htail.and (hspr.and hsmall)).exists
  obtain ⟨G, hG, hlaw⟩ := hdens k
  have hkN : 0 < N k := by linarith [hN k]
  have hkK : 0 < K k := by linarith [hK k]
  let H : Set Observation := {x | ENNReal.ofReal (N k ^ α) ≤ G x}
  have hH : MeasurableSet H := measurableSet_le measurable_const hG
  let U : Set Base := {x | ∃ j : ℤ, ∃ v : Fin 2 → ℤ, ((x, j), v) ∈ H}
  have hmass1 : selected (ν k) (E k) univ ≤ 1 := by
    haveI := hprob k
    exact selected_mass_le_one (ν k) (E k) (htimes k)
  have hU : volume U ≤ ENNReal.ofReal (N k ^ (-α)) := by
    calc
      volume U ≤ reference H := volume_baseProj_le hH
      _ ≤ ENNReal.ofReal ((N k ^ α)⁻¹) := reference_high_density_le
        (measurable_observe _ _ _) hG hlaw hmass1 (Real.rpow_pos_of_pos hkN α)
      _ = _ := by rw [← Real.rpow_neg hkN.le α]
  have hhigh : selected (ν k) (E k) {p | ENNReal.ofReal (N k ^ α) ≤
      G (observe (N k) 0 0 p)} ≤ ENNReal.ofReal (N k ^ (-θ)) := by
    calc
      _ ≤ selected (ν k) (E k) {p : State | p.2 ∈ Icc (0 : ℝ) 1 ∧ base p ∈ U} := by
        apply measure_mono_ae
        filter_upwards [ae_restrict_mem (hE k)] with p hp hh
        exact ⟨(htimes k hp).2, (observe (N k) 0 0 p).1.2,
          (observe (N k) 0 0 p).2, hh⟩
      _ ≤ ((ν k).prod volume) {p : State | p.2 ∈ Icc (0 : ℝ) 1 ∧ base p ∈ U} :=
        selected_le (ν k) (E k) _
      _ ≤ _ := hkspr U hU
  have hlow : selected (ν k) (E k) {p | G (observe (N k) 0 0 p) <
      ENNReal.ofReal (N k ^ α)} ≤ ENNReal.ofReal (N k ^ (-c)) := by
    refine (measure_mono ?_).trans (hktyp G hG hlaw)
    intro p hp
    exact Or.inl (by simpa only [mem_setOf_eq, hexp] using hp)
  have hu : selected (ν k) (E k) univ ≤
      ENNReal.ofReal (N k ^ (-θ) + N k ^ (-c)) := by
    calc
      _ ≤ selected (ν k) (E k) {p | ENNReal.ofReal (N k ^ α) ≤ G (observe (N k) 0 0 p)} +
          selected (ν k) (E k) {p | G (observe (N k) 0 0 p) < ENNReal.ofReal (N k ^ α)} := by
        simpa only [compl_setOf, not_le] using
          measure_univ_le_add_compl (μ := selected (ν k) (E k))
            {p | ENNReal.ofReal (N k ^ α) ≤ G (observe (N k) 0 0 p)}
      _ ≤ ENNReal.ofReal (N k ^ (-θ)) + ENNReal.ofReal (N k ^ (-c)) := add_le_add hhigh hlow
      _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hlt : ENNReal.ofReal (N k ^ (-θ) + N k ^ (-c)) < ENNReal.ofReal ((K k)⁻¹) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    simpa only [pow_zero, mul_one, one_mul] using hksmall
  exact (not_lt_of_ge (hmass k)) (hu.trans_lt hlt)

end Submission.Obl.k4_profile_density_bounds
