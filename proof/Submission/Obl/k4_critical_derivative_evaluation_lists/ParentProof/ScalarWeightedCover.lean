/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, ScalarWeightedCover.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ScalarBandPreparation
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.DensityRestriction

/-! Adapted from our LOT tree o107 (`k4_finite_narrowness_path_improvement`), session x0353,
`ScalarWeightedCover.lean` (commit 96bcaa7b); namespace and import paths renamed. -/

/-! Heavy coefficient bins for an original continuous incidence law merely
dominated by the trajectory-prior product, rather than equal to a restriction. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Classical
open Submission.Obl.k4_scalar_coefficient_clustering

theorem scalar_weighted_heavy_coefficient_cover (d c ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
        [IsFiniteMeasure μ] (a : α → EuclideanSpace ℝ (Fin 3))
        (D : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
      Measurable a → MeasurableSet D → D ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → μ Dᶜ = 0 →
      μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod volume) →
      (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) →
      (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
      (∀ l t, (l, t) ∈ D →
        (⌊t / (N ^ (-c))⌋, ⌊quadratic (a l) t / (N ^ (-c))⌋) ∈ F) →
      (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r →
        (∃ l, a l ∈ Metric.ball b r) →
        μ {p | |quadratic (a p.1) p.2 - quadratic b p.2| ≤ 3 * r} ≤
          ENNReal.ofReal (N ^ η * r ^ d)) →
      ∃ G : Finset (Fin 3 → ℤ),
        (∀ q ∈ G, ENNReal.ofReal (N ^ (-c * d - ε)) ≤
          μ {p | coefficientCode (N ^ (-c)) (a p.1) = q}) ∧
        (G.card : ℝ) ≤ μ.real Set.univ / N ^ (-c * d - ε) ∧
        μ {p | coefficientCode (N ^ (-c)) (a p.1) ∉ G} <
          ENNReal.ofReal (N ^ (-η)) := by
  obtain ⟨η₀, hη₀, M, hM, hcover⟩ :=
    scalar_heavy_coefficient_cover_of_active_bands d c (ε / 2) hd hd1 hc (by positivity)
  let η := min (η₀ / 64) (ε / 32)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηle : η ≤ η₀ := by
    have := min_le_left (η₀ / 64) (ε / 32)
    dsimp [η]
    linarith
  have hη4 : 4 * η ≤ η₀ := by
    have := min_le_left (η₀ / 64) (ε / 32)
    dsimp [η]
    linarith
  have hη5 : 5 * η ≤ η₀ := by
    have := min_le_left (η₀ / 64) (ε / 32)
    dsimp [η]
    linarith
  have hηε : 4 * η ≤ ε / 2 := by
    have := min_le_right (η₀ / 64) (ε / 32)
    dsimp [η]
    linarith
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp (tendsto_rpow_atTop (by positivity : 0 < 2 * η))) (3 : ℝ))
  refine ⟨η, hη, max M R, hM.trans (le_max_left _ _), ?_⟩
  intro N hN α _ ν μ _ a D F ha hD hunit hDnull hdom hnorm hν hcard hsupport hband
  have hNM : M ≤ N := (le_max_left _ _).trans hN
  have hNR : R ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by linarith [hM.trans hNM]
  have hN1 : 1 ≤ N := by linarith [hM.trans hNM]
  have hpow (u v : ℝ) (huv : u ≤ v) : N ^ u ≤ N ^ v :=
    Real.rpow_le_rpow_of_exponent_le hN1 huv
  have hνfinite : ν Set.univ < ∞ := lt_of_le_of_lt hν ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure ν := ⟨hνfinite⟩
  let m : Measure (α × ℝ) := ν.prod volume
  have hmwindow : m (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) = ν Set.univ := by
    simp only [m, Measure.prod_prod, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  let code : α × ℝ → Fin 3 → ℤ := fun p => coefficientCode (N ^ (-c)) (a p.1)
  have hcode : Measurable code := (measurable_coefficientCode _).comp (ha.comp measurable_fst)
  have hcodes := coefficient_codes_finite a Set.univ (p := N ^ (-c))
    (Real.rpow_pos_of_pos hNpos _) (fun l _ => hnorm l)
  let C := hcodes.toFinset
  have hcodecover : ∀ᵐ p ∂μ, code p ∈ C := by
    apply Filter.Eventually.of_forall
    intro p
    exact hcodes.mem_toFinset.mpr ⟨p.1, Set.mem_univ _, rfl⟩
  have hac : μ ≪ m := Measure.absolutelyContinuous_of_le_smul hdom
  let f := μ.rnDeriv m
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have hlaw : μ = m.withDensity f := (Measure.withDensity_rnDeriv_eq μ m hac).symm
  have hsmall : 2 * N ^ (-3 * η) < N ^ (-η) := by
    have hh := mul_le_mul_of_nonneg_right (hR N hNR)
      (Real.rpow_nonneg hNpos.le (-3 * η))
    have heq : N ^ (2 * η) * N ^ (-3 * η) = N ^ (-η) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [heq] at hh
    linarith [Real.rpow_pos_of_pos hNpos (-3 * η)]
  have hdiscover : ∀ U : Set (α × ℝ), MeasurableSet U →
      ENNReal.ofReal (N ^ (-η)) ≤ μ U →
      ∃ q : Fin 3 → ℤ, ENNReal.ofReal (N ^ (-c * d - ε)) ≤ μ (U ∩ code ⁻¹' {q}) := by
    intro U hU hmass
    let U₀ := U ∩ D
    have hU₀ : MeasurableSet U₀ := hU.inter hD
    have hU₀mass : μ U₀ = μ U := by
      apply measure_congr
      have hfull : ∀ᵐ p ∂μ, p ∈ D := by
        rw [ae_iff]
        exact hDnull
      filter_upwards [hfull] with p hp
      simp only [U₀, mem_inter_iff, hp, and_true]
    have hU₀window : U₀ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := Set.inter_subset_right.trans hunit
    have hmU₀ : m U₀ ≤ ENNReal.ofReal (N ^ η) := by
      calc
        _ ≤ m (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := measure_mono hU₀window
        _ = ν Set.univ := hmwindow
        _ ≤ _ := hν
    let cutoff := ENNReal.ofReal (N ^ (-4 * η))
    have hcut0 : cutoff ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hNpos _)
    have hcutt : cutoff ≠ ∞ := ENNReal.ofReal_ne_top
    obtain ⟨E, hE, hEU, _, hlower, hloss⟩ := density_level_restriction m μ f hf hlaw U₀ hU₀ cutoff
    have hEwindow : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := hEU.trans hU₀window
    have hmEfinite : m E ≠ ∞ := ne_of_lt (lt_of_le_of_lt
      (measure_mono hEwindow) (by rw [hmwindow]; exact hνfinite))
    have hloss' : μ (U₀ \ E) ≤ ENNReal.ofReal (N ^ (-3 * η)) := by
      calc
        _ ≤ cutoff * m U₀ := hloss
        _ ≤ cutoff * ENNReal.ofReal (N ^ η) := mul_le_mul_right hmU₀ cutoff
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le _), ← Real.rpow_add hNpos]
          congr 2
          ring
    have hmassreal : N ^ (-η) ≤ μ.real U₀ := by
      have hmass' : ENNReal.ofReal (N ^ (-η)) ≤ μ U₀ := by rwa [hU₀mass]
      have hh := ENNReal.toReal_mono (measure_ne_top μ U₀) hmass'
      simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _), measureReal_def] using hh
    have hlossreal : μ.real (U₀ \ E) ≤ N ^ (-3 * η) := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hloss'
      simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _), measureReal_def] using hh
    have hsumreal : μ.real E + μ.real (U₀ \ E) = μ.real U₀ := by
      simpa only [Set.inter_eq_right.mpr hEU] using
        (measureReal_inter_add_sdiff (μ := μ) (s := U₀) hE)
    have hdomreal : μ.real E ≤ N ^ η * m.real E := by
      have hh := ENNReal.toReal_mono (by
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmEfinite) (hdom E)
      simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _), measureReal_def] using hh
    have hmEfloor : ENNReal.ofReal (N ^ (-η₀)) ≤ m E := by
      apply (ENNReal.ofReal_le_iff_le_toReal hmEfinite).mpr
      change N ^ (-η₀) ≤ m.real E
      by_contra hnot
      have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) (Real.rpow_pos_of_pos hNpos η)
      have hscale : N ^ η * N ^ (-η₀) ≤ N ^ (-3 * η) := by
        rw [← Real.rpow_add hNpos]
        exact hpow _ _ (by linarith)
      linarith
    have hproductband : ∀ b : EuclideanSpace ℝ (Fin 3), ∀ r : ℝ, N ^ (-c) ≤ r →
        (∃ l, a l ∈ Metric.ball b r) →
        (m.restrict E) {p | |quadratic (a p.1) p.2 - quadratic b p.2| ≤ 3 * r} ≤
          ENNReal.ofReal (N ^ η₀ * r ^ d) := by
      intro b r hr hex
      let Band := {p : α × ℝ | |quadratic (a p.1) p.2 - quadratic b p.2| ≤ 3 * r}
      have hb : cutoff * (m.restrict E) Band ≤ ENNReal.ofReal (N ^ η * r ^ d) := by
        calc
          _ ≤ (μ.restrict U₀) Band := hlower Band
          _ ≤ μ Band := Measure.restrict_le_self _
          _ ≤ _ := hband b r hr hex
      have hdiv : (m.restrict E) Band ≤ ENNReal.ofReal (N ^ η * r ^ d) / cutoff :=
        (ENNReal.le_div_iff_mul_le (Or.inl hcut0) (Or.inl hcutt)).mpr
          (by simpa only [mul_comm] using hb)
      calc
        _ ≤ ENNReal.ofReal (N ^ η * r ^ d) / cutoff := hdiv
        _ = ENNReal.ofReal (N ^ (5 * η) * r ^ d) := by
          rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hNpos _)]
          congr 1
          rw [show -4 * η = -(4 * η) by ring, Real.rpow_neg hNpos.le,
            div_eq_mul_inv, inv_inv]
          rw [show N ^ η * r ^ d * N ^ (4 * η) =
            (N ^ η * N ^ (4 * η)) * r ^ d by ring, ← Real.rpow_add hNpos]
          congr 2
          ring
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (hpow _ _ hη5) (Real.rpow_nonneg ((Real.rpow_nonneg hNpos.le _).trans hr) _))
    obtain ⟨G, hfloor, _, hexcluded⟩ := hcover N hNM α ν a E F ha hE hEwindow
      (fun l => (hnorm l).trans (hpow _ _ hηle))
      (hν.trans (ENNReal.ofReal_le_ofReal (hpow _ _ hηle)))
      (hcard.trans (mul_le_mul_of_nonneg_right (hpow _ _ hηle) (by positivity)))
      (fun l t hlt => hsupport l t (hEU hlt).2) hproductband
    have hG : G.Nonempty := by
      by_contra hn
      have hG0 : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hlt : m E < ENNReal.ofReal (N ^ (-η₀)) := by
        have hbadU : {p : α × ℝ | coefficientCode (N ^ (-c)) (a p.1) ∉ G} = Set.univ := by
          rw [hG0]
          ext p
          simp
        rw [hbadU, Measure.restrict_apply_univ] at hexcluded
        exact hexcluded
      exact not_lt_of_ge hmEfloor hlt
    obtain ⟨q, hq⟩ := hG
    have hqprod : ENNReal.ofReal (N ^ (-c * d - ε / 2)) ≤
        (m.restrict E) (code ⁻¹' {q}) := hfloor q hq
    have hfloorrestore : ENNReal.ofReal (N ^ (-c * d - ε)) ≤
        cutoff * ENNReal.ofReal (N ^ (-c * d - ε / 2)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le _), ← Real.rpow_add hNpos]
      exact ENNReal.ofReal_le_ofReal (hpow _ _ (by linarith))
    refine ⟨q, hfloorrestore.trans ?_⟩
    calc
      _ ≤ cutoff * (m.restrict E) (code ⁻¹' {q}) := mul_le_mul_right hqprod cutoff
      _ ≤ (μ.restrict U₀) (code ⁻¹' {q}) := hlower _
      _ = μ ((code ⁻¹' {q}) ∩ U₀) := Measure.restrict_apply (hcode (measurableSet_singleton q))
      _ ≤ μ (U ∩ code ⁻¹' {q}) := measure_mono (by
        intro p hp
        exact ⟨hp.2.1, hp.1⟩)
  obtain ⟨G, _, hfloor, hcount, hexcluded⟩ := finite_heavy_code_cover_of_dense_discovery
    μ code hcode C hcodecover (N ^ (-c * d - ε)) (ENNReal.ofReal (N ^ (-η)))
    (Real.rpow_pos_of_pos hNpos _) hdiscover
  exact ⟨G, hfloor, hcount, hexcluded⟩

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
