import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Model
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.CandidateReturn
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.OriginalObservation
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.MassFloors

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation.Data
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α] {cfg : Model α}

/-- The general original law is finite before any affine preparation. -/
theorem Valid.incidence_finite (h : cfg.Valid) (k : ℕ) : IsFiniteMeasure (cfg.μ k) := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  apply finite_original_incidence (cfg.ν k) (cfg.μ k) (cfg.K k) 0 1
    (h.basic k).2.2.2.1
  have hset : {p : α × ℝ | p.2 ∈ Icc (0 : ℝ) 1} = univ ×ˢ Icc (0 : ℝ) 1 := by
    ext p
    simp
  rw [hset]
  exact (h.basic k).2.2.2.2.2.1

/-- Bounded original observations are inherited by any retained law. -/
theorem Valid.original_observation_bounds (h : cfg.Valid) (k : ℕ) :
    ∀ᵐ p ∂cfg.μ k,
      (∀ i : Fin 3, |point (cfg.b k p.1) p.2 i.castSucc| ≤ cfg.K k) ∧
      |eval (point (cfg.b k p.1) p.2) (cfg.P k)| ≤ cfg.K k := by
  apply original_native_observation_bounds (cfg.ν k) (cfg.μ k) (cfg.b k) (cfg.P k)
    (h.subpower.1 k) (h.basic k).2.2.2.1 (h.basic k).2.2.2.2.2.2.2.2.1
    (h.basic k).2.2.2.2.2.1
  filter_upwards [(h.basic k).2.2.2.2.2.2.2.2.2] with p hp
  intro t ht
  exact (hp.1 t ht).1

/-- The native scalar-depth-zero ceiling gives the exact base grid required
by calibration, at every prescribed fixed mesh exponent. -/
theorem Valid.eventually_native_unit_caps (h : cfg.Valid) {r : ℝ} (hr : 1 ≤ r) :
    ∀ᶠ k in atTop, ∀ (q : Fin 3 → ℤ) (a : ℤ),
      cfg.μ k {p | (fun i : Fin 3 =>
        ⌊point (cfg.b k p.1) p.2 i.castSucc / cfg.N k ^ (-r)⌋) = q ∧
        ⌊eval (point (cfg.b k p.1) p.2) (cfg.P k)⌋ = a} ≤
          ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-r)) ^ (3 : ℕ)) := by
  let R := r + 2
  have hR : 1 < R := by dsimp [R]; linarith
  have hR0 : 0 < R := by linarith only [hR]
  have hR1 : 1 ≤ R := by linarith
  have hinv : R⁻¹ ≤ 1 := (inv_le_one₀ hR0).mpr hR1
  filter_upwards [h.caps R hR] with k hk
  intro q a
  have ha := (hk r 0 1 (hinv.trans hr) (by dsimp [R]; linarith)
    le_rfl (by linarith) hinv (by linarith)).2.1 true q a
  have hN0 : 0 < cfg.N k := by linarith [h.scale k]
  have hgrid : cfg.z k (cfg.N k) r = fun p i =>
      ⌊point (cfg.b k p.1) p.2 i.castSucc / cfg.N k ^ (-r)⌋ := by
    funext p i
    fin_cases i <;> rfl
  have hpower : cfg.N k ^ (-3 * r) = (cfg.N k ^ (-r)) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    norm_num
    ring
  simpa only [hgrid, ite_true, neg_zero, Real.rpow_zero, div_one, mul_zero,
    sub_zero, hpower, Submission.Obl.k4_critical_switching_state_preparation.Data.x, point] using ha

/-- A fine affine-source alternative at every tolerance yields the original
homogeneous quadratic or velocity alternative. -/
theorem Valid.candidates_of_affine_candidates
    (h : cfg.Valid) {C : ℝ} (hC : 1 ≤ C) (hcal : MeshCalibration C)
    (hcandidates : cfg.AffineCandidates) : cfg.Candidates := by
  obtain ⟨R₀, hR₀, hcand⟩ := hcandidates
  let B : ℝ := 5 * cfg.U + 5
  let r : ℝ := calibrationPower C B + 1
  let M : ℝ := calibrationPower C B + B + 1
  let R : ℝ := max R₀ (M + 2)
  have hB5 : 5 ≤ B := by dsimp [B]; linarith only [h.depth_pos]
  have hB1 : 1 ≤ B := by linarith only [hB5]
  have hr1 : 1 ≤ r := by
    have hp := calibrationPower_pos hC hB1
    dsimp [r]
    linarith only [hp]
  have hMR : M ≤ R := (by linarith only : M ≤ M + 2).trans (le_max_right _ _)
  have hR₀R : R₀ ≤ R := le_max_left _ _
  have hR : 1 < R := hR₀.trans_le hR₀R
  have hR0 : 0 < R := by linarith only [hR]
  have hR₀0 : 0 < R₀ := by linarith only [hR₀]
  have hinv : R⁻¹ ≤ R₀⁻¹ := inv_anti₀ hR₀0 hR₀R
  refine ⟨R, hR, ?_⟩
  intro ε hε
  let ζ : ℝ := min (ε / 4) (min (R₀⁻¹ / 2) (1 / 2))
  have hζ : 0 < ζ := by
    dsimp [ζ]
    exact lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hζε : ζ ≤ ε := by
    have hz := min_le_left (ε / 4) (min (R₀⁻¹ / 2) (1 / 2))
    dsimp [ζ]
    linarith only [hz, hε]
  have hζ4 : 4 * ζ ≤ ε := by
    have hz := min_le_left (ε / 4) (min (R₀⁻¹ / 2) (1 / 2))
    dsimp [ζ]
    linarith only [hz]
  have hζv : ζ ≤ R₀⁻¹ := by
    have hz := (min_le_right (ε / 4) (min (R₀⁻¹ / 2) (1 / 2))).trans
      (min_le_left (R₀⁻¹ / 2) (1 / 2))
    dsimp [ζ]
    linarith only [hz, inv_pos.mpr hR₀0]
  have hζ1 : ζ ≤ 1 := by
    have hz := (min_le_right (ε / 4) (min (R₀⁻¹ / 2) (1 / 2))).trans
      (min_le_right (R₀⁻¹ / 2) (1 / 2))
    dsimp [ζ]
    linarith only [hz]
  have htwo : ∀ᶠ k in atTop, (2 : ℝ) ≤ cfg.N k ^ ζ :=
    ((tendsto_rpow_atTop hζ).comp h.scale_limit).eventually_ge_atTop 2
  have hlarge : ∀ᶠ k in atTop, C ≤ cfg.N k := h.scale_limit.eventually_ge_atTop C
  have hlevels := h.eventually_return_levels R₀ hR₀
  have hcaps := h.eventually_native_unit_caps hr1
  have hlate := (h.subpower.2 ζ hζ).and ((h.subpower.2 1 (by norm_num)).and
    (htwo.and (hlarge.and (hlevels.and hcaps))))
  apply ((hcand ζ hζ).and_eventually hlate).mono
  rintro k ⟨⟨s, v, i, hs0, hsR, hv0, hvR, hsvU, hbranch⟩,
    hKζ, hKN, htwo, hCN, hlevels, hcaps⟩
  simp only [Real.rpow_one] at hKN
  have hN : 2 ≤ cfg.N k := h.scale k
  have hN0 : 0 < cfg.N k := by linarith only [hN]
  have hN1 : 1 ≤ cfg.N k := by linarith only [hN]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 < cfg.K k := by linarith only [hK]
  have hs : 0 < s := lt_of_lt_of_le (inv_pos.mpr hR₀0) hs0
  have hv : 0 < v := lt_of_lt_of_le (inv_pos.mpr hR₀0) hv0
  have hsU : s ≤ cfg.U := by linarith only [hsvU, hv]
  have hlevel := hlevels s hs0 hsU
  have hNζε : cfg.N k ^ ζ ≤ cfg.N k ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN1 hζε
  refine ⟨s, v, i, hinv.trans hs0, hsR.trans hR₀R, hinv.trans hv0, hvR.trans hR₀R, hsvU, ?_⟩
  rcases hbranch with haff | hvel
  · obtain ⟨σ, L, hσρ, hmass, hsource⟩ := haff
    have hσμ := hσρ.trans (h.basic k).2.2.2.2.1
    let : IsFiniteMeasure (cfg.μ k) := h.incidence_finite k
    let : IsFiniteMeasure σ := isFiniteMeasure_of_le (cfg.μ k) hσμ
    have hmassPower : ENNReal.ofReal (cfg.N k ^ (-B)) ≤ σ univ := by
      apply original_candidate_power_floor hN hK hKN h.dimension_nonneg
        h.dimension_lt_one.le h.rate_pos.le h.rate_le_one hs.le hv.le hsvU hζ1
        hlevel.time_upper ?_ hmass
      simpa only [h.equal_rate] using hlevel.prior_lower i
    have hobs := h.original_observation_bounds k
    have hbase : ∀ᵐ p ∂σ,
        ∀ e : Fin 3, |point (cfg.b k p.1) p.2 e.castSucc| ≤ cfg.N k ^ B := by
      filter_upwards [ae_mono hσμ hobs] with p hp
      intro e
      exact (hp.1 e).trans (hKN.trans (by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hN1 hB1))
    have hcapPower := original_base_cap_le_power (cfg.μ k) σ hσμ (cfg.b k) (cfg.P k)
      hN hK hKN hB5 (Real.rpow_pos_of_pos hN0 (-r)) (hobs.mono fun p hp => hp.2) hcaps
    have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN0 _
    have hc : 0 < cfg.N k ^ (-s - v) := Real.rpow_pos_of_pos hN0 _
    have hJ : 1 ≤ cfg.N k ^ ζ := Real.one_le_rpow hN1 hζ.le
    have hsmall : cfg.N k ^ ζ * cfg.N k ^ (-s - v) ≤ cfg.N k ^ (-s) := by
      rw [← Real.rpow_add hN0]
      apply Real.rpow_le_rpow_of_exponent_le hN1
      linarith only [hζv.trans hv0]
    have hfitLoss : 2 * cfg.K k * cfg.N k ^ ζ ≤ cfg.N k ^ ε := by
      calc
        2 * cfg.K k * cfg.N k ^ ζ ≤ cfg.N k ^ ζ * cfg.N k ^ ζ * cfg.N k ^ ζ := by gcongr
        _ = cfg.N k ^ (3 * ζ) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
          congr 1
          ring
        _ ≤ cfg.N k ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hζ4, hζ])
    have hcalValue : 3 * cfg.K k * cfg.N k ^ (-s) ≤ cfg.N k ^ B := by
      have ha1 : cfg.N k ^ (-s) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith only [hs])
      calc
        3 * cfg.K k * cfg.N k ^ (-s) ≤ 3 * cfg.N k := by
          calc
            _ ≤ 3 * cfg.N k * cfg.N k ^ (-s) := by gcongr
            _ ≤ 3 * cfg.N k * 1 := mul_le_mul_of_nonneg_left ha1 (by positivity)
            _ = _ := by ring
        _ ≤ cfg.N k ^ (3 : ℕ) := by
          have hsq : (3 : ℝ) ≤ cfg.N k ^ (2 : ℕ) := by nlinarith only [hN]
          calc
            3 * cfg.N k ≤ cfg.N k ^ (2 : ℕ) * cfg.N k :=
              mul_le_mul_of_nonneg_right hsq hN0.le
            _ = _ := by ring
        _ ≤ cfg.N k ^ B := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith only [hB5])
    have hfloor : cfg.N k ^ (-ε) ≤ (cfg.K k)⁻¹ := by
      rw [Real.rpow_neg hN0.le]
      exact inv_anti₀ hK0 (hKζ.trans hNζε)
    have hsource' : ∀ᵐ p ∂σ,
        p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
        (∀ e : Fin 3, |point (cfg.b k p.1) p.2 e.castSucc| ≤ cfg.N k ^ B) ∧
        trajectoryFit (cfg.b k p.1) (cfg.F k s i) (I (cfg.T k s) (cfg.j k s i))
          (cfg.K k) (cfg.N k ^ (-s)) ∧
        (∀ t ∈ I (cfg.T k s) (cfg.j k s i),
          |eval (point (cfg.b k p.1) t) (affineBase L) - point (cfg.b k p.1) t 3| ≤
            cfg.N k ^ ζ * cfg.N k ^ (-s - v)) ∧
        cfg.N k ^ (-ε) ≤ |eval (point (cfg.b k p.1) p.2) (pderiv (3 : Fin 4) (cfg.F k s i))| := by
      filter_upwards [hsource, hbase, ae_mono hσμ (hlevel.floor i)] with p hp hb hf
      refine ⟨hp.1, hp.2.1, hb, ?_, hp.2.2, hfloor.trans (hf hp.1 hp.2.1)⟩
      exact hlevel.fitted i p.1 hp.1
    obtain ⟨Q, hQ, hcoeff, hreturn⟩ := original_candidate_of_affine_source hcal hC
      hN hCN hB1 (cfg.ρ k) σ hσρ (cfg.b k) (h.basic k).1 (cfg.B k s i)
      (I (cfg.T k s) (cfg.j k s i)) (cfg.F k s i) (cfg.P k) (hlevel.degree i) L
      ha hc hK0.le hJ hsmall hfitLoss hcalValue hmassPower hcapPower hsource'
    left
    refine ⟨Q, hQ, ?_, ?_⟩
    · intro e
      have hA : 1 ≤ (1 + ∑ f ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff f|) +
          ∑ f ∈ (cfg.P k).support, |(cfg.P k).coeff f| := by
        have hf : 0 ≤ ∑ f ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff f| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        have hp : 0 ≤ ∑ f ∈ (cfg.P k).support, |(cfg.P k).coeff f| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
      exact (hcoeff e).trans (mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le hN1 hMR)
        (Real.rpow_le_rpow_of_exponent_le hA hMR) (by positivity) (by positivity))
    · have hweight : ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) ≤
          ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ζ) / (2 : ℝ) ^ cfg.T k s) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hζε])
      exact (mul_le_mul_left hweight _).trans (hmass.trans hreturn)
  · obtain ⟨z, hz, hmass⟩ := hvel
    right
    refine ⟨z, ?_, ?_⟩
    · intro e
      exact (hz e).trans (Real.rpow_le_rpow_of_exponent_le hN1 hR₀R)
    · have hweight : ENNReal.ofReal (cfg.N k ^ (-ε) / (2 : ℝ) ^ cfg.T k s) ≤
          ENNReal.ofReal (cfg.N k ^ (-ζ) / (2 : ℝ) ^ cfg.T k s) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hζε])
      refine (mul_le_mul_left hweight _).trans (hmass.trans (measure_mono ?_))
      intro p hp
      refine ⟨hp.1, hp.2.1, hp.2.2.trans ?_⟩
      exact mul_le_mul_of_nonneg_right hNζε (by positivity)

end Model

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
