/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/AngularGridCap.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/AngularGridCap.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.NativeGridCap
import Submission.Obl.k4_uncapped_native_capping.UWE.ProjectedAngularCap

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- Interpolate angular caps from finitely many positive original angular
depths. The common normal strip is thinner than every requested scalar bin. -/
theorem native_grid_projected_angular_cap_of_large_depth
    (μ ρ : Measure Incidence) (hρ : ρ ≤ μ)
    {N L s Adepth ε τ κ B S : ℝ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hsL : s ≤ L) (hS : 0 ≤ S) (hκ : 1 ≤ κ) (hB : 0 < B)
    (f : ℝ → ℝ)
    (hf : ∀ a b, 0 ≤ a → a ≤ b → b ≤ s → f b - f a ≤ b - a)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (g : ℝ → Observation → ENNReal)
    (hg : ∀ r ∈ coarseDepthGrid s ε, Measurable (g r))
    (hlaw : ∀ r ∈ coarseDepthGrid s ε,
      μ.map (obs B (δ N r)) = (volume.prod Measure.count).withDensity (g r))
    (hmask : ∀ r ∈ coarseDepthGrid s ε, ∀ᵐ p ∂ρ,
      g r (obs B (δ N r) p) ≤ ENNReal.ofReal (N ^ (-f r + τ)))
    (data : ∀ u, u ∈ coarseDepthGrid Adepth ε → 0 < u →
      NativeAngularSample μ N L B (δ N u))
    (hangular : ∀ u (hu : u ∈ coarseDepthGrid Adepth ε) (hu0 : 0 < u), ∀ᵐ p ∂ρ,
      (data u hu hu0).jointDensity (obs B (δ N L) p, nativeAngularBin (δ N u) p) ≤
        ENNReal.ofReal (N ^ (-S * u + 2 * τ)) *
          (data u hu hu0).terminalDensity (obs B (δ N L) p))
    (hnative : ∀ᵐ p ∂ρ, p.2 ∈ Icc (0 : ℝ) 1 ∧ ‖y p.1 p.2‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ κ * B ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ κ * B ^ 2 ∧
      B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)|)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (e c u : EuclideanSpace ℝ (Fin 2)) (t₀ Z : ℝ)
    {K q : ℝ} (hK : 0 < K) (hq : 0 < q)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (hframe : ∀ᵐ p ∂ρ, ‖Matrix.toEuclideanLin Q⁻¹ (y p.1 p.2 - c - p.2 • u)‖ ≤ K)
    (n : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (β : ℝ) {K₀ g₀ : ℝ} (hK₀ : 1 ≤ K₀) (hg₀ : 0 ≤ g₀) (hg₀A : g₀ ≤ N ^ (-Adepth))
    (hnormal : ∀ᵐ p ∂ρ, |inner ℝ n (v p.1) - β| ≤ K₀ * g₀)
    (r θ : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (hθε : ε ≤ θ) (hθA : θ ≤ Adepth)
    (j k : ℤ) (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U) :
    ρ {p | packetProjection e t₀ Z q p ∈ U ∧
      ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j ∧
      ⌊inner ℝ e (v p.1) / N ^ (-θ)⌋ = k} ≤
      ENNReal.ofReal (N ^ (-S * θ + 2 * τ + S * ε)) *
        ENNReal.ofReal ((8 * K₀ + 2) ^ 2) * ENNReal.ofReal (N ^ (-f r + τ + ε)) *
        ENNReal.ofReal (64 * κ ^ 2) * ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U := by
  obtain ⟨r₀, hr₀, hr₀0, hr₀r, _, hwidth, hprofile⟩ :=
    coarseDepthGrid_power_bounds hN hε hr hrs f hf
  obtain ⟨u₀, hu₀, hu₀θ, hgap⟩ := exists_coarseDepthGrid hε (hε.le.trans hθε) hθA
  have hu₀0 : 0 < u₀ := by linarith
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hw : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have hvw : 0 < N ^ (-θ) := Real.rpow_pos_of_pos hN0 _
  have ha : 0 < δ N r₀ := by unfold δ; positivity
  have ha1 : δ N r₀ ≤ 1 := nativeWidth_le_one hN hr₀0
  have hvwidth : N ^ (-θ) ≤ δ N u₀ :=
    (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hu₀θ)).trans
      (Submission.Obl.k4_profile_density_bounds.width_bounds hN0 u₀).1
  have hnormalWidth : g₀ ≤ N ^ (-θ) := hg₀A.trans
    (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hθA))
  have hgain : N ^ (-S * u₀ + 2 * τ) ≤ N ^ (-S * θ + 2 * τ + S * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith [mul_le_mul_of_nonneg_left hgap.le hS]
  let E : Set Incidence := {p | packetProjection e t₀ Z q p ∈ U ∧
    ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j ∧
    ⌊inner ℝ e (v p.1) / N ^ (-θ)⌋ = k}
  have hE : MeasurableSet E := by
    apply (hU.preimage (measurable_packetProjection e t₀ Z q)).inter
    apply MeasurableSet.inter
    · exact measurableSet_eq_fun
        ((P.continuous_eval.measurable.comp
          (show Measurable (fun p : Incidence => x p.1 p.2) by unfold x; fun_prop)).div_const _).floor
        measurable_const
    · exact measurableSet_eq_fun (by unfold v; fun_prop) measurable_const
  let σ : Measure Incidence := ρ.restrict E
  have hσρ : σ ≤ ρ := Measure.restrict_le_self
  have hnat : ∀ᵐ p ∂σ, p.2 ∈ Icc (0 : ℝ) 1 ∧ ‖y p.1 p.2‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) P - N ^ (-r) * (j : ℝ)| ≤ κ * δ N r₀ ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ κ * B ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ κ * B ^ 2 / δ N r₀ ∧
      B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ∧
      g r₀ (obs B (δ N r₀) p) ≤ ENNReal.ofReal (N ^ (-f r₀ + τ)) := by
    filter_upwards [ae_mono hσρ hnative, ae_mono hσρ (hmask r₀ hr₀),
      ae_restrict_mem hE] with p hp hm he
    obtain ⟨ht, hy, hd, hdd, hfl⟩ := hp
    refine ⟨ht, hy, ?_, hd, ?_, hfl, hm⟩
    · have hb := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hw
        (MvPolynomial.eval (x p.1 p.2) P)
      rw [he.2.1] at hb
      exact hb.trans (hwidth.trans (le_mul_of_one_le_left ha.le hκ))
    · apply (le_div_iff₀ ha).2
      calc
        _ ≤ (κ * B ^ 2) * δ N r₀ := mul_le_mul_of_nonneg_right hdd ha.le
        _ ≤ (κ * B ^ 2) * 1 := mul_le_mul_of_nonneg_left ha1 (by positivity)
        _ = _ := mul_one _
  have hcap := native_signal_band_projected_angular_cap μ σ (hσρ.trans hρ) hN
    (hr₀r.trans (hrs.trans hsL)) hB hκ (data u₀ hu₀ hu₀0) P hP (N ^ (-r) * (j : ℝ))
    (g r₀) (hg r₀ hr₀) (hlaw r₀ hr₀) (ENNReal.ofReal (N ^ (-f r₀ + τ)))
    (ENNReal.ofReal (N ^ (-S * u₀ + 2 * τ))) hnat
    (ae_mono hσρ (hangular u₀ hu₀ hu₀0)) Q hQ e c u t₀ Z hK hq hfull U hU
    (ae_mono hσρ hframe) (by
      filter_upwards [ae_restrict_mem hE] with p hp
      exact hp.1) n he hn hen β hK₀ hg₀ hnormalWidth hvw hvwidth k (by
      filter_upwards [ae_mono hσρ hnormal, ae_restrict_mem hE] with p hp hm
      exact ⟨hp, hm.2.2⟩)
  rw [show σ univ = ρ E from Measure.restrict_apply_univ E] at hcap
  exact hcap.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul'
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hgain) le_rfl)
      (ENNReal.ofReal_le_ofReal hprofile)) le_rfl) le_rfl) le_rfl)

/-- Below the first positive angular grid point, the pure cap already gives
the desired angular estimate with the same interpolation loss. -/
theorem shallow_angular_grid_cap {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (E V : Set Ω) {M : ENNReal} (hcap : ρ E ≤ M)
    {N S ε θ τ K₀ : ℝ} (hN : 1 ≤ N) (hS : 0 ≤ S) (hτ : 0 ≤ τ)
    (hθε : θ ≤ ε) (hK₀ : 1 ≤ K₀) :
    ρ (E ∩ V) ≤ ENNReal.ofReal (N ^ (-S * θ + 2 * τ + S * ε)) *
      ENNReal.ofReal ((8 * K₀ + 2) ^ 2) * M := by
  have hgain : 1 ≤ N ^ (-S * θ + 2 * τ + S * ε) :=
    Real.one_le_rpow hN (by nlinarith [mul_nonneg hS (sub_nonneg.mpr hθε)])
  have hcard : (1 : ℝ) ≤ (8 * K₀ + 2) ^ 2 := by nlinarith
  have hone : (1 : ENNReal) ≤ ENNReal.ofReal (N ^ (-S * θ + 2 * τ + S * ε)) *
      ENNReal.ofReal ((8 * K₀ + 2) ^ 2) := by
    simpa only [ENNReal.ofReal_one, one_mul] using
      mul_le_mul' (ENNReal.ofReal_le_ofReal hgain) (ENNReal.ofReal_le_ofReal hcard)
  exact (measure_mono inter_subset_left).trans (hcap.trans (by simpa using mul_le_mul' hone (le_refl M)))

/-- Continuous projected angular caps at all positive depths, including the
shallow range where the pure cap absorbs the angular interpolation loss. -/
theorem native_grid_projected_angular_cap
    (μ ρ : Measure Incidence) (hρ : ρ ≤ μ)
    {N L s Adepth ε τ κ B S : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hτ : 0 ≤ τ)
    (hsL : s ≤ L) (hS : 0 ≤ S) (hκ : 1 ≤ κ) (hB : 0 < B)
    (f : ℝ → ℝ)
    (hf : ∀ a b, 0 ≤ a → a ≤ b → b ≤ s → f b - f a ≤ b - a)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (g : ℝ → Observation → ENNReal)
    (hg : ∀ r ∈ coarseDepthGrid s ε, Measurable (g r))
    (hlaw : ∀ r ∈ coarseDepthGrid s ε,
      μ.map (obs B (δ N r)) = (volume.prod Measure.count).withDensity (g r))
    (hmask : ∀ r ∈ coarseDepthGrid s ε, ∀ᵐ p ∂ρ,
      g r (obs B (δ N r) p) ≤ ENNReal.ofReal (N ^ (-f r + τ)))
    (data : ∀ u, u ∈ coarseDepthGrid Adepth ε → 0 < u →
      NativeAngularSample μ N L B (δ N u))
    (hangular : ∀ u (hu : u ∈ coarseDepthGrid Adepth ε) (hu0 : 0 < u), ∀ᵐ p ∂ρ,
      (data u hu hu0).jointDensity (obs B (δ N L) p, nativeAngularBin (δ N u) p) ≤
        ENNReal.ofReal (N ^ (-S * u + 2 * τ)) *
          (data u hu hu0).terminalDensity (obs B (δ N L) p))
    (hnative : ∀ᵐ p ∂ρ, p.2 ∈ Icc (0 : ℝ) 1 ∧ ‖y p.1 p.2‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ κ * B ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ κ * B ^ 2 ∧
      B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)|)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (e c u : EuclideanSpace ℝ (Fin 2)) (t₀ Z : ℝ)
    {K q : ℝ} (hK : 0 < K) (hq : 0 < q)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (hframe : ∀ᵐ p ∂ρ, ‖Matrix.toEuclideanLin Q⁻¹ (y p.1 p.2 - c - p.2 • u)‖ ≤ K)
    (n : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (β : ℝ) {K₀ g₀ : ℝ} (hK₀ : 1 ≤ K₀) (hg₀ : 0 ≤ g₀) (hg₀A : g₀ ≤ N ^ (-Adepth))
    (hnormal : ∀ᵐ p ∂ρ, |inner ℝ n (v p.1) - β| ≤ K₀ * g₀)
    (r θ : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (_hθ0 : 0 < θ) (hθA : θ ≤ Adepth)
    (j k : ℤ) (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U) :
    ρ {p | packetProjection e t₀ Z q p ∈ U ∧
      ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j ∧
      ⌊inner ℝ e (v p.1) / N ^ (-θ)⌋ = k} ≤
      ENNReal.ofReal (N ^ (-S * θ + 2 * τ + S * ε)) *
        ENNReal.ofReal ((8 * K₀ + 2) ^ 2) * ENNReal.ofReal (N ^ (-f r + τ + ε)) *
        ENNReal.ofReal (64 * κ ^ 2) * ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U := by
  by_cases hθε : ε ≤ θ
  · exact native_grid_projected_angular_cap_of_large_depth μ ρ hρ hN hε hsL hS hκ hB
      f hf P hP g hg hlaw hmask data hangular hnative Q hQ e c u t₀ Z hK hq hfull
      hframe n he hn hen β hK₀ hg₀ hg₀A hnormal r θ hr hrs hθε hθA j k U hU
  · have hpure := native_grid_projected_cap μ ρ hρ hN hε hκ hB f hf P hP g hg hlaw
      hmask hnative Q hQ e c u t₀ Z hK hq hfull hframe r hr hrs j U hU
    have h := shallow_angular_grid_cap ρ
      {p | packetProjection e t₀ Z q p ∈ U ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j}
      {p | ⌊inner ℝ e (v p.1) / N ^ (-θ)⌋ = k}
      hpure hN hS hτ (le_of_not_ge hθε) hK₀
    have heq : {p : Incidence | packetProjection e t₀ Z q p ∈ U ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j} ∩
      {p | ⌊inner ℝ e (v p.1) / N ^ (-θ)⌋ = k} =
      {p | packetProjection e t₀ Z q p ∈ U ∧
        ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j ∧
        ⌊inner ℝ e (v p.1) / N ^ (-θ)⌋ = k} := by
      ext p
      exact and_assoc
    rw [heq] at h
    simpa only [mul_assoc] using h

end Submission.Obl.k4_uncapped_native_capping.UWE
