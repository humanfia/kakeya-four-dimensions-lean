/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/NativeGridCap.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/NativeGridCap.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.DepthGrid
import Submission.Obl.k4_uncapped_native_capping.UWE.ProjectedNativeCap
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

theorem nativeWidth_le_one {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) : δ N r ≤ 1 := by
  have hdepth : 0 ≤ ⌊r * Real.log N / Real.log 2⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (mul_nonneg hr (Real.log_nonneg hN)) (by positivity))
  exact zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr hdepth)

/-- Exact projected coordinates of an original incidence in a time packet. -/
def packetProjection (e : EuclideanSpace ℝ (Fin 2)) (t₀ Z q : ℝ)
    (p : Incidence) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(p.2 - t₀) / q, (inner ℝ e (y p.1 p.2) - Z) / q]

theorem measurable_packetProjection (e : EuclideanSpace ℝ (Fin 2)) (t₀ Z q : ℝ) :
    Measurable (packetProjection e t₀ Z q) := by
  unfold packetProjection y x
  fun_prop

/-- A finite grid of original pure-density masks yields a continuous projected
cap at EVERY signal depth. The measure is an unchanged original submeasure;
the only interpolation loss is the explicit `N^ε`. -/
theorem native_grid_projected_cap
    (μ ρ : Measure Incidence) (hρ : ρ ≤ μ)
    {N s ε τ κ B : ℝ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hκ : 1 ≤ κ) (hB : 0 < B)
    (f : ℝ → ℝ)
    (hf : ∀ a b, 0 ≤ a → a ≤ b → b ≤ s → f b - f a ≤ b - a)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (g : ℝ → Observation → ENNReal)
    (hg : ∀ r ∈ coarseDepthGrid s ε, Measurable (g r))
    (hlaw : ∀ r ∈ coarseDepthGrid s ε,
      μ.map (obs B (δ N r)) = (volume.prod Measure.count).withDensity (g r))
    (hmask : ∀ r ∈ coarseDepthGrid s ε, ∀ᵐ p ∂ρ,
      g r (obs B (δ N r) p) ≤ ENNReal.ofReal (N ^ (-f r + τ)))
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
    (r : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (j : ℤ)
    (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U) :
    ρ {p | packetProjection e t₀ Z q p ∈ U ∧
      ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j} ≤
      ENNReal.ofReal (N ^ (-f r + τ + ε)) * ENNReal.ofReal (64 * κ ^ 2) *
        ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U := by
  obtain ⟨r₀, hr₀, hr₀0, hr₀r, _, hwidth, hprofile⟩ :=
    coarseDepthGrid_power_bounds hN hε hr hrs f hf
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hw : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have ha : 0 < δ N r₀ := by unfold δ; positivity
  have ha1 : δ N r₀ ≤ 1 := nativeWidth_le_one hN hr₀0
  let E : Set Incidence := {p | packetProjection e t₀ Z q p ∈ U ∧
    ⌊MvPolynomial.eval (x p.1 p.2) P / N ^ (-r)⌋ = j}
  have hE : MeasurableSet E := by
    exact (hU.preimage (measurable_packetProjection e t₀ Z q)).inter
      (measurableSet_eq_fun
        ((P.continuous_eval.measurable.comp
          (show Measurable (fun p : Incidence => x p.1 p.2) by unfold x; fun_prop)).div_const _).floor
        measurable_const)
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
      rw [he.2] at hb
      exact hb.trans (hwidth.trans (le_mul_of_one_le_left ha.le hκ))
    · apply (le_div_iff₀ ha).2
      calc
        _ ≤ (κ * B ^ 2) * δ N r₀ := mul_le_mul_of_nonneg_right hdd ha.le
        _ ≤ (κ * B ^ 2) * 1 := mul_le_mul_of_nonneg_left ha1 (by positivity)
        _ = _ := mul_one _
  have hcap := native_signal_band_projected_cap μ σ (hσρ.trans hρ) hκ hB ha P hP
    (N ^ (-r) * (j : ℝ)) (g r₀) (hg r₀ hr₀) (hlaw r₀ hr₀)
    (ENNReal.ofReal (N ^ (-f r₀ + τ))) hnat Q hQ e c u t₀ Z hK hq hfull U hU
    (ae_mono hσρ hframe) (by
      filter_upwards [ae_restrict_mem hE] with p hp
      exact hp.1)
  rw [show σ univ = ρ E from Measure.restrict_apply_univ E] at hcap
  exact hcap.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
    (ENNReal.ofReal_le_ofReal hprofile) le_rfl) le_rfl) le_rfl)

end Submission.Obl.k4_uncapped_native_capping.UWE
