import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpAngular
set_option autoImplicit false

/-! The density cap of the calibrated remainder: the world-aggregated intermediate upper
comparison (new pure density at depth `s` against the original density at depth `r + s`),
and the resulting inequality `f''(L'') - f''(s) ≤ d (L'' - s)` from the terminal calibration
and the new typical pure densities. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion (x y v δ obs Data Atlas chart Valid)
open Submission.Obl.k4_native_calibrated_homogeneous_remainder (RemainderGeometry)

section Intermediate

variable {p q : Data} {r h w : ℝ} (g : RemainderGeometry p q r h w)

/-- The pulled-back selection of a remainder world lies in its parent event. -/
theorem geometry_pullback_subset (k : ℕ) (b : Fin (q.W k)) :
    incEquiv (g.θ k b) ((2 : ℝ) ^ (g.parent k).T)
        (((g.parent k).j (g.worlds k b) : ℝ) / (2 : ℝ) ^ (g.parent k).T)
        (by positivity) ⁻¹' q.E k b ⊆ (g.parent k).F (g.worlds k b) := by
  intro z hz
  have h1 := g.selected_pullback k b _ hz
  rw [incEquiv_apply] at h1
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  have ht : ((g.parent k).j (g.worlds k b) : ℝ) / (2 : ℝ) ^ (g.parent k).T +
      (z.2 - ((g.parent k).j (g.worlds k b) : ℝ) / (2 : ℝ) ^ (g.parent k).T) *
        (2 : ℝ) ^ (g.parent k).T / (2 : ℝ) ^ (g.parent k).T = z.2 := by
    field_simp; ring
  rw [ht] at h1
  exact h1

theorem weight_factor {ωγ Z : ℝ} (T : ℕ) (hω : 0 ≤ ωγ) (hZ : 0 < Z) {m : ℝ≥0∞}
    (hm0 : m ≠ 0) (hmt : m ≠ ⊤) :
    ENNReal.ofReal (ωγ / (2 : ℝ) ^ T * m.toReal / Z) * (ENNReal.ofReal ((2 : ℝ) ^ T) / m) =
      ENNReal.ofReal ωγ * ENNReal.ofReal Z⁻¹ := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hm' : ENNReal.ofReal m.toReal = m := ENNReal.ofReal_toReal hmt
  have e1 : ωγ / (2 : ℝ) ^ T * m.toReal / Z = (ωγ * Z⁻¹) * m.toReal * ((2 : ℝ) ^ T)⁻¹ := by
    field_simp
  rw [e1, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hω, hm', div_eq_mul_inv]
  have h2' : ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ENNReal.ofReal ((2 : ℝ) ^ T) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h2.ne', ENNReal.ofReal_one]
  calc ENNReal.ofReal ωγ * ENNReal.ofReal Z⁻¹ * m * ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
        (ENNReal.ofReal ((2 : ℝ) ^ T) * m⁻¹)
      = ENNReal.ofReal ωγ * ENNReal.ofReal Z⁻¹ * (m * m⁻¹) *
          (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ENNReal.ofReal ((2 : ℝ) ^ T)) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hm0 hmt, h2', mul_one, mul_one]

/-- **Aggregated intermediate upper comparison at one sample.** -/
theorem geometry_pure_upper_sample (hp : Valid p) (hr : 0 ≤ r) (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s)
    (hsL : s ≤ q.L) (hqE : ∀ b, MeasurableSet (q.E k b))
    (G : Fin (q.W k) → EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b) ∧ Measure.map (obs (q.B k b) (δ (q.N k) s))
      (((q.ν k b).prod volume).restrict (q.E k b)) = obsRef.withDensity (G b))
    (X : ℝ≥0∞) :
    (∑ b, ENNReal.ofReal (q.ω k b) * (((q.ν k b).prod volume).restrict (q.E k b))
        {z | ENNReal.ofReal |((g.parent k).Q (g.worlds k b)).det| /
            p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b)) *
              (3 * X) < G b (obs (q.B k b) (δ (q.N k) s) z)}) ≤
      12 * ENNReal.ofReal (g.Z k)⁻¹ * ∑ γ, ENNReal.ofReal (p.ω (g.φ k) γ) *
        (((p.ν (g.φ k) γ).prod volume).restrict (p.E (g.φ k) γ))
          {z | X < p.g (g.φ k) γ (r + s) (obs (p.B (g.φ k) γ) (δ (p.N (g.φ k)) (r + s)) z)} := by
  classical
  obtain ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hmodel, hgl, hGl, hprof, htyp, hdc, hcap⟩ := hp
  obtain ⟨M₀, D₀, hmodel⟩ := hmodel
  have hworld : ∀ γ, IsProbabilityMeasure (p.ν (g.φ k) γ) ∧ MeasurableSet (p.E (g.φ k) γ) := by
    intro γ
    obtain ⟨hpr, -, -, -, -, -, -, hE, -⟩ := (hmodel (g.φ k)).2.2.2.1 γ
    exact ⟨hpr, hE⟩
  have : ∀ γ, IsFiniteMeasure (p.ν (g.φ k) γ) := fun γ => by
    have := (hworld γ).1; infer_instance
  have hchart := fun c => chart_parts ((g.parent_valid k).2.2 c)
  have hrs : r + s ≤ p.L := by rw [g.length] at hsL; linarith
  have hr0 : 0 ≤ r + s := by linarith
  have hNk : q.N k = p.N (g.φ k) := g.same_base k
  -- the old bad sets
  set Y : Fin (p.W (g.φ k)) → Set Point := fun γ =>
    {z | X < p.g (g.φ k) γ (r + s) (obs (p.B (g.φ k) γ) (δ (p.N (g.φ k)) (r + s)) z)}
  have hY : ∀ γ, MeasurableSet (Y γ) := fun γ =>
    measurableSet_lt measurable_const ((hgl (g.φ k) γ (r + s) hr0 hrs).1.comp (measurable_obs _ _))
  -- one chart
  have hone : ∀ b, ENNReal.ofReal (q.ω k b) * (((q.ν k b).prod volume).restrict (q.E k b))
      {z | ENNReal.ofReal |((g.parent k).Q (g.worlds k b)).det| /
          p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b)) *
            (3 * X) < G b (obs (q.B k b) (δ (q.N k) s) z)} ≤
      6 * ENNReal.ofReal (g.Z k)⁻¹ * (ENNReal.ofReal (p.ω (g.φ k) ((g.parent k).γ (g.worlds k b))) *
        ((p.ν (g.φ k) ((g.parent k).γ (g.worlds k b))).prod volume)
          ((g.parent k).F (g.worlds k b) ∩ Y ((g.parent k).γ (g.worlds k b)))) := by
    intro b
    set c := g.worlds k b
    set γ := (g.parent k).γ c
    have hD : (0 : ℝ) < (2 : ℝ) ^ (g.parent k).T := by positivity
    have hνA : p.ν (g.φ k) γ ((g.parent k).A c) ≠ 0 := (g.prior_pos k b).ne'
    have hsub : incEquiv (g.θ k b) ((2 : ℝ) ^ (g.parent k).T)
        (((g.parent k).j c : ℝ) / (2 : ℝ) ^ (g.parent k).T) hD ⁻¹' q.E k b ⊆ p.E (g.φ k) γ :=
      fun z hz => ((hchart c).2.2.2.2 z (geometry_pullback_subset g k b hz)).1
    have hGlaw := (hG b).2
    rw [g.conditioned_prior k b, g.derivative_unit k b, hNk] at hGlaw
    have hup := chart_pure_upper (p.ν (g.φ k) γ) ((g.parent k).A c) (g.θ k b) hD
      (hchart c).1 hνA (g.planar_map k b) (g.hidden_map k b) (hqE b) hsub (p.B (g.φ k) γ)
      (p.N (g.φ k)) r s (hgl (g.φ k) γ (r + s) hr0 hrs).2 (hG b).1 hGlaw X
    rw [← g.conditioned_prior k b] at hup
    have hfun : obs (p.B (g.φ k) γ / δ (p.N (g.φ k)) r) (δ (p.N (g.φ k)) s) =
        obs (q.B k b) (δ (q.N k) s) := by rw [g.derivative_unit k b, hNk]
    rw [hfun] at hup
    have hS : ((p.ν (g.φ k) γ).prod volume).restrict
        (incEquiv (g.θ k b) ((2 : ℝ) ^ (g.parent k).T)
          (((g.parent k).j c : ℝ) / (2 : ℝ) ^ (g.parent k).T) hD ⁻¹' q.E k b) (Y γ) ≤
        ((p.ν (g.φ k) γ).prod volume) ((g.parent k).F c ∩ Y γ) := by
      rw [Measure.restrict_apply (hY γ), Set.inter_comm]
      exact measure_mono (Set.inter_subset_inter_left _ (geometry_pullback_subset g k b))
    calc ENNReal.ofReal (q.ω k b) * _ ≤ ENNReal.ofReal (q.ω k b) *
          (ENNReal.ofReal ((2 : ℝ) ^ (g.parent k).T) / p.ν (g.φ k) γ ((g.parent k).A c) *
            (6 * ((p.ν (g.φ k) γ).prod volume).restrict
              (incEquiv (g.θ k b) ((2 : ℝ) ^ (g.parent k).T)
                (((g.parent k).j c : ℝ) / (2 : ℝ) ^ (g.parent k).T) hD ⁻¹' q.E k b) (Y γ))) := by
          gcongr
      _ = (ENNReal.ofReal (q.ω k b) *
            (ENNReal.ofReal ((2 : ℝ) ^ (g.parent k).T) / p.ν (g.φ k) γ ((g.parent k).A c))) *
            (6 * ((p.ν (g.φ k) γ).prod volume).restrict
              (incEquiv (g.θ k b) ((2 : ℝ) ^ (g.parent k).T)
                (((g.parent k).j c : ℝ) / (2 : ℝ) ^ (g.parent k).T) hD ⁻¹' q.E k b) (Y γ)) := by
          ring
      _ = (ENNReal.ofReal (p.ω (g.φ k) γ) * ENNReal.ofReal (g.Z k)⁻¹) *
            (6 * ((p.ν (g.φ k) γ).prod volume).restrict
              (incEquiv (g.θ k b) ((2 : ℝ) ^ (g.parent k).T)
                (((g.parent k).j c : ℝ) / (2 : ℝ) ^ (g.parent k).T) hD ⁻¹' q.E k b) (Y γ)) := by
          rw [g.world_weights k b, weight_factor _ ((hmodel (g.φ k)).2.1 γ) (g.normalizer_pos k)
            hνA (measure_ne_top _ _)]
      _ ≤ (ENNReal.ofReal (p.ω (g.φ k) γ) * ENNReal.ofReal (g.Z k)⁻¹) *
            (6 * ((p.ν (g.φ k) γ).prod volume) ((g.parent k).F c ∩ Y γ)) := by
          gcongr
      _ = _ := by ring
  -- sum over charts, grouped by world
  calc _ ≤ ∑ b, 6 * ENNReal.ofReal (g.Z k)⁻¹ *
        (ENNReal.ofReal (p.ω (g.φ k) ((g.parent k).γ (g.worlds k b))) *
          ((p.ν (g.φ k) ((g.parent k).γ (g.worlds k b))).prod volume)
            ((g.parent k).F (g.worlds k b) ∩ Y ((g.parent k).γ (g.worlds k b)))) :=
        Finset.sum_le_sum fun b _ => hone b
    _ = 6 * ENNReal.ofReal (g.Z k)⁻¹ * ∑ c, ENNReal.ofReal (p.ω (g.φ k) ((g.parent k).γ c)) *
          ((p.ν (g.φ k) ((g.parent k).γ c)).prod volume)
            ((g.parent k).F c ∩ Y ((g.parent k).γ c)) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fintype.sum_equiv (g.worlds k) _ _ fun b => rfl
    _ = 6 * ENNReal.ofReal (g.Z k)⁻¹ * ∑ γ, ENNReal.ofReal (p.ω (g.φ k) γ) *
          ∑ c ∈ Finset.univ.filter (fun c => (g.parent k).γ c = γ),
            ((p.ν (g.φ k) γ).prod volume) ((g.parent k).F c ∩ Y γ) := by
        congr 1
        rw [← Finset.sum_fiberwise Finset.univ (g.parent k).γ]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c hc => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        rw [hc]
    _ ≤ 6 * ENNReal.ofReal (g.Z k)⁻¹ * ∑ γ, ENNReal.ofReal (p.ω (g.φ k) γ) *
          (2 * ((p.ν (g.φ k) γ).prod volume) (p.E (g.φ k) γ ∩ Y γ)) := by
        gcongr with γ
        exact (atlasSystem (g.parent k)).sum_world_event_le ((p.ν (g.φ k) γ).prod volume)
          (p.E (g.φ k)) γ (fun c => (hchart c).2.2.2.1) (g.parent_valid k).2.1
          (fun c z hz => (hchart c).2.2.2.2 z hz) (Y γ) (hY γ) (((hworld γ).2).inter (hY γ))
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Measure.restrict_apply (hY γ), Set.inter_comm]
        ring

/-- A weighted family whose two exceptional masses together are below its total mass has a
point outside both exceptional sets in some world. -/
theorem exists_good_point {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (wt : ι → ℝ≥0∞) (μ : ι → Measure Ω) (B₁ B₂ : ι → Set Ω) (m x₁ x₂ : ℝ≥0∞)
    (hmass : m ≤ ∑ i, wt i * μ i Set.univ)
    (h₁ : ∑ i, wt i * μ i (B₁ i) ≤ x₁) (h₂ : ∑ i, wt i * μ i (B₂ i) ≤ x₂)
    (hlt : x₁ + x₂ < m) : ∃ i z, z ∉ B₁ i ∧ z ∉ B₂ i := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hcov : ∀ i, μ i Set.univ ≤ μ i (B₁ i) + μ i (B₂ i) := by
    intro i
    calc μ i Set.univ ≤ μ i (B₁ i ∪ B₂ i) := measure_mono fun z _ => by
          by_cases hz : z ∈ B₁ i
          · exact Or.inl hz
          · exact Or.inr (hcon i z hz)
      _ ≤ _ := measure_union_le _ _
  have : m ≤ x₁ + x₂ := by
    calc m ≤ ∑ i, wt i * μ i Set.univ := hmass
      _ ≤ ∑ i, (wt i * μ i (B₁ i) + wt i * μ i (B₂ i)) := by
          gcongr with i
          rw [← mul_add]; gcongr; exact hcov i
      _ = ∑ i, wt i * μ i (B₁ i) + ∑ i, wt i * μ i (B₂ i) := Finset.sum_add_distrib
      _ ≤ x₁ + x₂ := add_le_add h₁ h₂
  exact (not_lt_of_ge this) hlt

/-- **The density cap of the remainder.** The new pure profile inherits the original cap
`d`: `f''(L'') - f''(s) ≤ f(L) - f(r + s) ≤ d (L'' - s)`, from the new typical pure densities,
the aggregated intermediate upper comparison and the terminal calibration. -/
theorem geometry_density_cap (hp : Valid p) (hr : 0 ≤ r)
    (hqE : ∀ k b, MeasurableSet (q.E k b))
    (hqK : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, q.K k ≤ q.N k ^ ε)
    (hqK1 : ∀ k, 1 ≤ q.K k)
    (hqmass : ∀ k, ENNReal.ofReal (q.K k)⁻¹ ≤
      ∑ b, ENNReal.ofReal (q.ω k b) * (((q.ν k b).prod volume).restrict (q.E k b)) Set.univ)
    (hqg : ∀ k b s, 0 ≤ s → s ≤ q.L → Measurable (q.g k b s) ∧
      Measure.map (obs (q.B k b) (δ (q.N k) s)) (((q.ν k b).prod volume).restrict (q.E k b)) =
        obsRef.withDensity (q.g k b s))
    (hqtyp : ∀ s τ : ℝ, 0 ≤ s → s ≤ q.L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop,
      (∑ b, ENNReal.ofReal (q.ω k b) * (((q.ν k b).prod volume).restrict (q.E k b))
        {z | q.g k b s (obs (q.B k b) (δ (q.N k) s) z) < ENNReal.ofReal (q.N k ^ (-q.f s - τ)) ∨
          ENNReal.ofReal (q.N k ^ (-q.f s + τ)) < q.g k b s (obs (q.B k b) (δ (q.N k) s) z)}) ≤
        ENNReal.ofReal (q.N k ^ (-c)))
    (hcal : ∀ k b, p.N (g.φ k) ^ (-p.f p.L) * |((g.parent k).Q (g.worlds k b)).det| ≤
      g.κ k * (p.ν (g.φ k) ((g.parent k).γ (g.worlds k b))
        ((g.parent k).A (g.worlds k b))).toReal * q.N k ^ (-q.f q.L)) :
    ∀ s : ℝ, 0 ≤ s → s ≤ q.L → q.f q.L - q.f s ≤ q.d * (q.L - s) := by
  intro s hs0 hsL
  have hp' := hp
  obtain ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hmodel, hgl, hGl, hprof, htyp, hdc, hcap⟩ := hp'
  have hrs : r + s ≤ p.L := by rw [g.length] at hsL; linarith
  have hr0 : 0 ≤ r + s := by linarith
  -- it suffices to prove the comparison with the original profile up to every tolerance
  suffices H : ∀ τ : ℝ, 0 < τ → q.f q.L - q.f s ≤ p.f p.L - p.f (r + s) + 4 * τ by
    have h1 : q.f q.L - q.f s ≤ p.f p.L - p.f (r + s) := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have := H (ε / 8) (by positivity)
      linarith
    have h2 := hdc (r + s) hr0 hrs
    rw [g.density_cap, g.length]
    rw [g.length] at h1
    calc q.f (p.L - r) - q.f s ≤ p.f p.L - p.f (r + s) := h1
      _ ≤ p.d * (p.L - (r + s)) := h2
      _ = p.d * (p.L - r - s) := by ring
  intro τ hτ
  obtain ⟨c₁, hc₁, hev₁⟩ := hqtyp s τ hs0 hsL hτ
  obtain ⟨c₂, hc₂, hev₂⟩ := htyp (r + s) τ hr0 hrs hτ
  have hφ : Filter.Tendsto g.φ Filter.atTop Filter.atTop := g.increasing.tendsto_atTop
  have hev₂' := hφ.eventually hev₂
  set c₃ := min c₁ c₂ / 4 with hc₃
  have hc₃pos : 0 < c₃ := by positivity
  have hevK := hqK c₃ hc₃pos
  have herr : ∀ᶠ k in Filter.atTop, g.error k < min c₃ τ :=
    (tendsto_order.1 g.error_limit).2 _ (lt_min hc₃pos hτ)
  have hbig : ∀ᶠ k in Filter.atTop,
      max ((13 : ℝ) ^ (1 / c₃)) ((3 : ℝ) ^ (1 / τ)) ≤ p.N (g.φ k) :=
    (hNt.comp hφ).eventually_ge_atTop _
  obtain ⟨k, hk₁, hk₂, hkK, hke, hkN⟩ := (hev₁.and (hev₂'.and (hevK.and (herr.and hbig)))).exists
  obtain ⟨M₀, D₀, hmodel'⟩ := hmodel
  have hfinp : ∀ γ, IsFiniteMeasure (p.ν (g.φ k) γ) := fun γ => by
    have := ((hmodel' (g.φ k)).2.2.2.1 γ).1; infer_instance
  set Nk := p.N (g.φ k) with hNkdef
  have hqN : q.N k = Nk := g.same_base k
  have hN2 : 2 ≤ Nk := hN _
  have hN0 : 0 < Nk := by linarith
  have hN1 : 1 < Nk := by linarith
  have hκ1 : 1 ≤ g.κ k := g.slack_one k
  have hκ0 : 0 < g.κ k := by linarith
  have hκτ : g.κ k ≤ Nk ^ τ := (g.slack_bound k).trans
    (Real.rpow_le_rpow_of_exponent_le hN1.le ((lt_min_iff.1 hke).2.le))
  have hκc : g.κ k ≤ Nk ^ c₃ := (g.slack_bound k).trans
    (Real.rpow_le_rpow_of_exponent_le hN1.le ((lt_min_iff.1 hke).1.le))
  have h13 : (13 : ℝ) ≤ Nk ^ c₃ :=
    le_rpow_of_root_le (by norm_num) hc₃pos ((le_max_left _ _).trans hkN)
  have h3 : (3 : ℝ) ≤ Nk ^ τ :=
    le_rpow_of_root_le (by norm_num) hτ ((le_max_right _ _).trans hkN)
  have hZκ : (g.Z k)⁻¹ ≤ g.κ k :=
    (inv_le_comm₀ hκ0 (g.normalizer_pos k)).1 (g.normalizer_lower k)
  -- the two exceptional masses
  set X : ℝ≥0∞ := ENNReal.ofReal (Nk ^ (-p.f (r + s) + τ)) with hX
  have hcmp := geometry_pure_upper_sample g hp hr k s hs0 hsL (hqE k) (fun b => q.g k b s)
    (fun b => hqg k b s hs0 hsL) X
  have hold : (∑ γ, ENNReal.ofReal (p.ω (g.φ k) γ) *
      (((p.ν (g.φ k) γ).prod volume).restrict (p.E (g.φ k) γ))
        {z | X < p.g (g.φ k) γ (r + s) (obs (p.B (g.φ k) γ) (δ Nk (r + s)) z)}) ≤
      ENNReal.ofReal (Nk ^ (-c₂)) := by
    refine le_trans ?_ hk₂
    gcongr with γ
    exact fun hz => Or.inr hz
  have hB2 : (∑ b, ENNReal.ofReal (q.ω k b) * (((q.ν k b).prod volume).restrict (q.E k b))
      {z | ENNReal.ofReal |((g.parent k).Q (g.worlds k b)).det| /
          p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b)) *
            (3 * X) < q.g k b s (obs (q.B k b) (δ (q.N k) s) z)}) ≤
      ENNReal.ofReal (12 * g.κ k * Nk ^ (-c₂)) := by
    refine hcmp.trans ?_
    calc 12 * ENNReal.ofReal (g.Z k)⁻¹ * _ ≤ 12 * ENNReal.ofReal (g.κ k) *
          ENNReal.ofReal (Nk ^ (-c₂)) := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
          norm_num
  have hB1 := hk₁
  rw [hqN] at hB1
  -- a good point
  have hsmall : ENNReal.ofReal (Nk ^ (-c₁)) + ENNReal.ofReal (12 * g.κ k * Nk ^ (-c₂)) <
      ENNReal.ofReal (q.K k)⁻¹ := by
    have hK0 : 0 < q.K k := by linarith [hqK1 k]
    have hKc : q.K k ≤ Nk ^ c₃ := by rw [← hqN]; exact hkK
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
    have hc1 : Nk ^ (-c₁) ≤ Nk ^ (-(4 * c₃)) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le (by
        have : 4 * c₃ ≤ c₁ := by rw [hc₃]; linarith [min_le_left c₁ c₂]
        linarith)
    have hc2 : Nk ^ (-c₂) ≤ Nk ^ (-(4 * c₃)) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le (by
        have : 4 * c₃ ≤ c₂ := by rw [hc₃]; linarith [min_le_right c₁ c₂]
        linarith)
    have hP : 0 < Nk ^ c₃ := Real.rpow_pos_of_pos hN0 _
    have e4 : Nk ^ (-(4 * c₃)) = ((Nk ^ c₃) ^ 4)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_neg hN0.le]
      congr 1; push_cast; ring
    calc Nk ^ (-c₁) + 12 * g.κ k * Nk ^ (-c₂)
        ≤ ((Nk ^ c₃) ^ 4)⁻¹ + 12 * Nk ^ c₃ * ((Nk ^ c₃) ^ 4)⁻¹ := by
          rw [← e4]; gcongr
      _ < (Nk ^ c₃)⁻¹ := by
          set P := Nk ^ c₃
          have hP1 : 13 ≤ P := h13
          have hP0 : 0 < P := by linarith
          have hcube : 1 + 12 * P < P ^ 3 := by nlinarith [mul_le_mul hP1 hP1 (by norm_num) hP0.le]
          have e : ((P ^ 4)⁻¹ + 12 * P * (P ^ 4)⁻¹ : ℝ) = (1 + 12 * P) * (P ^ 4)⁻¹ := by ring
          rw [e]
          have hP4 : (0 : ℝ) < P ^ 4 := by positivity
          rw [← div_eq_mul_inv, div_lt_iff₀ hP4]
          calc 1 + 12 * P < P ^ 3 := hcube
            _ = P⁻¹ * P ^ 4 := by field_simp
      _ ≤ (q.K k)⁻¹ := (inv_le_inv₀ hP hK0).2 hKc
  obtain ⟨b, z, hz1, hz2⟩ := exists_good_point (fun b => ENNReal.ofReal (q.ω k b))
    (fun b => ((q.ν k b).prod volume).restrict (q.E k b)) _ _ _ _ _ (hqmass k) hB1 hB2 hsmall
  simp only [Set.mem_ofPred_eq, not_or, not_lt] at hz1 hz2
  rw [hqN] at hz2
  -- the exponent inequality at the good point
  set J := |((g.parent k).Q (g.worlds k b)).det|
  set mA := (p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b))).toReal
  have hmA : 0 < mA := ENNReal.toReal_pos (g.prior_pos k b).ne' (measure_ne_top _ _)
  have hνA : p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b)) =
      ENNReal.ofReal mA := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hchain : ENNReal.ofReal (Nk ^ (-q.f s - τ)) ≤
      ENNReal.ofReal (J / mA * (3 * Nk ^ (-p.f (r + s) + τ))) := by
    refine hz1.1.trans (hz2.trans ?_)
    rw [hνA, hX, ← ENNReal.ofReal_div_of_pos hmA, ← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  have hc := hcal k b
  rw [hqN] at hc
  have hJm : J / mA ≤ g.κ k * Nk ^ (p.f p.L - q.f q.L) := by
    rw [div_le_iff₀ hmA]
    have e : Nk ^ (p.f p.L - q.f q.L) = Nk ^ (-q.f q.L) / Nk ^ (-p.f p.L) := by
      rw [← Real.rpow_sub hN0]; congr 1; ring
    rw [e]
    have hpos : 0 < Nk ^ (-p.f p.L) := Real.rpow_pos_of_pos hN0 _
    rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith [hc]
  have hfinal : Nk ^ (-q.f s - τ) ≤ Nk ^ (p.f p.L - q.f q.L - p.f (r + s) + 3 * τ) := by
    calc Nk ^ (-q.f s - τ) ≤ J / mA * (3 * Nk ^ (-p.f (r + s) + τ)) := hreal
      _ ≤ g.κ k * Nk ^ (p.f p.L - q.f q.L) * (3 * Nk ^ (-p.f (r + s) + τ)) := by gcongr
      _ ≤ Nk ^ τ * Nk ^ (p.f p.L - q.f q.L) * (Nk ^ τ * Nk ^ (-p.f (r + s) + τ)) := by
          gcongr
      _ = Nk ^ (p.f p.L - q.f q.L - p.f (r + s) + 3 * τ) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
          congr 1; ring
  have := (Real.rpow_le_rpow_left_iff hN1).1 hfinal
  linarith

end Intermediate

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp
