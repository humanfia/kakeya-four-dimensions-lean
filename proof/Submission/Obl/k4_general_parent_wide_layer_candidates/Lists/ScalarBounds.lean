import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.CapTests

/-!
# Scalar cap bounds and ready frames from pooled submeasures

Adapted from accepted o248 (`k4_wide_velocity_lists_scalar_preparation`, files
`ScalarBounds.lean` and `ReadyFromBounds.lean`) to the general parent and its
native signal.
-/

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The two analytical cap requirements in `ScalarAdmissible`, with exact
fixed density and a positive angular interval independent of the loss. -/
structure ScalarBounds (p : Parent α) (k : ℕ) (r v m η : ℝ)
    (coeff : α → Fin 5 → ℝ) (law : Measure (α × ℝ)) : Prop where
  pure : ∀ (s : ℝ) (β : Fin 2 → ℤ) (j : ℤ), 0 ≤ s → s ≤ r + v →
    law {ω | scalarCell (coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
      ⌊scalarX (coeff ω.1) ω.2 / p.N k ^ (-s)⌋ = j} ≤
      ENNReal.ofReal (p.N k ^ η * (p.N k ^ (-m)) ^ 2 * p.N k ^ (p.d * r) *
        (p.N k ^ (-s)) ^ p.d)
  angular : ∀ (θ : ℝ) (β : Fin 2 → ℤ) (j b : ℤ), 0 < θ → θ ≤ m / 2 →
    law {ω | scalarCell (coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
      ⌊scalarX (coeff ω.1) ω.2 / p.N k ^ (-(r + v))⌋ = j ∧
      ⌊coeff ω.1 1 / p.N k ^ (-θ)⌋ = b} ≤
      ENNReal.ofReal (p.N k ^ η * (p.N k ^ (-m)) ^ 2 * p.N k ^ (p.d * r) *
        (p.N k ^ (-(r + v))) ^ p.d * p.N k ^ (-p.S * θ))

theorem ScalarBounds.mono {k : ℕ} {r v m η : ℝ}
    {coeff : α → Fin 5 → ℝ} {law law' : Measure (α × ℝ)}
    (h : ScalarBounds p k r v m η coeff law) (hle : law' ≤ law) :
    ScalarBounds p k r v m η coeff law' := by
  constructor
  · intro s β j hs hsv
    exact (hle _).trans (h.pure s β j hs hsv)
  · intro θ β j b hθ hθm
    exact (hle _).trans (h.angular θ β j b hθ hθm)

/-- Original pure and joint native caps supply all scalar cap tests uniformly in
incoming frames. At very shallow angular scales, the final loss pays for
the requested decay directly from the pure cap. -/
theorem Valid.eventually_scalar_bounds (h : p.Valid)
    {r v m : ℝ} (hr : 0 < r) (hv : 0 < v) (hm : 100 * (r + v) < m)
    (hℓm : p.ℓ * r ≤ m) (hrU : r ≤ p.U) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ ε : ℝ, ∀ f : p.ListFrame k r v m ε,
      ScalarBounds p k r v m η f.coeff f.law := by
  have hm0 : 0 < m := by linarith
  have hrv : 0 ≤ r + v := by linarith
  let angFloor := min (η / (2 * p.S)) (m / 4)
  have hangFloor : 0 < angFloor := lt_min (by exact div_pos hη (by linarith [h.palette_pos]))
    (by positivity)
  have hangFloorm : angFloor ≤ m / 2 := (min_le_right _ _).trans (by linarith)
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [h.scale k]
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 4
    (show (0 : ℝ) < η / 2 by positivity) (show (0 : ℝ) ≤ 42000 by norm_num)
  filter_upwards [h.eventually_parent_geometry hr hrU, h.eventually_frame_mesh hr hv hm hℓm,
    h.eventually_fine_caps (show 0 < 100 * m by positivity) hrv hangFloor hangFloorm, hcost]
    with k a mesh caps hcost
  intro ε f
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hK0 : 0 ≤ p.K k := by linarith
  have hcost : 42000 * p.K k ^ 4 ≤ p.N k ^ (η / 2) := by
    simpa only [Real.rpow_zero, mul_one] using hcost.le
  have hsmallCost : 8400 * p.K k ^ 3 ≤ p.N k ^ (η / 2) := by
    have hcompare : 8400 * p.K k ^ 3 ≤ 42000 * p.K k ^ 4 := by
      nlinarith [pow_nonneg hK0 4, pow_nonneg hK0 3,
        mul_le_mul_of_nonneg_left hK (pow_nonneg hK0 3)]
    exact hcompare.trans hcost
  have hηhalf : p.N k ^ (η / 2) ≤ p.N k ^ η :=
    Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
  have hfmesh := mesh ε f a
  constructor
  · intro s β j hs hsv
    apply (f.pure_cell_cap h a hfmesh caps s hs hsv β j).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      8400 * p.K k ^ 3 * p.N k ^ (p.d * r) *
          (p.N k ^ (-m)) ^ 2 * (p.N k ^ (-s)) ^ p.d ≤
          p.N k ^ η * p.N k ^ (p.d * r) *
            (p.N k ^ (-m)) ^ 2 * (p.N k ^ (-s)) ^ p.d := by
        gcongr
        exact hsmallCost.trans hηhalf
      _ = _ := by ring
  · intro θ β j b hθ hθm
    by_cases hθangFloor : angFloor ≤ θ
    · have hc := f.translated_velocity_bin_cap h a hfmesh caps (r + v) θ
        hrv le_rfl hθangFloor hθm β j b
      apply hc.trans
      apply ENNReal.ofReal_le_ofReal
      calc
        42000 * p.K k ^ 4 * p.N k ^ (p.d * r) * (p.N k ^ (-m)) ^ 2 *
            (p.N k ^ (-(r + v))) ^ p.d * p.N k ^ (-p.S * θ) ≤
            p.N k ^ η * p.N k ^ (p.d * r) * (p.N k ^ (-m)) ^ 2 *
              (p.N k ^ (-(r + v))) ^ p.d * p.N k ^ (-p.S * θ) := by
          gcongr
          exact hcost.trans hηhalf
        _ = _ := by ring
    · have hθsmall : p.S * θ ≤ η / 2 := by
        have hθangFloor : θ ≤ angFloor := le_of_not_ge hθangFloor
        have hangFloorη : angFloor ≤ η / (2 * p.S) := min_le_left _ _
        have hh := (le_div_iff₀ (by linarith [h.palette_pos] : 0 < 2 * p.S)).mp
          (hθangFloor.trans hangFloorη)
        linarith
      have hcoeff : 8400 * p.K k ^ 3 ≤ p.N k ^ η * p.N k ^ (-p.S * θ) := by
        calc
          _ ≤ p.N k ^ (η / 2) := hsmallCost
          _ ≤ p.N k ^ (η + -p.S * θ) :=
            Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
          _ = _ := Real.rpow_add hN _ _
      have hmon : f.law {ω | scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
          ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-(r + v))⌋ = j ∧
          ⌊f.coeff ω.1 1 / p.N k ^ (-θ)⌋ = b} ≤
          f.law {ω | scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
            ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-(r + v))⌋ = j} :=
        measure_mono (fun ω hω => ⟨hω.1, hω.2.1⟩)
      apply hmon.trans
      apply (f.pure_cell_cap h a hfmesh caps (r + v) hrv le_rfl β j).trans
      apply ENNReal.ofReal_le_ofReal
      calc
        8400 * p.K k ^ 3 * p.N k ^ (p.d * r) * (p.N k ^ (-m)) ^ 2 *
            (p.N k ^ (-(r + v))) ^ p.d ≤
            (p.N k ^ η * p.N k ^ (-p.S * θ)) * p.N k ^ (p.d * r) *
              (p.N k ^ (-m)) ^ 2 * (p.N k ^ (-(r + v))) ^ p.d := by
          gcongr
        _ = _ := by ring

namespace ListFrame

variable {k : ℕ} {r v m ε η : ℝ} (f : p.ListFrame k r v m ε)

/-- A pooled submeasure with a terminal list completes Scalar readiness.
All fixed frames, coefficients, priors and original domination are retained. -/
theorem ready_of_submeasure (h : p.Valid) (hr : 0 < r) (hεη : ε ≤ η)
    (law : Measure (α × ℝ)) (hle : law ≤ f.law)
    (hcaps : ScalarBounds p k r v m η f.coeff law)
    (hmass : ENNReal.ofReal (p.N k ^ (-η)) ≤ law univ)
    (terminal : Finset ((Fin 2 → ℤ) × ℤ))
    (hcard : (terminal.card : ℝ) * (p.N k ^ (-m)) ^ 2 ≤
      p.N k ^ η * p.N k ^ (p.d * v))
    (hterminal : ∀ᵐ ω ∂law,
      (scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)),
        ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-r - v)⌋) ∈ terminal) :
    Nonempty (p.ReadyFrame k r v m (p.d * r + 1) p.S (m / 2) (max 1 (m / 10)) η) := by
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [h.scale k]
  have hpow := Real.rpow_le_rpow_of_exponent_le hN1 hεη
  have hdr : 0 ≤ p.d * r := mul_nonneg h.dimension_nonneg hr.le
  have hdom : law ≤ ENNReal.ofReal (p.N k ^ η) • f.prior.prod volume := by
    apply hle.trans
    apply f.law_domination.trans
    intro E
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl
  have htime : law (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((hle _).trans_eq f.time_support) bot_le
  have hfactor : (p.N k ^ (p.d * r))⁻¹ *
      (p.N k ^ (-(r + v))) ^ (-p.d) = p.N k ^ (p.d * v) := by
    rw [← Real.rpow_mul hN.le, ← Real.rpow_neg hN.le, ← Real.rpow_add hN]
    congr 1
    ring
  have hgood := ae_mono hle f.good_ae
  have hheight : p.N k ^ (m / 10) ≤ p.N k ^ max 1 (m / 10) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
  refine ⟨{
    parent := f.parent
    t₀ := f.t₀
    q := f.q
    z₀ := f.z₀
    zv := f.zv
    background := f.background
    prior := f.prior
    law := law
    coeff := f.coeff
    good := f.good
    good_measurable := f.good_measurable
    good_subset := f.good_subset
    good_ae := hgood
    admissible := ?_
    mass_lower := hmass
    q_pos := f.q_pos
    q_eq := f.q_eq
    time_eq := f.time_eq
    background_degree := f.background_degree
    background_bound := f.background_bound.trans hheight
    frame_bound := f.frame_bound.trans hheight
    scalarY_eq := f.scalarY_eq
    scalarX_eq := f.scalarX_eq
    original_domination := ?_
  }⟩
  · refine ⟨f.coeff_measurable, f.prior_probability, hdom, htime,
      (fun l i => (f.coeff_bound l i).trans hpow),
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith),
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith), hcaps.pure,
      ⟨terminal, ?_, ?_⟩, hcaps.angular⟩
    · rw [mul_assoc, hfactor]
      exact hcard
    · simpa only [neg_add, sub_eq_add_neg] using hterminal
  · have hf : Measurable (fun ω : α × ℝ => (ω.1, f.t₀ + f.q * ω.2)) := by fun_prop
    have hmap := Measure.map_mono hle hf
    intro E
    have horig := f.original_domination E
    simp only [Measure.smul_apply, smul_eq_mul] at horig ⊢
    exact (mul_le_mul' le_rfl (hmap E)).trans horig

end ListFrame

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
