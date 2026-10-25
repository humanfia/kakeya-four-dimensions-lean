import Submission.Obl.k4_coarsened_outer_horizon_composition.Crossings
import Submission.Obl.k4_coarsened_outer_horizon_composition.Pruning
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

/-!
# Upper bounds for full assigned priors

A label of a layer is *heavy* when its full assigned prior `ν (A b)` exceeds
`N ^ σ * N ^ (-f r) * |det Q b|`. Away from the exceptional (high density) part, the
selected mass of a chart is at most the density ceiling `N ^ (-f r + τ)` times the volume of
its observable support, `256 κ ^ 4 2 ^ (-T) |det Q b|` (o148's `reference_crossing`, o094's
`mass_le_of_density_le`). For a
heavy label this is at most `256 κ ^ 4 N ^ (τ - σ) 2 ^ (-T) ν (A b)`, and the assignments of
one layer cost at most `2 ^ T` in total (o115's assignment budget). Hence the heavy labels of
a layer carry weighted selected mass at most `2 X + 256 κ ^ 4 N ^ (τ - σ)`, where `X` bounds
the weighted exceptional mass. No floor is used.
-/

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- Within one world, a point lies in at most two selections of a layer: a finite set of
charts of one time generation with disjoint assignments in each dyadic time cell. -/
theorem layer_multiplicity_le_two {ι : Type*} (S : Finset ι) {W T : ℕ}
    (γ : ι → Fin W) (j : ι → ℕ) (hj : ∀ b ∈ S, j b < 2 ^ T)
    (A : ι → Set Line) (F : ι → Set Inc)
    (hdisj : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hsel : ∀ b ∈ S, ∀ p ∈ F b, p.1 ∈ A b ∧
      p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T) (((j b : ℝ) + 1) / (2 : ℝ) ^ T))
    (w : Fin W) (p : Inc) :
    (∑ b ∈ S.filter (fun b => γ b = w), (F b).indicator (1 : Inc → ℝ≥0∞) p) ≤ 2 := by
  classical
  set s := (S.filter (fun b => γ b = w)).filter (fun b => p ∈ F b) with hs
  have hsum : (∑ b ∈ S.filter (fun b => γ b = w), (F b).indicator (1 : Inc → ℝ≥0∞) p) =
      (s.card : ℝ≥0∞) := by
    rw [hs, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : p ∈ F b <;> simp [h]
  rw [hsum]
  have hpos : 0 < 2 ^ T := by positivity
  let jf : ι → Fin (2 ^ T) := fun b => ⟨j b % 2 ^ T, Nat.mod_lt _ hpos⟩
  have hmem : ∀ b ∈ s, b ∈ S ∧ γ b = w ∧ p ∈ F b := by
    intro b hb
    simp only [hs, Finset.mem_filter] at hb
    exact ⟨hb.1.1, hb.1.2, hb.2⟩
  have hcard : s.card ≤ 2 := by
    refine le_trans (Finset.card_le_card_of_injOn jf ?_ ?_)
      (card_dyadic_intervals_le_two T p.2)
    · intro b hb
      obtain ⟨hbS, -, hbF⟩ := hmem b hb
      have hmod : j b % 2 ^ T = j b := Nat.mod_eq_of_lt (hj b hbS)
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq]
      simp only [jf, hmod]
      exact (hsel b hbS p hbF).2
    · intro b hb b' hb' hjj
      obtain ⟨hbS, hbw, hbF⟩ := hmem b hb
      obtain ⟨hbS', hbw', hbF'⟩ := hmem b' hb'
      by_contra hne
      have hmod : j b % 2 ^ T = j b := Nat.mod_eq_of_lt (hj b hbS)
      have hmod' : j b' % 2 ^ T = j b' := Nat.mod_eq_of_lt (hj b' hbS')
      have hjeq : j b = j b' := by
        have := congrArg Fin.val hjj
        simp only [jf, hmod, hmod'] at this
        exact this
      have hd := hdisj b hbS b' hbS' hne (hbw.trans hbw'.symm) hjeq
      exact Set.disjoint_left.mp hd (hsel b hbS p hbF).1 (hsel b' hbS' p hbF').1
  exact_mod_cast hcard

/-- The heavy labels of a layer carry little weighted selected mass. The layer is an arbitrary
finite set `S` of labels of one time generation `T` and depth `r`; `X` bounds the weighted
exceptional mass at the density ceiling `N ^ (-fr + τ)`. -/
theorem heavy_mass_le {ι : Type*} (S : Finset ι) {N κ r fr τ σ : ℝ} {W T M D : ℕ}
    {X : ℝ≥0∞} (hN : 0 < N) (hκ : 1 ≤ κ)
    (ω : Fin W → ℝ) (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (ν : Fin W → Measure Line) (hν : ∀ w, IsProbabilityMeasure (ν w))
    (E : Fin W → Set Inc) (B : Fin W → ℝ) (hB : ∀ w, 0 < B w)
    (g : Fin W → Obs → ℝ≥0∞) (hg : ∀ w, Measurable (g w))
    (hlaw : ∀ w, (selected (ν w) (E w)).map (obs (B w) (δ N r)) =
      (volume.prod Measure.count).withDensity (g w))
    (γ : ι → Fin W) (j : ι → ℕ) (hj : ∀ b ∈ S, j b < 2 ^ T)
    (c u : ι → E2) (Q : ι → Matrix (Fin 2) (Fin 2) ℝ) (R : ι → MvPolynomial (Fin 4) ℝ)
    (A : ι → Set Line) (F : ι → Set Inc) (ex : ι → Prop)
    (hdisj : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hc : ∀ b ∈ S, chart N M D κ T (j b : ℝ) r (B (γ b)) (E (γ b)) (c b) (u b) (Q b) (R b)
      (A b) (F b) (ex b))
    (htyp : ∑ w, ENNReal.ofReal (ω w) * selected (ν w) (E w)
      {p | ENNReal.ofReal (N ^ (-fr + τ)) < g w (obs (B w) (δ N r) p)} ≤ X) :
    ∑ b ∈ S.filter (fun b => ENNReal.ofReal (N ^ σ * N ^ (-fr) * |(Q b).det|) < ν (γ b) (A b)),
      ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b) ≤
      2 * X + ENNReal.ofReal (256 * κ ^ 4 * N ^ (τ - σ)) := by
  classical
  set a : ℝ≥0∞ := ENNReal.ofReal (N ^ (-fr + τ)) with ha
  set Exc : Fin W → Set Inc := fun w => {p | a < g w (obs (B w) (δ N r) p)} with hExc
  set μ : Fin W → Measure Inc := fun w => selected (ν w) (E w) with hμ
  set Cr : ι → Set Obs := fun b => crossing κ ((j b : ℝ) / (2 : ℝ) ^ T)
    (((j b : ℝ) + 1) / (2 : ℝ) ^ T) (δ N r / B (γ b)) (B (γ b)) (c b) (u b) (Q b) (R b)
    with hCr
  set c₁ : ℝ := 256 * κ ^ 4 * N ^ (τ - σ) with hc₁
  have hκ0 : 0 < κ := by linarith
  have hδ : 0 < δ N r := by unfold δ; positivity
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hExcm : ∀ w, MeasurableSet (Exc w) := fun w =>
    measurableSet_lt measurable_const ((hg w).comp (measurable_obs _ _))
  -- facts read from the charts
  have hFE : ∀ b ∈ S, F b ⊆ E (γ b) := by
    intro b hb p hp
    rcases hc b hb with ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩
    exact (hsel p hp).1
  have hFm : ∀ b ∈ S, MeasurableSet (F b) := by
    intro b hb
    rcases hc b hb with ⟨_, _, _, _, _, _, _, hF, _⟩
    exact hF
  have hAm : ∀ b ∈ S, MeasurableSet (A b) := by
    intro b hb
    rcases hc b hb with ⟨_, _, _, _, _, _, hA, _⟩
    exact hA
  have hsel : ∀ b ∈ S, ∀ p ∈ F b, p.1 ∈ A b ∧
      p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T) (((j b : ℝ) + 1) / (2 : ℝ) ^ T) := by
    intro b hb p hp
    rcases hc b hb with ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩
    exact ⟨(hsel p hp).2.1, (hsel p hp).2.2.1⟩
  have hcross : ∀ b ∈ S, ∀ p ∈ F b, obs (B (γ b)) (δ N r) p ∈ Cr b := by
    intro b hb p hp
    rcases hc b hb with ⟨_, _, _, _, hR, _, _, _, _, hwhole, hselc, _⟩
    obtain ⟨_, hpA, ht, hd⟩ := hselc p hp
    obtain ⟨hs, hv, hd', hc'⟩ := (hwhole p.1 hpA).2.2 p.2 ht
    exact obs_mem_crossing hκ0 hδ (hB _) (c b) (u b) (Q b) (R b) hR p ht hs hv hd' hc' hd
  have hvol : ∀ b ∈ S, (volume.prod Measure.count) (Cr b) ≤
      ENNReal.ofReal (256 * κ ^ 4 *
        ((((j b : ℝ) + 1) / (2 : ℝ) ^ T) - (j b : ℝ) / (2 : ℝ) ^ T) * |(Q b).det|) := by
    intro b hb
    rcases hc b hb with ⟨hdet, _, _, _, hR, _⟩
    have ht : (j b : ℝ) / (2 : ℝ) ^ T ≤ ((j b : ℝ) + 1) / (2 : ℝ) ^ T :=
      div_le_div_of_nonneg_right (by linarith) h2T.le
    exact reference_crossing hκ ht (div_pos hδ (hB _)) (hB _) (c b) (u b) (Q b) hdet (R b) hR
  -- one label: exceptional part plus the capped part
  have hsplit : ∀ b ∈ S, ((ν (γ b)).prod volume) (F b) ≤
      μ (γ b) (F b ∩ Exc (γ b)) + a * (volume.prod Measure.count) (Cr b) := by
    intro b hb
    have hrestr : ((ν (γ b)).prod volume) (F b) = μ (γ b) (F b) := by
      simp only [hμ, selected]
      rw [Measure.restrict_eq_self _ (hFE b hb)]
    rw [hrestr]
    refine (measure_le_inter_add_sdiff _ _ (Exc (γ b))).trans (add_le_add le_rfl ?_)
    exact Submission.Obl.k4_scalar_terminal_chart_packet_extraction.mass_le_of_density_le
      (measurable_obs _ _) (hg _) (hlaw _) (measurableSet_crossing ..) a
      (fun p hp => hcross b hb p hp)
  -- a heavy label pays its capped part with its full prior
  have hheavy : ∀ b ∈ S, ENNReal.ofReal (N ^ σ * N ^ (-fr) * |(Q b).det|) < ν (γ b) (A b) →
      a * (volume.prod Measure.count) (Cr b) ≤
        ENNReal.ofReal (c₁ / (2 : ℝ) ^ T) * ν (γ b) (A b) := by
    intro b hb hheavy
    calc a * (volume.prod Measure.count) (Cr b)
        ≤ a * ENNReal.ofReal (256 * κ ^ 4 *
          ((((j b : ℝ) + 1) / (2 : ℝ) ^ T) - (j b : ℝ) / (2 : ℝ) ^ T) * |(Q b).det|) :=
          mul_le_mul_right (hvol b hb) a
      _ = ENNReal.ofReal (c₁ / (2 : ℝ) ^ T) *
          ENNReal.ofReal (N ^ σ * N ^ (-fr) * |(Q b).det|) := by
          rw [ha, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hc₁, Real.rpow_add hN, Real.rpow_sub hN]
          have hσ0 : N ^ σ ≠ 0 := (Real.rpow_pos_of_pos hN σ).ne'
          field_simp
          ring
      _ ≤ ENNReal.ofReal (c₁ / (2 : ℝ) ^ T) * ν (γ b) (A b) :=
          mul_le_mul_right hheavy.le _
  -- the weighted exceptional parts of a layer
  have hexc : ∑ b ∈ S, ENNReal.ofReal (ω (γ b)) * μ (γ b) (F b ∩ Exc (γ b)) ≤ 2 * X := by
    set Fs : ι → Set Inc := fun b => if b ∈ S then F b else ∅ with hFs
    have hFsm : ∀ b, MeasurableSet (Fs b) := by
      intro b
      by_cases hb : b ∈ S
      · simpa [hFs, hb] using hFm b hb
      · simp [hFs, hb]
    have hmult : ∀ w p, (∑ b ∈ S.filter (fun b => γ b = w),
        (Fs b).indicator (1 : Inc → ℝ≥0∞) p) ≤ 2 := by
      intro w p
      apply layer_multiplicity_le_two S γ j hj A Fs hdisj
      intro b hb p hp
      simp only [hFs, hb, ite_true] at hp
      exact hsel b hb p hp
    calc ∑ b ∈ S, ENNReal.ofReal (ω (γ b)) * μ (γ b) (F b ∩ Exc (γ b))
        = ∑ w, ∑ b ∈ S.filter (fun b => γ b = w),
            ENNReal.ofReal (ω (γ b)) * μ (γ b) (F b ∩ Exc (γ b)) :=
          (Finset.sum_fiberwise S γ _).symm
      _ = ∑ w, ENNReal.ofReal (ω w) * ∑ b ∈ S.filter (fun b => γ b = w),
            μ w (Fs b ∩ Exc w) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b hb => ?_
          obtain ⟨hbS, hbw⟩ := Finset.mem_filter.mp hb
          simp only [hFs, hbS, ite_true, hbw]
      _ ≤ ∑ w, ENNReal.ofReal (ω w) * (2 * μ w (Exc w)) := by
          refine Finset.sum_le_sum fun w _ => mul_le_mul_right ?_ _
          exact sum_measure_inter_le_two (μ w) _ Fs hFsm (hmult w) (hExcm w)
      _ = 2 * ∑ w, ENNReal.ofReal (ω w) * μ w (Exc w) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
      _ ≤ 2 * X := mul_le_mul_right htyp 2
  -- the assignment budget of a layer
  have hassign : ∑ b ∈ S, ENNReal.ofReal (ω (γ b)) * ν (γ b) (A b) ≤
      ENNReal.ofReal ((2 : ℝ) ^ T) := by
    have h := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
      ν ω (fun b : S => γ b) (fun b : S => (⟨j b, hj b b.2⟩ : Fin (2 ^ T)))
      (fun b : S => A b) hν hω0 hω1 (fun b => hAm b b.2)
      (fun b b' hne hγ hjj => hdisj b b.2 b' b'.2 (fun h => hne (Subtype.ext h)) hγ
        (congrArg Fin.val hjj))
    rw [Finset.sum_coe_sort S (fun b => ENNReal.ofReal (ω (γ b)) * ν (γ b) (A b))] at h
    apply h.trans_eq
    rw [Fintype.card_fin, Nat.cast_pow, ENNReal.ofReal_pow (by norm_num)]
    simp
  -- assemble
  set H := S.filter (fun b => ENNReal.ofReal (N ^ σ * N ^ (-fr) * |(Q b).det|) < ν (γ b) (A b))
    with hH
  have hHS : H ⊆ S := Finset.filter_subset _ _
  calc ∑ b ∈ H, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b)
      ≤ ∑ b ∈ H, (ENNReal.ofReal (ω (γ b)) * μ (γ b) (F b ∩ Exc (γ b)) +
          ENNReal.ofReal (c₁ / (2 : ℝ) ^ T) *
            (ENNReal.ofReal (ω (γ b)) * ν (γ b) (A b))) := by
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨hbS, hbh⟩ := Finset.mem_filter.mp hb
        calc ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b)
            ≤ ENNReal.ofReal (ω (γ b)) * (μ (γ b) (F b ∩ Exc (γ b)) +
                ENNReal.ofReal (c₁ / (2 : ℝ) ^ T) * ν (γ b) (A b)) :=
              mul_le_mul_right ((hsplit b hbS).trans
                (add_le_add le_rfl (hheavy b hbS hbh))) _
          _ = _ := by ring
    _ = ∑ b ∈ H, ENNReal.ofReal (ω (γ b)) * μ (γ b) (F b ∩ Exc (γ b)) +
          ENNReal.ofReal (c₁ / (2 : ℝ) ^ T) *
            ∑ b ∈ H, ENNReal.ofReal (ω (γ b)) * ν (γ b) (A b) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ b ∈ S, ENNReal.ofReal (ω (γ b)) * μ (γ b) (F b ∩ Exc (γ b)) +
          ENNReal.ofReal (c₁ / (2 : ℝ) ^ T) *
            ∑ b ∈ S, ENNReal.ofReal (ω (γ b)) * ν (γ b) (A b) := by
        gcongr
    _ ≤ 2 * X + ENNReal.ofReal (c₁ / (2 : ℝ) ^ T) * ENNReal.ofReal ((2 : ℝ) ^ T) := by
        gcongr
    _ = 2 * X + ENNReal.ofReal c₁ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

end Submission.Obl.k4_true_forest_own_depth_preparation
