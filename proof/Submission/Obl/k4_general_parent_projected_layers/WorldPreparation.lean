import Submission.Obl.k4_general_parent_projected_layers.Prepare
import Submission.Obl.k4_general_parent_projected_layers.WorldReadiness
import Submission.Obl.k4_general_parent_projected_layers.Support.EventualSupport
import Submission.Obl.k4_general_parent_projected_layers.Support.EventualCaps
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldSelection
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldTerminalSupport
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldGeometry

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery (scalarCell scalarX)
open Submission.Obl.k4_horizontal_supercritical_three_projections (chartLaw chartLaw_mass_lower)

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- Original terminal tables and native palette caps prepare the worlds for
Scalar without changing their original trajectory priors. -/
theorem worldsPrepared_of_data (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) (hcaps : a.Caps p) (hatlases : a.Atlases p) :
    a.WorldsPrepared p := by
  classical
  obtain ⟨L, hL, Htables⟩ := a.eventually_terminal_tables p hp hcommon hcaps hatlases
  refine ⟨L, by linarith, ?_⟩
  intro a₀ ha₀ hU s hslo hshi m hm
  let M := L * a₀ / 2
  have hs : 0 < s := ha₀.trans_le hslo
  have hLM : 0 < L * a₀ := mul_pos (by linarith) ha₀
  have hM : 0 < M := by dsimp [M]; positivity
  have hsM : s < M := by
    have hh := mul_lt_mul_of_pos_right hL ha₀
    dsimp [M]
    linarith
  have hML : M ≤ L * a₀ := by dsimp [M]; linarith
  have hm0 : 0 < m := hLM.trans hm
  refine ⟨M, 2 * M + s + 2, hsM, hML, by positivity, ?_⟩
  intro η₁ hη₁ θ hθ
  let δ := min (η₁ / 10) (min (1 / 100) (s / 10))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hδη : 10 * δ ≤ η₁ := by
    have hh : δ ≤ η₁ / 10 := min_le_left _ _
    linarith
  have hδ1 : δ ≤ 1 / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hδs : δ ≤ s := by
    have hh : δ ≤ s / 10 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  let η := δ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hN1 (k : ℕ) : 1 ≤ p.N k := by linarith [hp.1 k]
  have Hconst := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.2.1 hp.2.2.1.1 hp.2.2.1.2 1 (a := 0) (b := δ) hδ
    (A := 2000) (by norm_num)
  have Herror := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hp.2.1 (a := -δ) (b := -η) (by dsimp [η]; linarith) 6
  have Hprior := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.2.1 hp.2.2.1.1 hp.2.2.1.2 1 (a := 0) (b := θ) hθ
    (A := 2) (by norm_num)
  refine ⟨η, hη, ?_⟩
  filter_upwards [Htables a₀ m ha₀ hm δ hδ,
    a.eventually_scalar_world_caps p hp hcommon hcaps hs.le hM hm0,
    Hconst, Herror, Hprior] with k hTables hCaps hConst hError hPrior
  intro ζ hζ hmass
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK1 : 1 ≤ p.K k := hp.2.2.1.1 k
  have hK : 0 ≤ p.K k := by linarith
  have hConst' : 2000 * p.K k ≤ p.N k ^ δ := by
    simpa only [pow_one, Real.rpow_zero, mul_one] using hConst.le
  have hKN : p.K k ≤ p.N k ^ δ := by
    have hh := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2000) hK
    have hh' : p.K k ≤ 2000 * p.K k := by simpa only [one_mul] using hh
    exact hh'.trans hConst'
  have h8KN : 8 * p.K k ≤ p.N k ^ δ :=
    (mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 2000) hK).trans hConst'
  have h1200KN : 1200 * p.K k ≤ p.N k ^ δ :=
    (mul_le_mul_of_nonneg_right (by norm_num : (1200 : ℝ) ≤ 2000) hK).trans hConst'
  have h1944 : 1944 ≤ p.N k ^ δ := by
    calc
      (1944 : ℝ) ≤ 2000 * 1 := by norm_num
      _ ≤ 2000 * p.K k := mul_le_mul_of_nonneg_left hK1 (by norm_num)
      _ ≤ _ := hConst'
  rcases hcommon k with ⟨hb, hν, hπ, hdom, hρ, htime, hρmass, hP, hbase, hjet⟩
  letI := hν
  letI := hπ
  letI : IsFiniteMeasure (a.mu k) := a.incidence_finite p hcommon k
  have hζμ : ζ ≤ a.mu k := hζ.trans hρ
  letI : IsFiniteMeasure ζ := ⟨(hζμ univ).trans_lt (measure_lt_top _ _)⟩
  obtain ⟨T⟩ := hTables s hslo hshi (hshi.trans hU.le)
  let C := a.scalarGoodLabels p k
  let χ := p.N k ^ (-m)
  let g := narrow p k s
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  have hg : 0 < g := Real.rpow_pos_of_pos hN _
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have hC : MeasurableSet C := a.measurableSet_scalarGoodLabels p k hb
  let ζ₀ := ζ.restrict T.retained
  have hζ₀ : ζ₀ ≤ ζ := Measure.restrict_le_self
  have hζ₀μ : ζ₀ ≤ a.mu k := hζ₀.trans hζμ
  have hsource : ∀ᵐ z ∂ζ₀, z.1 ∈ C := ae_mono hζ₀μ (a.ae_scalarGoodLabels p hcommon k)
  have htimeμ : ∀ᵐ z ∂a.mu k, z.2 ∈ Icc (0 : ℝ) 1 := by
    have hh : ∀ᵐ z ∂a.mu k, z ∈ univ ×ˢ Icc (0 : ℝ) 1 := ae_iff.mpr htime
    exact hh.mono fun _ hz => hz.2
  let cost := fun u : Fin 4 → ℤ =>
    (χ * g * (a.pi k {v | ⌊v / χ⌋ = u 0}).toReal) *
      (((T.tables u).card : ℝ) * (p.N k ^ (-M)) ^ 2) * (width p k s) ^ p.d
  have hcost : ∀ u ∈ T.worlds, 0 ≤ cost u := by intro u hu; dsimp [cost]; positivity
  obtain ⟨G, ζ₁, hG, hζ₁, hLoss, hCover, hMassBudget, hGood⟩ :=
    select_scalar_worlds (a.nu k) (a.mu k) ζ₀ hK
      (Real.rpow_pos_of_pos hN (3 * δ)) (Real.rpow_nonneg hN.le (-δ)) hdom hζ₀μ
      C hC (a.b k) hb T.worlds T.cover hsource (ae_mono hζ₀μ htimeμ)
      cost hcost T.budget
  have hζ₁μ : ζ₁ ≤ a.mu k := hζ₁.trans hζ₀μ
  letI : IsFiniteMeasure ζ₁ := ⟨(hζ₁μ univ).trans_lt (measure_lt_top _ _)⟩
  have hζ₁dom : ζ₁ ≤ ENNReal.ofReal (p.N k ^ δ) • (a.nu k).prod volume := by
    refine hζ₁μ.trans (hdom.trans ?_)
    intro E
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  have hζ₁time : ζ₁ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((hζ₁μ _).trans_eq htime) bot_le
  have hretained : ∀ᵐ z ∂ζ₁, z ∈ T.retained := ae_mono hζ₁ (ae_restrict_mem T.measurable)
  let W := fun u => coefficientWorld (a.P k) (a.b k) (p.K k) χ g C u
  have hReady (u : Fin 4 → ℤ) (hu : u ∈ G) :
      (W u).Ready (p.N k) η₁ p.d s M (2 * M + s + 2) χ g (2 * p.K k)
        (a.b k) (a.P k) (a.nu k) (a.pi k) ζ₁ := by
    obtain ⟨hprior, hcostPrior, hcurrent⟩ := hGood u hu
    have hcrop : MeasurableSet (W u).crop := measurableSet_projectedWorldCrop hC (a.b k) hb χ g u
    have hpriorR : 0 < (a.nu k (W u).crop).toReal := ENNReal.toReal_pos hprior (measure_ne_top _ _)
    have hentry : ENNReal.ofReal (p.N k ^ (-δ)) * a.nu k (W u).crop ≤
        ζ₁ ((W u).crop ×ˢ (univ : Set ℝ)) := by
      have hh : ENNReal.ofReal (p.N k ^ (-δ) * (a.nu k (W u).crop).toReal) ≤
          ζ₁ ((W u).crop ×ˢ Icc (0 : ℝ) 1) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top ζ₁ _)]
        exact ENNReal.ofReal_le_ofReal hcurrent
      have heq : ENNReal.ofReal (p.N k ^ (-δ) * (a.nu k (W u).crop).toReal) =
          ENNReal.ofReal (p.N k ^ (-δ)) * a.nu k (W u).crop := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [heq] at hh
      exact hh.trans (measure_mono (Set.prod_mono le_rfl (subset_univ _)))
    have hdense : ENNReal.ofReal (p.N k ^ (-δ)) ≤ chartLaw (a.nu k) ζ₁ (W u).crop univ :=
      chartLaw_mass_lower (a.nu k) ζ₁ (W u).crop hprior _ hentry
    apply ScalarWorld.ready_of_small_loss (W u) (hp.1 k) hp.2.2.2.1 hp.2.2.2.2.1 hs hsM
      hδ hδη hδ1 h1944 hχ.le hg.le hcrop hprior
      (fun l hl => coefficientWorld_tags _ _ _ _ _ _ _ hl)
      (coefficientWorld_center _ _ hK _ _ _ _)
      (fun l hl t => coefficientWorld_y _ _ _ _ _ _ _ hl t)
      (fun l hl t => coefficientWorld_x _ hP _ _ _ _ _ _ hl t)
      (measurable_nativeScalarCoefficients _ hb _ _ _ hcrop) hζ₁dom hζ₁time
      (fun l i => (a.scalar_world_coefficient_bound p hp k hχ hg u l i).trans h8KN) hdense
    · intro r q j hr hrs
      have hh := hCaps ζ₁ hζ₁μ u hprior r hr hrs q j
      refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
      have hc0 : 0 ≤ (W u).param χ g (a.nu k) (a.pi k) := by
        unfold ScalarWorld.param
        positivity
      change 1200 * p.K k * (p.N k ^ (-M)) ^ 2 * (W u).param χ g (a.nu k) (a.pi k) *
          (p.N k ^ (-r)) ^ p.d ≤
        p.N k ^ δ * (p.N k ^ (-M)) ^ 2 * (W u).param χ g (a.nu k) (a.pi k) *
          (p.N k ^ (-r)) ^ p.d
      gcongr
    · refine ⟨T.tables u, ?_, ?_⟩
      · change ((χ * g * (a.pi k {v | ⌊v / χ⌋ = u 0}).toReal) /
          (a.nu k (W u).crop).toReal) * (((T.tables u).card : ℝ) * (p.N k ^ (-M)) ^ 2) *
            (p.N k ^ (-s)) ^ p.d ≤ p.N k ^ (3 * δ)
        have heq : ((χ * g * (a.pi k {v | ⌊v / χ⌋ = u 0}).toReal) /
            (a.nu k (W u).crop).toReal) * (((T.tables u).card : ℝ) * (p.N k ^ (-M)) ^ 2) *
              (p.N k ^ (-s)) ^ p.d = cost u / (a.nu k (W u).crop).toReal := by
          dsimp only [cost, width]
          ring
        rw [heq]
        exact (div_le_iff₀ hpriorR).mpr hcostPrior
      · exact world_scalar_terminal_support (a.nu k) ζ₁ (a.P k) hP (a.b k) hb
          (p.K k) χ g (p.N k ^ (-M)) (width p k s) C hC u T.retained hretained (T.tables u)
          (fun z hz htag => (T.support u z hz htag).2)
  refine ⟨ζ₁, G, W, hζ₁.trans hζ₀, hReady, ?_, ?_⟩
  · intro u hu u' hu' hne
    exact projectedWorldCrop_disjoint C (a.b k) χ g hne
  · have hζ₀univ : ζ₀ univ = ζ T.retained := Measure.restrict_apply_univ T.retained
    have hNative : (ζ univ).toReal ≤ (ζ₀ univ).toReal + p.N k ^ (-s) := by
      have hc : (ζ T.retainedᶜ).toReal ≤ p.N k ^ (-s) := by
        have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((hζμ _).trans T.loss)
        simpa only [width, ENNReal.toReal_ofReal (Real.rpow_nonneg hN.le _)] using hh
      have heq : (ζ univ).toReal = (ζ₀ univ).toReal + (ζ T.retainedᶜ).toReal := by
        rw [hζ₀univ, ← measure_add_measure_compl T.measurable,
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      linarith
    have hRatio : p.K k * p.N k ^ δ / p.N k ^ (3 * δ) ≤ p.N k ^ (-δ) := by
      calc
        _ ≤ p.N k ^ δ * p.N k ^ δ / p.N k ^ (3 * δ) := by gcongr
        _ = _ := by
          rw [← Real.rpow_add hN, ← Real.rpow_sub hN]
          congr 1
          ring
    have hDepth : p.N k ^ (-s) ≤ p.N k ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
    have hMass : p.N k ^ (-η) ≤ (ζ univ).toReal := by
      have hh := ENNReal.toReal_mono (measure_ne_top ζ univ) hmass
      simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg hN.le _)] using hh
    have hHalf : (ζ univ).toReal ≤ 2 * (ζ₁ univ).toReal := by
      linarith [hError.le]
    have h2K : 2 * p.K k ≤ p.N k ^ θ := by
      simpa only [pow_one, Real.rpow_zero, mul_one] using hPrior.le
    have hpsum : 0 ≤ ∑ u ∈ G, (a.nu k (W u).crop).toReal :=
      Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    have hpriorMass : (ζ univ).toReal ≤
        p.N k ^ θ * (∑ u ∈ G, (a.nu k (W u).crop).toReal) := by
      calc
        _ ≤ 2 * (ζ₁ univ).toReal := hHalf
        _ ≤ 2 * (p.K k * (∑ u ∈ G, (a.nu k (W u).crop).toReal)) :=
          mul_le_mul_of_nonneg_left hMassBudget (by norm_num)
        _ = (2 * p.K k) * (∑ u ∈ G, (a.nu k (W u).crop).toReal) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h2K hpsum
    have hcancel : p.N k ^ θ * p.N k ^ (-θ) = 1 := by
      rw [← Real.rpow_add hN]
      simp
    calc
      _ ≤ (p.N k ^ θ * (∑ u ∈ G, (a.nu k (W u).crop).toReal)) * p.N k ^ (-θ) :=
        mul_le_mul_of_nonneg_right hpriorMass (Real.rpow_nonneg hN.le _)
      _ = (p.N k ^ θ * p.N k ^ (-θ)) * (∑ u ∈ G, (a.nu k (W u).crop).toReal) := by ring
      _ = _ := by rw [hcancel, one_mul]

end PreparedModel

/-- The geometric world preparation for every valid general parent. -/
theorem worlds_principle : WorldsPrinciple := by
  intro p hp α _ a ha
  exact a.worldsPrepared_of_data p hp ha.1 ha.2.1 ha.2.2.1

end

end Submission.Obl.k4_general_parent_projected_layers
