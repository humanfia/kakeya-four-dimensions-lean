import Submission.Obl.k4_finite_affine_parent_sources.SourceKeptHistoryCaps
import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleParameters
import Submission.Obl.k4_finite_affine_parent_sources.SourceSamplePureBudget
import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleDepths
import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleDensityGrid
import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleShare
import Submission.Obl.k4_finite_affine_parent_sources.SourceLocalizationParameters
import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildSelect
import Submission.Obl.k4_finite_affine_parent_sources.SourceSamplePalette
import Submission.Obl.k4_finite_affine_parent_sources.SourceDensityGrid
import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleStateMass
import Submission.Lib.K4ExactProblemOps

/-! Actual original-law window preparation and its common end-state restriction. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_finite_forest_width_selection
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

local instance optMeasActual (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingActual (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

theorem selectionSample : SelectionSample := by
  classical
  intro d₁ κ₁ ℓ S η ρ n unit gain m sg δ₀ N K L d W ω ν E P B f g G Mp Dp Mprep ε σ k p H
    T N₀ τ τd τa hd ma Qd Qa
    hd₁ hd₁1 hκ₁ hκ₁1 hℓ hS hS1 hη hρ hρ4 hn hu hgain hgrid hδ₀ hδgain hprob hflat hε hσ hp
    hnT hup hsmall huη huℓ hgainunit hLQd hQd hhd hQdc hQa hma hQac hτd0 hτa0
    hτdb hτab hhdb hmab hN₀ hbig h2κ hτ hτbudget hH hHmask hHfull hmass
  obtain ⟨hNge, hNt, hL, hω0, hω1, hνp, hBpos, hEunit⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G hprob
  have hpr := hprob
  obtain ⟨_, _, hK, _, _, _, _, _, hdata, hpureLaw, hangularLaw, _⟩ := hpr
  have hK1 : 1 ≤ K k := hK.1 k
  obtain ⟨Mdata, Ddata, hwd⟩ := hdata
  have hEm : ∀ w, MeasurableSet (E k w) := fun w =>
    ((hwd k).2.2.2.1 w).2.2.2.2.2.2.2.1
  have hNk : 1 < N k := lt_of_lt_of_le (by norm_num) (hNge k)
  have hNk0 : 0 < N k := zero_lt_one.trans hNk
  have hκ : 1 ≤ p.κ := hp.one_le_slack
  have hκ0 : 0 < p.κ := zero_lt_one.trans_le hκ
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0 : 0 < T := by linarith only [hn', hnT]
  have hρ1 : ρ ≤ 1 := by linarith only [hρ4]
  have hm : 0 < m := hgrid.1.1
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  letI : ∀ w, IsProbabilityMeasure (ν k w) := hνp k
  letI : ∀ w, IsFiniteMeasure (((ν k w).prod volume).restrict (E k w)) :=
    fun w => Submission.Lib.K4ExactProblemOps.prob_world_finite hprob k w
  have hstrict : StrictMonoOn sg (Iio m) := by
    apply strictMonoOn_of_lt_add_one Set.ordConnected_Iio
    intro i _ hi hnext
    exact hgrid.1.2.2.1 i hnext
  have hC : 1 ≤ (groupsC : ℝ) := by exact_mod_cast groupsC_spec.1
  obtain ⟨hδunit, hgain100, hδb⟩ := selection_grid_errors hρ hρ1 hgain.le hL.le hδgain hgainunit
  obtain ⟨hD4, hDu, hDlog⟩ := selection_window_constants hn hκ₁ hκ₁1 hρ hρ4 hu hnT hC hsmall
  have hu64 : unit ≤ 1 / 64 := by nlinarith only [hD4, hDu, hu]
  have hu1 : unit ≤ 1 := by linarith only [hu64]
  have hδ64 : δ₀ ≤ 1 / 64 := by linarith only [hδunit, hu64]
  have hmesh : ρ * gain ≤ unit := by
    have hrg : ρ * gain ≤ gain := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hρ1 hgain.le
    linarith only [hrg, hgain100, hgain]
  have hTD : T ≤ selectionLookahead κ₁ T := by
    unfold selectionLookahead
    rw [le_div_iff₀ hκ₁]
    nlinarith only [hκ₁1, hT0]
  have hTu : unit * T ≤ 1 / 64 := by nlinarith only [hDu, mul_le_mul_of_nonneg_left hTD hu.le]
  let b := selectionBudget n ρ unit L
  let A := N k ^ b
  let NN := N k ^ (unit * L)
  have hb : 0 ≤ b := by dsimp [b, selectionBudget, stagePower]; positivity
  have hApos : 0 < A := by dsimp [A]; positivity
  have hstrong : 10 ^ 40 * p.κ ^ 20 * K k ^ 4 * ((m : ℝ) + 2) ^ 4 ≤ A :=
    sample_budget_lower hT0.le hκ₁ hκ₁1 hρ hρ1 hu hu1 hL hκ hK1 hbig
  obtain ⟨hA10000, hκ7A, hκ192A, hκ1024A, hAfloor⟩ := sample_slack_costs hκ hK1 hstrong
  obtain ⟨hshareCost, hκ12A⟩ := sample_share_row_cost hκ hK1 hstrong
  have hA1 : 1 ≤ A := by linarith only [hA10000]
  obtain ⟨hNN256, hKNN, hκ7NN, hlog⟩ := sample_native_bounds hT0.le hκ₁ hκ₁1 hρ hρ1
    hu hu1 hL hκ hK1 hNk hbig
  obtain ⟨q⟩ := source_entropy_windows hgrid hn hκ₁ hκ₁1 hρ hρ4 hu hnT hC hsmall
    (by positivity) hmesh
  have hCw : winBase (K k) (NN ^ (-((n : ℝ) + 2))) q.count ^ (1 / 2 : ℝ) ≤ A := by
    dsimp only [A, b, NN]
    rw [selection_budget_native n ρ unit L (N k) hNk0.le]
    exact source_window_likelihood_bound hn hκ₁ hκ₁1 hρ hρ4 hu hnT hC hsmall q
      (by linarith only [hNN256]) (by linarith only [hK1]) hKNN hlog
  obtain ⟨S0, hS0, hS0mass, hshare⟩ := sample_share_masked hp (hνp k) (hω0 k) (hω1 k)
    (hEunit k) hNk.le hL.le hδ64 A hApos hshareCost H hH hmass
  by_cases hc : MixedCandidate (N k) L (W k) (ν k) (B k) Mprep d₁ ρ gain ε
      p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H
  · exact Or.inl hc
  apply Or.inr
  have hroom := fun i hi => sample_window_depth_room hp q hstrict hL.le hu.le hu64 hδ64
    hT0.le hTu (i := i) hi
  obtain ⟨Jd, rd, hrd, hrdonto⟩ := exists_indexed_depth_grid Qd
  have hconst := sample_pure_group_budget (b := b) hNk.le hκ hb hhdb hτdb hδb
    hA10000 hκ7A hκ192A (rfl : A = N k ^ b)
  have hloc := sample_localization_constants hNk (by positivity : 0 ≤ unit * L) hρ.le hρ1 hε.le
    hκ0.le hA1 hκ12A (rfl : A = N k ^ b) (selection_budget_fraction hρ.le (by positivity))
  have hδu : δ₀ ≤ unit := by linarith only [hδunit, hδ₀]
  obtain ⟨rq, hrq, hrqs, hratio, hprofq, ha1⟩ := sample_q_density_inputs hp hNk hL hd₁ hn
    hκ₁ hκ₁1 hu hu64 hδ₀.le hδu hδ64 hmesh hnT hTu
    (by linarith only [hNN256]) q hstrict Qd hQd hQdc hflat
  let Hx := A * N k ^ (unit * L / 100)
  let meshS := NN ^ (-T)
  let δv := sourcePaletteMesh n (N k) unit L
  let Cw := winBase (K k) δv q.count ^ (1 / 2 : ℝ)
  have hCwA : Cw ≤ A := hCw
  have hCw0 : 0 ≤ Cw := Real.rpow_nonneg (by unfold winBase; positivity) _
  have hNN0 : 0 < NN := Real.rpow_pos_of_pos hNk0 _
  have hmeshS : 0 < meshS := Real.rpow_pos_of_pos hNN0 _
  have hδv : 0 < δv := Real.rpow_pos_of_pos hNN0 _
  have hδpos : ∀ r : ℝ, 0 < δ (N k) r := fun r =>
    (Real.rpow_pos_of_pos hNk0 _).trans_le (δ_bounds hNk r).1
  have hMNN : (A ^ 6) ^ groupsC ≤ NN := by
    rw [← pow_mul]
    exact selection_group_power hNk.le (by positivity) hρ hρ1
  have hsmallCodes : ∀ i < q.count,
      16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (q.level (i + 1)))⁻¹ /
        ((2 : ℝ) ^ p.T (q.level i))⁻¹) ≤ meshS ∧
      (A ^ 6) ^ groupsC * (δ (N k) (p.r (q.middle i)) / δ (N k) (p.r (q.level i)) +
        16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (q.level (i + 1)))⁻¹ /
          ((2 : ℝ) ^ p.T (q.middle i))⁻¹)) +
        16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (q.level (i + 1)))⁻¹ /
          ((2 : ℝ) ^ p.T (q.level i))⁻¹) ≤ meshS := by
    intro i hi
    obtain ⟨hT1, hT2, hqt1, hqt2, hqt3, hδratio⟩ := source_window_scale_decay hp hn hκ₁ hκ₁1 hu
      hnT hmesh hδ₀.le hδu hNk.le hL.le q i hi
    exact kept_state_mesh_budget (by linarith only [hNN256])
      (by linarith only [hn', hnT]) (by positivity) hMNN (by dsimp [Hx]; positivity)
      hloc.2.2.1 (div_nonneg (hδpos _).le (hδpos _).le) hδratio
      (by positivity) hqt2 (by positivity) hqt3
  have hvel : ∀ w, ∀ᵐ l ∂ν k w, |l.2 3| ≤ K k ∧ |l.2 4| ≤ K k := by
    intro w
    filter_upwards [(prob_original_velocity_bound hprob k w).1] with l hl
    exact ⟨hl 0, hl 1⟩
  have hrow : 12 * p.κ / (N k ^ (ρ * (unit / 100) * L + ε) *
      N k ^ (-(unit / 100) * L)) ≤ Hx := by
    have h1 : ρ * (unit / 100) * L = ρ * (unit * L / 100) := by ring
    have h2 : -(unit / 100) * L = -(unit * L / 100) := by ring
    rw [h1, h2]
    exact hloc.2.2.2.1
  obtain ⟨i, hi, a, S1, S2, hlev, hS1m, hS2m, hS21, hS1sub, hS1pos, hfloorP, href, hwin,
      hcodes, hdel⟩ := selection_construct hp (hνp k) (hω0 k) (hω1 k) (hEunit k) hNk hm
    hc (fun w => (hH w).2) S0 hS0 (by positivity : 0 < 1 / (8 * p.κ ^ 2)) hS0mass
    q.level q.middle q.monotone (fun j => by have hj := q.level_lt j; omega)
    q.count q.count_pos (fun j hj => (q.between j hj).1) (fun j hj => (q.between j hj).2)
    δv (K k) hδv (by linarith only [hK1]) hvel groupsC_spec.2 (hBpos k)
    (τQ := A⁻¹) (by positivity)
    (g k) rq (τ := τd) (hgd := hd)
    (fun w j hj => (hpureLaw k w _ (hQd _ (hrq j hj)).1 (hQd _ (hrq j hj)).2).1)
    (fun w j hj => (hpureLaw k w _ (hQd _ (hrq j hj)).1 (hQd _ (hrq j hj)).2).2)
    (fun w j hj z hz => (hHmask w z hz).1 (rq j) (hrq j hj)) hhd.le hratio hprofq ha1
    hconst.2.2.1 hconst.2.2.2 hconst.2.1
    (hl := unit / 100) (Hx := Hx) (mesh := meshS)
    (by linarith only [hgain100]) (by linarith only [hu64])
    (fun j hj => (hroom j hj).2.1) (by simpa only [Real.rpow_natCast] using h2κ) hloc.1 hloc.2.1 hrow hmeshS
    (fun j hj => (hsmallCodes j hj).1) (fun j hj => (hsmallCodes j hj).2)
  let w₀ := p.world a
  let μ := (ν k w₀).prod (volume : Measure ℝ)
  let R := S0 w₀ ∩ {x | p.history m (q.level i) (w₀, x) = some a}
  have hS1R : S1 ⊆ R := hS1sub
  have hRm : MeasurableSet R := (hS0 w₀).1.inter
    (((hp.measurable_history (q.level i)).comp measurable_prodMk_left) (measurableSet_singleton _))
  have hRF : R ⊆ p.counted a := fun z hz => (history_some hp hz.2).2
  have hS1F : S1 ⊆ p.counted a := hS1R.trans hRF
  have hS2F : S2 ⊆ p.counted a := hS21.trans hS1F
  have hS1H : S1 ⊆ H w₀ := fun z hz => (hS0 w₀).2 (hS1R hz).1
  have hPF : p.counted a ⊆ p.packet a := fun z hz =>
    ⟨(hp.counted_support a z hz).2.1, (hp.counted_support a z hz).2.2.1⟩
  have hPfin : μ (p.packet a) ≠ ⊤ := by
    dsimp only [μ, w₀]
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hS1fin : μ S1 ≠ ⊤ := measure_ne_top_of_subset (hS1F.trans hPF) hPfin
  have hRfin : μ R ≠ ⊤ := measure_ne_top_of_subset (hRF.trans hPF) hPfin
  have hfloor : (1 / (64 * (m : ℝ) * p.κ ^ 2)) * μ.real (p.packet a) ≤ μ.real S1 := by
    convert hfloorP using 1 <;> congr 1 <;> ring
  have hpacket : ENNReal.ofReal (1 / (64 * (m : ℝ) * p.κ ^ 2)) * μ (p.packet a) ≤ μ S1 := by
    have h := ENNReal.ofReal_le_ofReal hfloor
    rw [ENNReal.ofReal_mul (by positivity), ofReal_measureReal hPfin, ofReal_measureReal hS1fin] at h
    exact h
  have hS1ne : μ S1 ≠ 0 := by
    intro hz
    have hh : 0 < (μ S1).toReal := hS1pos
    rw [hz] at hh
    norm_num at hh
  have hS1posE : 0 < μ S1 := pos_iff_ne_zero.mpr hS1ne
  obtain ⟨z₀, hz₀⟩ := nonempty_of_measure_ne_zero hS1ne
  have hband0 : 1 / 8 ≤ sg (p.lev a) := by rw [hlev]; exact (q.parent_band i).1
  have hband1 : sg (p.lev a) ≤ 1 / 4 := by rw [hlev]; exact (q.parent_band i).2
  have haxis := hHfull a (by linarith only [hband1]) ⟨z₀, hS1H hz₀, hS1F hz₀⟩
  let β := min (stagePower n ρ / 1000) (ℓ / 1000)
  have hθ1 : stagePower n ρ ≤ 1 := by
    unfold stagePower
    rw [div_le_iff₀ (by positivity)]
    linarith only [hρ1, Nat.cast_nonneg (α := ℝ) n]
  have hβ1 : β ≤ 1 := (min_le_left _ _).trans (by linarith only [hθ1])
  obtain ⟨π, hπ, hδv', hblur0, hblur, hpal, hdom⟩ := sample_parent_palette hprob hp n unit ρ β ma τd τa
    hm hu (by linarith only [hNN256]) hℓ.le hS1 hβ1 hma.le huℓ hδunit hτdb hτab hmab hstrong
    a hband0 haxis.2 Qa Qd hQa hQac R S1 hRm hRF hS1R hS1posE hpacket
    (fun z hz => hshare w₀ z hz.1 a rfl hband1 (hRF hz))
    (fun z hz => hHmask w₀ z ((hS0 w₀).2 hz.1))
  let Φ := labelFrame p a (B k w₀) (δ (N k) (p.r (p.lev a)))
  let Pn := Φ.normTest (δ (N k) (p.r (p.lev a))) (p.test a)
  let code := stateCode (frameBase Φ) (frameSignal Φ Pn) meshS
  let endL : Incidence → Option (Fin p.C) := fun x => p.history m (q.level (i + 1)) (w₀, x)
  let wt : Option (Fin p.C) → ENNReal := fun h => μ (R ∩ {x | endL x = h})
  let F := keptSet (μ.restrict S2) endL code wt (ENNReal.ofReal ((A ^ (6 * groupsC + 2))⁻¹))
  let Gm := S2 ∩ F
  have hend : Measurable endL := (hp.measurable_history _).comp measurable_prodMk_left
  have hcode : Measurable code := measurable_state_code (measurable_frameBase Φ)
    (measurable_frameSignal Φ Pn) meshS
  have hwt : ∑ h, wt h ≤ ENNReal.ofReal 8 * μ S1 := by
    rw [sum_reference_history_mass μ R endL hend]
    have hh := ENNReal.ofReal_le_ofReal href
    rw [ofReal_measureReal hRfin, ENNReal.ofReal_mul (by norm_num), ofReal_measureReal hS1fin] at hh
    exact hh
  have hV : ∀ h : Option (Fin p.C), ∃ V : Finset (Fin 4 → ℤ), (V.card : ℝ) ≤ 81 * A ^ (6 * groupsC) ∧
      ∀ x ∈ S2, endL x = h → code x ∈ V := by
    simpa only [← pow_mul] using hcodes
  have hrowtail : N k ^ (-ρ * (unit / 100) * L - ε) ≤ A⁻¹ := by
    have hex : -ρ * (unit / 100) * L - ε = -ρ * (unit * L / 100) - ε := by ring
    rw [hex]
    exact hloc.2.2.2.2
  have hdel' : μ (S1 \ S2) ≤ ENNReal.ofReal A⁻¹ * μ (p.packet a) +
      ENNReal.ofReal ((A ^ 6)⁻¹) * μ S1 +
      ENNReal.ofReal (N k ^ (-ρ * (unit / 100) * L - ε)) * μ (p.packet a) := by
    simpa only [pow_one] using hdel
  have hdelReal : μ.real (S1 \ S2) ≤ μ.real S1 / 4 :=
    (original_deletion_real_bound μ hS1fin hPfin (by positivity) (by positivity) hrowtail hdel').trans
      (window_deletion_power_budget hA10000 (by exact_mod_cast hm) hκ0
        measureReal_nonneg hκ1024A hfloor)
  obtain ⟨hGmm, hGmhalf, hGmpos⟩ := sample_kept_state_mass hp w₀ (q.level (i + 1)) groupsC A
    hA10000 S1 S2 hS2m hS21 hS1fin hS1pos code hcode wt hwt hV hdelReal
  have hGmS1 : Gm ⊆ S1 := fun z hz => hS21 hz.1
  have hGmH : Gm ⊆ H w₀ := hGmS1.trans hS1H
  have hGmF : Gm ⊆ p.counted a := hGmS1.trans hS1F
  have hGmInter : Gm ∩ p.counted a = Gm := inter_eq_left.mpr hGmF
  have hroomModel : sg (p.lev a) + unit + δ₀ ≤ 1 / 2 := by
    linarith only [hband1, hu64, hδ64]
  refine ⟨a, Gm, π, hGmm, hGmH, ?_, hband0, hband1, ?_, hroomModel, hπ, ?_⟩
  · rw [hGmInter]
    exact selection_mass_floor hm' hκ hτ measureReal_nonneg hS1pos hτbudget hfloor hGmhalf
  · intro b hbw hab hsb hGB
    apply (hHfull b hsb ?_).1
    obtain ⟨z, hzG, hzB⟩ := hGB
    refine ⟨z, ?_, hzB⟩
    rw [hbw]
    exact hGmH hzG
  · intro D hDa hDπ hDS hDm hDne hDD hDK hDepth hDo hSend hfa hfl hpf hlf
    have hDw : D.w₀ = w₀ := by change p.world D.parent = p.world a; rw [hDa]
    have hDi : D.i₀ = q.level i := by change p.lev D.parent = q.level i; rw [hDa, hlev]
    have hD0 : D.D₀ = MajorFrame.frame (p.frame D.parent) := by simpa only [hDa] using hDD
    have hDpower : D.K = A ^ (100 * (groupsC + 2)) := by
      exact hDK.trans (selection_stage_power n ρ unit L (N k) hNk0).symm
    have hdepth : ∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → D.depth x ≤ q.level (i + 1) := by
      intro x hx hx1
      have hh := ((q.source_depth_range hu.le hstrict hi x).2).trans (q.between i hi).2
      simpa only [hDepth, hlev] using hh
    have hge : ∀ x, D.i₀ ≤ D.depth x := by
      intro x
      have hh := (q.source_depth_range hu.le hstrict hi x).1
      simpa only [hDi, hDepth, hlev] using hh
    have hS0E : S0 w₀ ⊆ E k w₀ := by
      intro z hz
      obtain ⟨b, hb, hbw, hzb⟩ := (hH w₀).2 ((hS0 w₀).2 hz)
      have he := (hp.counted_support b z hzb).1
      simpa only [hbw] using he
    have hR0 : μ R ≠ 0 := ne_of_gt (hS1posE.trans_le (measure_mono hS1R))
    have hMask2 : S2 ⊆ E k w₀ ∩ densMask (g k w₀) (B k w₀) (N k) τd f rd := by
      intro z hz
      exact ⟨(hp.counted_support a z (hS2F hz)).1,
        selectionMask_densMask (hHmask w₀ z (hS1H (hS21 hz))) rd hrd⟩
    have hCover : ∀ x : ℝ, 0 ≤ x → x ≤ T → ∃ j,
        p.r (q.level i) + unit * L * x ≤ rd j ∧
        rd j ≤ p.r (q.level i) + unit * L * x + hd ∧
        f (p.r (q.level i)) + d₁ * (rd j - p.r (q.level i)) - 2 * (δ₀ * L) ≤ f (rd j) := by
      apply selected_profile_cover hQdc hQd hrdonto hflat
        (hp.level_bounds _ (q.level_lt i)).2.1.le
      · have hh := (hroom i hi).2.2 0 (by norm_num) hT0.le
        simpa only [mul_zero, add_zero] using hh.2
      · exact (hroom i hi).2.2
    have hframeD : D.frame (N k) (B k) = Φ := by
      rw [frame_eq_labelFrame hp D hD0, hDa]
    have hPD : (D.stage (N k) L unit (ν k) (B k)).P = Pn := by
      change (D.frame (N k) (B k)).normTest (δ (N k) (p.r (p.lev D.parent))) (p.test D.parent) = _
      rw [hframeD, hDa]
    have hcodeD : stateCode (frameBase (D.frame (N k) (B k)))
        (frameSignal (D.frame (N k) (B k)) (D.stage (N k) L unit (ν k) (B k)).P) meshS = code := by
      rw [hframeD, hPD]
    have hwtD : endHistoryWeight D (q.level (i + 1)) (S0 w₀) (ν k) m = wt := by
      funext h
      unfold endHistoryWeight
      rw [hDw, hDi, hDa]
    have hKeptD : S2 ∩ keptSet (((ν k D.w₀).prod volume).restrict S2)
        (fun z => p.history m (q.level (i + 1)) (D.w₀, z))
        (stateCode (frameBase (D.frame (N k) (B k)))
          (frameSignal (D.frame (N k) (B k)) (D.stage (N k) L unit (ν k) (B k)).P) meshS)
        (endHistoryWeight D (q.level (i + 1)) (S0 w₀) (ν k) m)
        (ENNReal.ofReal ((A ^ (6 * groupsC + 2))⁻¹)) = Gm := by
      rw [hcodeD, hwtD, hDw]
    have hDSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀) := by
      have hright : D.t₀ + D.q₀ = ((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a) := by
        change (p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T (p.lev D.parent) +
          ((2 : ℝ) ^ p.T (p.lev D.parent))⁻¹ = _
        rw [hDa]
        field_simp
        <;> ring
      intro z hz
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hDa] using (hDo hz).1
      · change (p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T (p.lev D.parent) < z.2
        simpa only [hDa] using (hDo hz).2.1
      · rw [hright]
        exact (hDo hz).2.2
    apply kept_history_caps hp (hνp k) (hEunit k)
      hEm
      hNk hL hd₁ hd₁1.le D n unit T N₀ A (by omega) hu hnT hup hA10000 hκ7A
      (selection_intermediate_power hNk.le (by positivity) hρ hρ1) hN₀
      (by rw [hDw]; exact hBpos k w₀) hD0 hDpower hDm
      (by rw [hDπ]; exact hπ)
      (by simpa only [hDπ] using hpal)
      (q.level (i + 1)) (q.level_lt (i + 1)) hdepth hge
      (S0 w₀) S1 S2 δv Cw (sourcePaletteBlur n (N k) unit L β)
      (hS0 w₀).1 (by simpa only [hDw] using hS0E)
      (by simpa only [hDw, hDi, hDa] using hS1R)
      hS2m hS21 (by simpa only [hDa] using hS2F) hCw0 hCwA
      (by simpa only [hDw, hDi, hDa] using hwin)
      (by simpa only [hDw, hDi, hDa] using hR0)
      (by simpa only [hDw, hDi, hDa, hDπ, hlev] using hdom) hblur
      (g k w₀) rd
      (fun j => (hpureLaw k w₀ _ (hQd _ (hrd j)).1 (hQd _ (hrd j)).2).1)
      (by simpa only [hDw] using fun j => (hpureLaw k w₀ _ (hQd _ (hrd j)).1 (hQd _ (hrd j)).2).2)
      τd hd hhd.le (by simpa only [hDw] using hMask2)
      (by simpa only [hDi] using hCover) hconst.1 meshS hmeshS le_rfl
      (by simpa only [hKeptD] using hDS) hDSo
    · intro z hz
      rw [hDw]
      exact (hH w₀).2 (hGmH (hDS hz))
    · exact hSend

end
end Submission.Obl.k4_finite_affine_parent_sources
