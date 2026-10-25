import Submission.Obl.k4_horizontal_strict_parameter_step.PowerComparedLayer
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonPreparation
import Submission.Obl.k4_horizontal_strict_parameter_step.ComparisonMesh
import Submission.Obl.k4_horizontal_strict_parameter_step.PartialScales
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The original compact-range hypotheses and the old full-time engine give
comparison-prepared charts at every requested depth and every positive loss. -/
theorem compared_layers_at (hMatching : MatchingInput)
    (hN : ∀ k, 2 ≤ cfg.N k) (hNt : Tendsto cfg.N atTop atTop)
    (hK : ∀ k, 3 ≤ cfg.K k)
    (hsub : ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ a)
    (hd : 0 ≤ cfg.d) (hd1 : cfg.d < 1) (hκ : 0 < cfg.κ) (hκ1 : 2 * cfg.κ < 1)
    (hℓ : cfg.ℓ = cfg.κ)
    (hbasic : cfg.Basic) (hcaps : cfg.Caps) (hatlas : cfg.Atlas) (hnested : cfg.Nested)
    {sMax u θ : ℝ} (hsMax : 0 < sMax) (hU : 4 * sMax ≤ cfg.U)
    (he : 100 * sMax ≤ cfg.e₀) (hu : 2 * cfg.κ < u) (hu1 : u ≤ 1) (hθ : 0 < θ)
    (hθmax : θ ≤ (1 - cfg.d) / 10000 * (u - 2 * cfg.κ))
    (hold : LayersAt cfg.N cfg.d cfg.e₀ u sMax cfg.ρ cfg.π cfg.b) :
    ComparedLayersAt cfg.N cfg.d cfg.e₀ u θ sMax cfg.ρ cfg.π cfg.b := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [hN k]
  have hNgt : ∀ k, 1 < cfg.N k := fun k => by linarith [hN k]
  have hK1 : ∀ k, 1 ≤ cfg.K k := fun k => by linarith [hK k]
  have he₀ : 0 < cfg.e₀ := by linarith
  have hU₀ : 0 < cfg.U := by linarith
  have hu0 : 0 ≤ u := by linarith
  let mid := (1 + cfg.d) / 2
  have hmid0 : 0 ≤ mid := by dsimp [mid]; linarith
  have hmid1 : mid < 1 := by dsimp [mid]; linarith
  have hmidgt : cfg.d < mid := by dsimp [mid]; linarith
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmbmid⟩ :=
    unnormalized_matching_of_input hMatching hmid0 hmid1
  obtain ⟨m, hmid⟩ := matchingScales_at_middle hmidgt hmid0 hmid1 hε₀
  have hmb : MatchBound m.middle ε₀ R₀ := hmid.symm ▸ hmbmid
  let J := Classical.choice nonempty_jetData
  intro target htarget htargetMax δ hδ
  let s := target / (1 + θ)
  have hs : 0 < s := (partial_old_depth_bounds hθ htarget htargetMax).1
  have hsOldMax : s < sMax := (partial_old_depth_bounds hθ htarget htargetMax).2.2
  let E := θ * s * (1000 / (1 - cfg.d))
  have hE : 0 < E := by dsimp [E]; positivity
  have hθgain : θ ≤ gain cfg.d cfg.κ u := by
    have heq : gain cfg.d cfg.κ u = (1 - cfg.d) / 10000 * (u - 2 * cfg.κ) := by
      dsimp [gain]
      ring
    rw [heq]
    exact hθmax
  have hEjet : E ≤ jetDepth cfg.κ u s := (partial_jet_depth_bounds hd1 hθ hθgain hs).2
  have hEsmall : E < sMax / 10 := hEjet.trans_lt (jetDepth_bounds hκ hu hu1 hs hsOldMax).2
  have hEMax : E ≤ sMax := by linarith
  have hsU : s + E ≤ cfg.U := by linarith
  have hse : s + E < cfg.e₀ := by linarith
  have hroom : -u * s + 2 * cfg.κ * (s + E) ≤ -8 * E :=
    partial_transverse_room (by linarith : cfg.κ ≤ 1) hE.le hEjet
  obtain ⟨p⟩ := exists_comparison_exponents hδ hs m.size_one
  have hprod : 0 ≤ p.x * m.size := mul_nonneg p.x_pos.le (zero_le_one.trans m.size_one)
  have hηs : p.η < s := by linarith [p.width_gap]
  have hεMax : p.ε ≤ sMax := by linarith [p.ε_η]
  let R := 2 + cfg.U + cfg.e₀ + cfg.e₀⁻¹ + 100 * sMax + s⁻¹
  have hR : 1 < R := by dsimp [R]; have := inv_pos.mpr he₀; have := inv_pos.mpr hs; linarith
  have hRp : 0 < R := by linarith
  have hRmesh : 100 * sMax ≤ R := by
    dsimp [R]
    have := inv_pos.mpr he₀
    have := inv_pos.mpr hs
    linarith
  have hRe : cfg.e₀ ≤ R := by
    dsimp [R]
    have := inv_pos.mpr he₀
    have := inv_pos.mpr hs
    linarith
  have hRe' : R⁻¹ ≤ cfg.e₀ := (inv_le_comm₀ hRp he₀).mpr (by
    dsimp [R]
    have := inv_pos.mpr hs
    linarith)
  have hsR : s ≤ R := by
    dsimp [R]
    have := inv_pos.mpr he₀
    have := inv_pos.mpr hs
    linarith
  have hcaps' : Hyp2 cfg.N cfg.K cfg.d cfg.S cfg.μ cfg.π cfg.b cfg.P := hcaps
  have hwidthCaps := eventually_original_width_caps hNgt hcaps' hR
  have hmesh := uniformComparisonMesh cfg.N cfg.K hN hNt hK1 hsub sMax cfg.e₀ R hsMax he hRmesh
  have hfit := eventually_native_witness_fit hN1 hNt hK1 hsub p.η_pos (by linarith : s < cfg.e₀)
  have hfine := cfg.eventually_fine_preparation hN hNt hK1 hsub hbasic hcaps hatlas hnested
    hℓ hκ.le hκ1.le hs hE hsU hse hroom
  have hnums := p.eventually_budgets hN1 hNt hK1 hsub hd hd1.le m.size_one
  have hbig := Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow
    hNt p.x_pos (max 4 (max R₀ (max (3 * J.C₂) (budgetMatchingConstant m J))))
  have hold₁ := hold 1 (fun _ : Fin 1 => s)
    (fun _ => And.intro hs hsOldMax) p.ε p.ε_pos
  filter_upwards [hold₁, hfine, hwidthCaps, hmesh, hfit, hnums, hbig]
    with k hkold hkfine hkcaps hkmesh hkfit hknums hkbig
  have hNp : 0 < cfg.N k := by linarith [hN k]
  obtain ⟨σ, hσρ, hmass, nH, AH, qH, hH, hLayer⟩ := hkold
  obtain ⟨fine⟩ := hkfine
  let D := cfg.N k ^ (-u * s)
  let a := cfg.N k ^ (-s)
  let A := cfg.N k ^ p.η * a
  let ζ := cfg.N k ^ (-E)
  have ha : 0 < a := Real.rpow_pos_of_pos hNp _
  have hD : 0 < D := Real.rpow_pos_of_pos hNp _
  have hD1 : D ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by nlinarith)
  have hζ : 0 < ζ := Real.rpow_pos_of_pos hNp _
  have hζ1 : ζ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
  have hA1 : A ≤ 1 := by
    dsimp [A, a]
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
  have hAR : cfg.N k ^ (-R) ≤ A := by
    dsimp [A, a]
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith [p.η_pos])
  have hsource : cfg.N k ^ p.ε * a ≤ A :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (hN1 k) p.ε_η) ha.le
  have hDq : D ≤ cfg.timeLength k s ^ 2 := by
    simpa only [fine.grid.depth_zero (hNgt k)] using fine.parameter_small 0
  have hσμ : σ ≤ cfg.μ k := hσρ.trans (hbasic k).2.2.2.2.1
  have hσ0 : σ univ ≠ 0 := ne_of_gt
    ((ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hNp _)).trans_le hmass)
  let c := cfg.prepare_native_comparison fine.parent hbasic (hN1 k) (hK1 k) hκ.le hκ1.le
    hs.le p.ε_pos.le σ hσμ hσ0 (AH 0) (qH 0) (hH 0) (hLayer 0) hkcaps hR hRe' hRe
    hAR hA1 hD hD1 hDq hζ hζ1 hsource hkfit
    (hkmesh s u p.ε E hs.le hsOldMax.le hu0 hu1 p.ε_pos.le hεMax hE.le hEMax)
  have hout := c.comparedLayer_of_power_budgets fine hbasic (hN k) (hK k) hd hd1.le hℓ
    hκ.le hκ1.le hs.le m J hmb hR₀ p rfl rfl rfl rfl hknums hkbig (cfg.ρ k) hσρ hmass
  have hfloor : (cfg.N k ^ (-(θ * s))) ^ (1000 / (1 - cfg.d)) = cfg.N k ^ (-E) := by
    rw [← Real.rpow_mul hNp.le]
    congr 1
    dsimp [E]
    ring
  change Nonempty (ComparedLayer cfg.N cfg.d cfg.e₀ cfg.π cfg.b k (cfg.ρ k) δ D a
    ((cfg.N k ^ (-(θ * s))) ^ (1000 / (1 - cfg.d))))
  rw [hfloor]
  exact hout

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
