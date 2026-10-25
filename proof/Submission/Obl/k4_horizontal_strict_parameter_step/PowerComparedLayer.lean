import Submission.Obl.k4_horizontal_strict_parameter_step.MatchingComparedLayer

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

attribute [local instance] sum_measurableSingletonClass

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- The explicit small powers pay for every matching and selection condition.
Only the prepared original native comparison and fine grid remain as inputs. -/
theorem comparedLayer_of_power_budgets {δ E ε₀ R₀ : ℝ}
    (fine : NativeFinePreparation cfg k s E c.D)
    (hbasic : cfg.Basic) (hN : 2 ≤ cfg.N k) (hK : 3 ≤ cfg.K k)
    (hd : 0 ≤ cfg.d) (hd1 : cfg.d ≤ 1) (hℓ : cfg.ℓ = cfg.κ)
    (hκ : 0 ≤ cfg.κ) (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s)
    (m : MatchingScales cfg.d ε₀) (J : JetData)
    (hmb : MatchBound m.middle ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (p : ComparisonExponents δ s m.size)
    (hε : c.ε = p.ε) (ha : c.a = cfg.N k ^ (-s))
    (hA : c.A = cfg.N k ^ p.η * c.a) (hslopes : c.M = 8 * cfg.K k ^ 4)
    (hnumerics : p.Budgets (cfg.N k) (cfg.K k) cfg.d)
    (hbig : max 4 (max R₀ (max (3 * J.C₂) (budgetMatchingConstant m J))) ≤ cfg.N k ^ p.x)
    (ρ : Measure (α × ℝ)) (hσρ : σ ≤ ρ)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-c.ε)) ≤ σ univ) :
    Nonempty (ComparedLayer cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ρ δ c.D c.a
      (cfg.N k ^ (-E))) := by
  have hNp : 0 < cfg.N k := by linarith
  have hN1 : 1 ≤ cfg.N k := by linarith
  have hKp : 0 < cfg.K k := by linarith
  obtain ⟨hKX, hW, hρ, hfactor, hrow, hM1, hreserve, hcount⟩ := hnumerics
  let X := cfg.N k ^ p.x
  let M := 8 * (cfg.N k ^ p.η * cfg.N k ^ (-s)) * (cfg.N k ^ p.x) ^ m.size
  let cutoff := cfg.N k ^ (-2 * p.x)
  have hcut : 0 < cutoff := Real.rpow_pos_of_pos hNp _
  have hap : 0 < c.a := by rw [ha]; exact Real.rpow_pos_of_pos hNp _
  have hA₀ : 0 < cfg.N k ^ p.η * cfg.N k ^ (-s) := by positivity
  obtain ⟨hAa, hMphysical, hMa, hbadpow⟩ := p.scale_identities hNp
  have hX : 4 ≤ X := (le_max_left _ _).trans hbig
  have hmax₁ : max R₀ (max (3 * J.C₂) (budgetMatchingConstant m J)) ≤ X :=
    (le_max_right _ _).trans hbig
  have hXR : R₀ ≤ X := (le_max_left _ _).trans hmax₁
  have hmax₂ : max (3 * J.C₂) (budgetMatchingConstant m J) ≤ X :=
    (le_max_right _ _).trans hmax₁
  have hXJ : 3 * J.C₂ ≤ X := (le_max_left _ _).trans hmax₂
  have hXB : budgetMatchingConstant m J ≤ X := (le_max_right _ _).trans hmax₂
  have hDq : c.D ≤ cfg.timeLength k s ^ 2 := by
    simpa only [fine.grid.depth_zero (by linarith : 1 < cfg.N k)]
      using fine.parameter_small 0
  have hχq := c.velocity_width.trans hDq
  have hAa' : c.A / cfg.N k ^ (-s) = cfg.N k ^ p.η := by
    simpa only [hA, ha] using hAa
  have hbudget : (∑ i : c.Index, c.comparison.density (c.comparison.colour i)) ≤ X ^ 2 := by
    have hb := c.density_budget fine.parent hbasic hℓ ha hDq hχq
    rw [hAa', hε] at hb
    calc
      _ ≤ (28672 * cfg.K k * (cfg.N k ^ p.η) ^ cfg.d) *
          (cfg.N k ^ p.ε * cfg.K k + 128 * cfg.K k ^ 5) := hb
      _ ≤ cfg.N k ^ p.x * cfg.N k ^ p.x := mul_le_mul hρ hW (by positivity) (by positivity)
      _ = _ := by dsimp [X]; ring
  have hthreshold : M = 2 * c.comparison.error * X ^ m.size := by
    have herr : c.comparison.error = 4 * c.A := rfl
    rw [herr, hA, ha]
    dsimp [M, X]
    ring
  have hAM : c.A ≤ M := by
    have hNX : 1 ≤ cfg.N k ^ p.x := Real.one_le_rpow hN1 p.x_pos.le
    have hNXm : 1 ≤ (cfg.N k ^ p.x) ^ m.size :=
      Real.one_le_rpow hNX (zero_le_one.trans m.size_one)
    have hh := mul_le_mul_of_nonneg_left hNXm (by positivity :
      0 ≤ 8 * (cfg.N k ^ p.η * cfg.N k ^ (-s)))
    rw [hA, ha]
    dsimp [M]
    nlinarith
  have hM1' : 2 * M ≤ 1 := by
    change 2 * (8 * (cfg.N k ^ p.η * cfg.N k ^ (-s)) * (cfg.N k ^ p.x) ^ m.size) ≤ 1
    rw [hMphysical]
    linarith
  have hMa' : M / c.a = 8 * cfg.N k ^ (p.η + p.x * m.size) := by
    simpa only [M, ha] using hMa
  have hfactor' : (100800 * cfg.K k * (M / c.a) ^ cfg.d) / cutoff ≤
      cfg.N k ^ (p.x * (m.size + 3)) := by
    simpa only [hMa', cutoff] using hfactor
  have hW' : (∑ i : c.WitnessIndex, c.witnessWeight i) ≤ cfg.N k ^ p.x := by
    have hw := c.witness_budget fine.parent hbasic hℓ ha hDq hχq
    rw [hε] at hw
    exact hw.trans hW
  have hcutloss : cutoff * (∑ i : c.WitnessIndex, c.witnessWeight i) ≤ cfg.N k ^ (-p.x) := by
    calc
      _ ≤ cfg.N k ^ (-2 * p.x) * cfg.N k ^ p.x := mul_le_mul_of_nonneg_left hW' hcut.le
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hfactorloss : ((100800 * cfg.K k * (M / c.a) ^ cfg.d) / cutoff) * cfg.N k ^ (-δ) ≤
      cfg.N k ^ (p.x * (m.size + 3) - δ) := by
    calc
      _ ≤ cfg.N k ^ (p.x * (m.size + 3)) * cfg.N k ^ (-δ) :=
        mul_le_mul_of_nonneg_right hfactor' (Real.rpow_nonneg hNp.le _)
      _ = _ := by
        simpa only [sub_eq_add_neg] using
          (Real.rpow_add hNp (p.x * (m.size + 3)) (-δ)).symm
  have hreserve' : ((100800 * cfg.K k * (M / c.a) ^ cfg.d) / cutoff) * cfg.N k ^ (-δ) +
      X ^ (-5 : ℝ) + cutoff * (∑ i : c.WitnessIndex, c.witnessWeight i) ≤ cfg.N k ^ (-c.ε) := by
    rw [hε]
    apply le_trans _ hreserve
    apply add_le_add _ hcutloss
    apply add_le_add hfactorloss
    exact hbadpow.le
  have hrow' : 4 * (M / c.a) ≤ cfg.N k ^ δ := by
    rw [hMa']
    convert hrow using 1 <;> ring
  exact c.comparedLayer_of_matching fine hbasic hN hK hd hd1 hℓ hκ hκ1 hs ha hslopes
    (by rw [hε]; exact p.ε_δ) ρ hσρ hmass m J hmb hR₀ hX hXR hXJ hXB hKX
    hbudget hthreshold hAM hM1' hcut hreserve' hrow' hcount

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
