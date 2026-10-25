import Submission.Obl.k4_pair_bin_atlas_assembly.FiniteToSequence
import Submission.Obl.k4_pair_bin_atlas_assembly.FrozenCharts
import Submission.Obl.k4_pair_bin_atlas_assembly.FrozenMass
import Submission.Obl.k4_pair_bin_atlas_assembly.PowerBudgets
import Submission.Obl.k4_pair_bin_atlas_assembly.SelectionSlack
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_quadratic_atlas_normalization (fmt δ)

/-- All per-resolution selections and geometric charts have format bounds
fixed before the requested cofinal slack. -/
theorem finiteAssembly {Cs : ℕ} (k : BinKernel Cs) {CD C₂ c₂ : ℝ}
    (hCD : CD ≤ C₂) (hfit : k.CK + 2 * k.CR < C₂)
    (hsafe : SafeProbability Cs)
    (hsub : ∀ a : ℝ, 0 < a → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → SublevelAt Cs CD N a) :
    FiniteAssembly C₂ c₂ := by
  intro L a h hL ha haL M D Mb Me De
  obtain ⟨H : ℕ, hH⟩ := exists_nat_ge (h + 1)
  let K : ℕ := M + Mb + H
  let M' : ℕ := 2 * M + Me + 4 * K + 16
  let D' : ℕ := max De (max D 2)
  have hMK : M ≤ K := by dsimp [K]; omega
  have hMbK : Mb ≤ K := by dsimp [K]; omega
  have hHK : h + 1 ≤ (K : ℝ) := by
    apply hH.trans
    exact_mod_cast (show H ≤ K by dsimp [K]; omega)
  have hMM' : M ≤ M' := by dsimp [M']; omega
  have hcoefM : M + 4 * K + 12 ≤ M' := by dsimp [M']; omega
  have hformatM : 2 * M + Me + 5 ≤ M' := by dsimp [M']; omega
  refine ⟨M', D', ?_⟩
  intro ε hε
  let Kn : ℕ := 2 * 3 ^ k.d
  let C : ℝ := max 4 (Kn : ℝ)
  have hC4 : 4 ≤ C := le_max_left _ _
  have hKnC : (Kn : ℝ) ≤ C := le_max_right _ _
  obtain ⟨η, hη, hηε, hη1, Nsel, hNsel, hselection⟩ := exists_selection_slack a ε C ha hε
  obtain ⟨Nint, hNint, hinterpolation⟩ := exists_interpolation_scale ha k.CR_pos hfit
  obtain ⟨Nker, hkernel⟩ := k.at_large a ha M
  obtain ⟨Nsub, hsublevel⟩ := hsub a ha
  let N₀ : ℝ := max Nsel (max Nint (max Nker Nsub))
  have hN₀ : 2 ≤ N₀ := hNsel.trans (le_max_left _ _)
  refine ⟨η, hη, hηε, N₀, hN₀, ?_⟩
  intro Nk hNk Wk ωk νk Ek Bk hω hωsum hν hB hE p
  have hNk2 : 2 ≤ Nk := hN₀.trans hNk
  have hNk1 : 1 ≤ Nk := by linarith
  have hNk0 : 0 < Nk := by linarith
  have hNselk : Nsel ≤ Nk := (le_max_left _ _).trans hNk
  have hNintk : Nint ≤ Nk := (le_max_left _ _).trans ((le_max_right _ _).trans hNk)
  have hNkerk : Nker ≤ Nk := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hNk))
  have hNsubk : Nsub ≤ Nk := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hNk))
  obtain ⟨hA, hrel, hκupper⟩ := hselection Nk p.κ hNselk p.κ_one p.κ_upper
  obtain ⟨hCR, hgap⟩ := hinterpolation Nk hNintk
  have hδpos : 0 < δ Nk L := by unfold δ; positivity
  have hδone : δ Nk L ≤ 1 :=
    Submission.Obl.k4_quadratic_atlas_normalization.delta_le_one hNk1 hL.le
  have hq : (1 : ℝ) ≤ 2 ^ p.T := one_le_pow₀ (by norm_num)
  obtain ⟨fp⟩ := p.exists_frozenPairs k hNk0 hA hν hω hsafe
    (hkernel Nk (δ Nk L) ((2 : ℝ) ^ p.T) hNkerk hδpos hδone hq)
    (hsublevel Nk hNsubk) (p.nodeEligible k (C₂ * a)) (p.measurableSet_nodeEligible k _)
    (fun θ hθ s v hv β r hr hb => p.lift k hNk1 (fun w => (hB w).1) hCR hgap θ s v hv β r hr hb)
  have hκpos : 0 < p.κ := lt_of_lt_of_le zero_lt_one p.κ_one
  have hC1 : 1 ≤ C := by linarith
  have hκnew : 1 ≤ C * p.κ := one_le_mul_of_one_le_of_one_le hC1 p.κ_one
  have hKn : p.κ * (2 * 3 ^ k.d : ℕ) ≤ C * p.κ := by
    calc _ ≤ p.κ * C := mul_le_mul_of_nonneg_left hKnC hκpos.le
      _ = _ := mul_comm _ _
  have hZM : Nk ^ M ≤ Nk ^ K := pow_le_pow_right₀ hNk1 hMK
  have hZT : (2 : ℝ) ^ p.T ≤ Nk ^ K := p.horizon.trans (by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith))
  have hBZ : ∀ w, 0 < Bk w ∧ Bk w ≤ Nk ^ K := fun w =>
    ⟨(hB w).1, (hB w).2.1.trans (pow_le_pow_right₀ hNk1 hMbK)⟩
  have hcoef : 81 * Nk ^ M * (6 * (Nk ^ K) ^ 2) ^ 2 ≤ Nk ^ M' :=
    (physical_coefficient_budget hNk2 M K).trans (pow_le_pow_right₀ hNk1 hcoefM)
  have hbudF : Nk ^ Me + (((p.m : ℝ) * Nk ^ M + 14) + (2 + (p.m : ℝ) * Nk ^ M)) ≤ Nk ^ M' :=
    (chart_format_budget hNk2 M Me p.source_count).trans (pow_le_pow_right₀ hNk1 hformatM)
  have hbudA : (p.m : ℝ) * Nk ^ M + 14 ≤ Nk ^ M' := by
    have hnonneg : 0 ≤ Nk ^ Me + (2 + (p.m : ℝ) * Nk ^ M) := by positivity
    linarith
  have hden : Nk ^ (CD * a) ≤ (C * p.κ) * Nk ^ (C₂ * a) := by
    calc
      _ ≤ Nk ^ (C₂ * a) := Real.rpow_le_rpow_of_exponent_le hNk1 (by nlinarith)
      _ = 1 * Nk ^ (C₂ * a) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hκnew (by positivity)
  have hρD : ((C * p.κ) * Nk ^ (C₂ * a))⁻¹ ≤ Nk ^ (-(CD * a)) := by
    rw [Real.rpow_neg hNk0.le]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNk0 _) hden
  have hm := fp.mass_floor_enlarged hν hNk0 hA hrel hC4
  obtain ⟨nc, γ, j, c, u, Q, R, A, F, lst, hcount, hdisj, hlst, hrough, hmass⟩ :=
    p.roughAt_of_frozen k fp hNk1 hKn hMM' hBZ hZM hZT hcoef hρD
      (fun w => (hE w).1) (fun w => (hE w).2) hbudA hbudF (le_refl D') hm
  refine ⟨C * p.κ, hκnew, hκupper, p.T, nc, γ, j, c, u, Q, R, A, F, lst, ?_,
    hcount, hdisj, hlst, hrough, hmass⟩
  exact p.horizon.trans (Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith))

end Submission.Obl.k4_pair_bin_atlas_assembly
