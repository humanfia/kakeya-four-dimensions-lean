import Submission.Obl.k4_matched_pair_representative_realization.Selection.FrozenCharts
import Submission.Obl.k4_matched_pair_representative_realization.Selection.FiniteToSequence
import Submission.Obl.k4_matched_pair_representative_realization.Selection.SelectionSlack
import Submission.Obl.k4_matched_pair_representative_realization.Selection.Retention
import Submission.Obl.k4_matched_pair_representative_realization.Selection.Budgets
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

namespace Submission.Obl.k4_matched_pair_representative_realization

open MeasureTheory Filter
open Submission.Obl.k4_quadratic_atlas_normalization
open Selection

/-- Assemble the three supplied kernels into the original-law representative atlas. -/
theorem realization_from_kernels (hanalytic : AnalyticKernel) (hdisc : DiscSublevel)
    (hsafe : SafePaths) : Realization := by
  classical
  obtain ⟨Cs, hCs, hprob⟩ := safePaths_probability hsafe
  obtain ⟨k⟩ := Selection.AnalyticKernel.binKernel hanalytic Cs hCs
  obtain ⟨CD, hCD, hsublevel⟩ := hdisc Cs hCs
  let C₂ : ℝ := k.CK + 2 * k.CR + CD + 3
  let K : ℝ := 4 + 2 * (3 : ℝ) ^ k.d
  have hC₂ : 0 < C₂ := by dsimp [C₂]; linarith [k.CK_pos, k.CR_pos]
  have hK4 : 4 ≤ K := by
    have : 0 ≤ 2 * (3 : ℝ) ^ k.d := by positivity
    dsimp [K]
    linarith
  have hK1 : 1 ≤ K := by linarith
  apply realization_of_finiteAssembly hC₂ (by norm_num : (0 : ℝ) < 1)
  intro L a h hL ha _ M D Mb Me De
  let Zexp : ℕ := max M (max Mb ⌈h + 1⌉₊)
  let M' : ℕ := max Me (M + 4 * Zexp) + 16
  let D' : ℕ := max De (max D 2)
  have hMZ : M ≤ Zexp := le_max_left _ _
  have hMbZ : Mb ≤ Zexp := (le_max_left _ _).trans (le_max_right _ _)
  have hhZ : h + 1 ≤ (Zexp : ℝ) := by
    exact (Nat.le_ceil (h + 1)).trans (by
      exact_mod_cast (le_max_right Mb ⌈h + 1⌉₊).trans (le_max_right M _))
  refine ⟨M', D', fun ε hε => ?_⟩
  obtain ⟨η, hη, hηε, hη1, Ns, hNs2, hslack⟩ := exists_selection_slack a ε K ha hε
  obtain ⟨Nk, hkernel⟩ := k.at_large a ha M
  obtain ⟨Nd, hsub⟩ := hsublevel a ha
  have hgrowth : ∀ᶠ N : ℝ in atTop, 256 ≤ N ^ a ∧ 2 ≤ N ^ (k.CR * a) :=
    ((tendsto_rpow_atTop ha).eventually_ge_atTop 256).and
      ((tendsto_rpow_atTop (mul_pos k.CR_pos ha)).eventually_ge_atTop 2)
  obtain ⟨Ng, hGrowthAt⟩ := eventually_atTop.mp hgrowth
  let N₀ := max Ns (max Nk (max Nd Ng))
  refine ⟨η, hη, hηε, N₀, hNs2.trans (le_max_left _ _), ?_⟩
  intro N hN₀ W ω ν E B hω hωsum hν hB hE p
  obtain ⟨hNs, hNk, hNd, hNg⟩ : Ns ≤ N ∧ Nk ≤ N ∧ Nd ≤ N ∧ Ng ≤ N := by
    simpa only [N₀, max_le_iff] using hN₀
  have hN2 : 2 ≤ N := hNs2.trans hNs
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hκpos : 0 < p.κ := lt_of_lt_of_le zero_lt_one p.κ_one
  have hδ : 0 < δ N L := by unfold δ; positivity
  obtain ⟨hA, hrel, hKκ⟩ := hslack N p.κ hNs p.κ_one p.κ_upper
  obtain ⟨hlarge, hroot⟩ := hGrowthAt N hNg
  have hCR : N ^ (-(k.CR * a)) ≤ 1 / 2 := by
    rw [Real.rpow_neg hNpos.le]
    exact (inv_anti₀ (by norm_num : (0 : ℝ) < 2) hroot).trans_eq (by norm_num)
  have hgap : 256 * N ^ ((k.CK + 2 * k.CR) * a) ≤ N ^ (C₂ * a) := by
    calc
      _ ≤ N ^ a * N ^ ((k.CK + 2 * k.CR) * a) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hNpos.le _)
      _ = N ^ ((k.CK + 2 * k.CR + 1) * a) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1
        (mul_le_mul_of_nonneg_right (by dsimp [C₂]; linarith) ha.le)
  have hAt := hkernel N (δ N L) ((2 : ℝ) ^ p.T) hNk hδ
    (delta_le_one hN1 hL.le) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  obtain ⟨fp⟩ := p.exists_frozenPairs k hNpos hA hν hω hprob hAt (hsub N hNd)
    (p.nodeEligible k (C₂ * a)) (p.measurableSet_nodeEligible k (C₂ * a))
    (fun θ _ s v hv β r hr hshort =>
      p.lift k hN1 (fun w => (hB w).1) hCR hgap θ s v hv β r hr hshort)
  have hretained := retained_mass_floor hκpos (p.pairMass_finite hν) p.mass_floor fp.mass
    (ENNReal.ofReal_le_ofReal hrel)
    (ENNReal.ofReal_le_ofReal (power_absolute_error_le hNpos hκpos hA hrel))
  have hκout : 1 ≤ K * p.κ := one_le_mul_of_one_le_of_one_le hK1 p.κ_one
  have hcoverage : ENNReal.ofReal (K * p.κ)⁻¹ ≤
      ∑ s, ENNReal.ofReal (ω (p.world s)) * p.incidenceLaw s (fp.F s) := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hretained
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right hK4 hκpos.le)
  have hKn : p.κ * (2 * 3 ^ k.d : ℕ) ≤ K * p.κ := by
    have hn : ((2 * 3 ^ k.d : ℕ) : ℝ) ≤ K := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      dsimp [K]
      linarith
    exact (mul_le_mul_of_nonneg_left hn hκpos.le).trans_eq (mul_comm _ _)
  obtain ⟨hMM', hcoef, hbudA, hbudF⟩ := chart_budgets (Me := Me) hN2 hMZ p.source_count
  have hZM : N ^ M ≤ N ^ Zexp := pow_le_pow_right₀ hN1 hMZ
  have hZT : (2 : ℝ) ^ p.T ≤ N ^ Zexp := by
    apply p.horizon.trans
    have hh : h + η ≤ (Zexp : ℝ) := by linarith
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hN1 hh
  have hBZ (w : Fin W) : 0 < B w ∧ B w ≤ N ^ Zexp :=
    ⟨(hB w).1, (hB w).2.1.trans (pow_le_pow_right₀ hN1 hMbZ)⟩
  have hρD : (K * p.κ * N ^ (C₂ * a))⁻¹ ≤ N ^ (-(CD * a)) := by
    rw [Real.rpow_neg hNpos.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hNpos _)
    calc
      _ ≤ N ^ (C₂ * a) := Real.rpow_le_rpow_of_exponent_le hN1
        (mul_le_mul_of_nonneg_right (by dsimp [C₂]; linarith [k.CK_pos, k.CR_pos]) ha.le)
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hNpos.le _) hκout
  have hr := p.roughAt_of_frozen k fp hN1 hKn hMM' hBZ hZM hZT hcoef hρD
    (fun w => (hE w).1) (fun w i => (hE w).2 i) hbudA hbudF (le_refl D') hcoverage
  exact Selection.RoughBody.roughAt hr hκout hKκ
    (p.horizon.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)))

end Submission.Obl.k4_matched_pair_representative_realization
