-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.LargeAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.SingleTube
import Submission.WZ.Obl.wz_coarse_grains_assembly.CarrierRefinement
import Submission.WZ.Obl.wz_coarse_grains_assembly.LargeRadius
import Submission.WZ.Obl.wz_coarse_grains_assembly.LargeLength
import Submission.WZ.Obl.wz_coarse_grains_assembly.BroadMerge
import Submission.WZ.Obl.wz_coarse_grains_assembly.Double
import Submission.WZ.Obl.wz_tower_balanced_refinement.Arithmetic
import Submission.WZ.Obl.wz_multiscale_finite_tower.MultipleGrids

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory Metric

/-- The large-radius case of the proposed cover assembly, conditional only
on the single-tube grains construction. A constant parameter selection
allows the new coarse cover to consist of one tube at radius one. -/
theorem large_radius_grains (hTG : TubeGrains) {ω ζ ε : ℝ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000)
    (hε : 0 < ε) (hεζ : ε ≤ ζ / 100) :
    ∃ θ d₀ : ℝ, 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V), 0 < n →
        (∀ i, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ I ∧ MeasurableSet (Y i) ∧
          Y i ⊆ T δ (x i) (v i)) → X δ n x v →
        O (δ ^ θ * n * δ ^ 2) ≤ ∑ i, μ (Y i) →
      ∀ (ρ : ℝ), 1 / 2 ≤ ρ → ρ ≤ 1 →
      ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N),
        C δ θ n x v Y S Z ρ N y w f True → Broad ω ζ δ θ ρ n N v S Z f →
        δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n →
        ∃ (S' : Finset (Fin n)) (Z' : Fin n → Set V) (y' w' : V) (c g : ℝ),
          C δ ε n x v Y S' Z' 1 1 (fun _ => y') (fun _ => w') (fun _ => 0) True ∧
          0 < g ∧ Broad ω ζ δ ε 1 n 1 v S' Z' (fun _ => 0) ∧
          H δ ε n x v S' Z' 1 1 (fun _ => y') (fun _ => w') (fun _ => 0) (16*δ) c 0 g ∧
          δ ^ ε * (ρ / δ) * N / n ≤ c := by
  classical
  obtain ⟨η, dG, hη, hdG, hdG100, hG⟩ := single_tube_grains_at_one hTG hω hζ
    (by positivity : 0 < ζ / 2) (by positivity : 0 < ε / 8)
  obtain ⟨K, hK, hcarrier⟩ := exists_uniform_carrier_refinement
  let θ := min (η / 10) (ε / 100)
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθη : θ ≤ η / 10 := min_le_left _ _
  have hθε : θ ≤ ε / 100 := min_le_right _ _
  let D : ℝ := max ((K : ℝ) ^ 2) 16000000000002
  obtain ⟨dB, hdB, _, hB⟩ :=
    WangZahlLot.Obl.wz_terminal_grains_restoration.const_le_rpow_neg hθ D
  refine ⟨θ, min dG dB, hθ, by linarith, lt_min hdG hdB,
    (min_le_left _ _).trans hdG100, ?_⟩
  intro δ hδ hδd n x v Y hn hY hX hmass ρ hρhalf hρ1 S Z N y w f hC hbr hreg
  have hδ100 : δ ≤ 1 / 100 := (hδd.trans (min_le_left _ _)).trans hdG100
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hρ : 0 < ρ := by linarith
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hbudget : D ≤ δ ^ (-θ) := hB δ hδ (hδd.trans (min_le_right _ _))
  have hK2 : (K : ℝ) ^ 2 ≤ δ ^ (-θ) := (le_max_left _ _).trans hbudget
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpow : (K : ℝ) ≤ δ ^ (-θ) := (show (K : ℝ) ≤ (K : ℝ) ^ 2 by nlinarith).trans hK2
  have hfixed : (16000000000002 : ℝ) ≤ δ ^ (-θ) := (le_max_right _ _).trans hbudget
  have htwo : (2 : ℝ) ≤ δ ^ (-θ) := (by norm_num : (2 : ℝ) ≤ 16000000000002).trans hfixed
  have hN : (N : ℝ) ≤ δ ^ (-θ) :=
    (coarse_card_large_radius hδ hρhalf hρ1 hn hmass (fun i => (hY i).2.1) hC).trans
      ((by norm_num : (16000000000000 : ℝ) ≤ 16000000000002).trans hfixed)
  obtain ⟨F', W, yp, wp, hwp, hW, hFT, hWmass, hWfrac⟩ :=
    hcarrier δ hδ hδ100 n x v Z (fun i => ⟨(hY i).1, (hY i).2.1⟩)
      (fun i => (hC.1 i).1)
  have hZsum : (∑ i ∈ S, μ (Z i)) = ∑ i, μ (Z i) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    rw [(hC.1 i).2.2 hi]
    exact measure_empty
  have hWsum : (∑ i ∈ F', μ (W i)) = ∑ i, μ (W i) := by
    apply Finset.sum_subset (Finset.subset_univ F')
    intro i _ hi
    rw [(hW i).2.2 hi]
    exact measure_empty
  have hsmall : δ ^ θ * (K : ℝ) ^ 2 ≤ 1 := by
    have hh := rpow_absorb hδ hδ1 hK2 (a := θ) (b := 0) (by linarith)
    simpa only [Real.rpow_zero, mul_comm] using hh
  have hcol : O (δ ^ θ) * ∑ i, μ (Z i) ≤ ∑ i ∈ F', μ (W i) := by
    have hh := WangZahlLot.Obl.wz_tower_balanced_refinement.retained_mass
      (ε := 2 * θ) (B := 1) (J := 1) hδ hK le_rfl
      (by simpa only [show 2 * θ / 2 = θ by ring] using hsmall) hWmass
    simpa only [show 2 * θ / 2 = θ by ring] using hh
  have hret : O (δ ^ (2 * θ)) * ∑ i, μ (Y i) ≤ ∑ i ∈ F', μ (W i) := by
    have he : O (δ ^ (2 * θ)) = O (δ ^ θ) * O (δ ^ θ) := by
      have heq : δ ^ (2 * θ) = δ ^ θ * δ ^ θ := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      rw [heq]
      exact ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le θ)
    rw [he, mul_assoc]
    exact (mul_le_mul' le_rfl (show O (δ ^ θ) * ∑ i, μ (Y i) ≤ ∑ i, μ (Z i) by
      simpa only [hZsum] using hC.2.1)).trans hcol
  have hden := WangZahlLot.Obl.wz_multiscale_finite_tower.shading_density_of_mass_retention
    hδ hmass (show O (δ ^ (2 * θ)) * ∑ i, μ (Y i) ≤ ∑ i, μ (W i) by
      simpa only [hWsum] using hret)
  have hFne : F'.Nonempty := by
    by_contra hnF
    have he := Finset.not_nonempty_iff_eq_empty.mp hnF
    rw [← hWsum, he, Finset.sum_empty] at hden
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) hden
  have hFcard : F'.card ≤ n := by simpa using Finset.card_le_univ F'
  have hdenTG : O (δ ^ η * F'.card * δ ^ 2) ≤ ∑ i ∈ F', μ (W i) := by
    calc
      _ ≤ O (δ ^ (θ + 2 * θ) * n * δ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hp : δ ^ η ≤ δ ^ (θ + 2 * θ) :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hp (Nat.cast_le.mpr hFcard) (Nat.cast_nonneg _) (Real.rpow_nonneg hδ.le _))
          (sq_nonneg δ)
      _ ≤ _ := by simpa only [hWsum] using hden
  have hb1 : Broad ω ζ δ (2 * θ) 1 n N v S Z f :=
    broad_enlarge hδ hω hω1 hζ (by linarith) hρ hρ1 (by linarith)
      (rpow_absorb hδ hδ1 htwo (by linarith))
      (htwo.trans (rpow_err_le hδ hδ1 (by linarith : θ ≤ 2 * θ)).2) hbr
  have hbGlobal := broad_forget_cover (fun i => (hC.1 i).2.2) hb1
  have hWmem (p : V) (i : Fin n) (hi : p ∈ W i) : i ∈ F' := by
    by_contra hnF
    rw [(hW i).2.2 hnF] at hi
    exact hi
  have hWeq (p : V) : {i | i ∈ F' ∧ p ∈ W i} = {i | p ∈ W i} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    exact ⟨And.right, fun hi => ⟨hWmem p i hi, hi⟩⟩
  have hfrac : ∀ p, (∃ i, p ∈ W i) → q n {i | p ∈ Z i} ≤ K * q n {i | p ∈ W i} := by
    rintro p ⟨i, hi⟩
    simpa only [hWeq] using hWfrac p ⟨i, hWmem p i hi, hi⟩
  have hbW := broad_of_pointwise_fraction hδ.le zero_lt_one
    (Real.rpow_nonneg hδ.le _) (fun i => (hW i).2.1) hfrac hbGlobal
  have hcoeff : (K : ℝ) * δ ^ (-(2 * θ)) ≤ δ ^ (-η) :=
    rpow_absorb hδ hδ1 hKpow (by linarith)
  have hbTG : ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ 1 →
      q n {i | p ∈ W i ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ≤
        δ ^ (-η) * r ^ (ω * ζ / 100) * q n {i | p ∈ W i} := by
    intro p u r hu hdr hr1
    have hh := hbW p u r hu hdr hr1
    simp only [div_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (hδ.le.trans hdr) _))
      (Nat.cast_nonneg _))
  obtain ⟨_, hnew⟩ := hG δ hδ (hδd.trans (min_le_left _ _)) n x v W F' yp wp hFne hwp
    (fun i hi => ⟨(hY i).1, hFT i hi, (hW i).1,
      (hW i).2.1.trans ((hC.1 i).2.1.trans (hY i).2.2.2)⟩)
    (fun i => (hW i).2.2) hX hdenTG hbTG
  let c := δ ^ (ε / 2) / (δ * n)
  obtain ⟨hclo, hlen⟩ := large_radius_prescribed_length (ε := ε) (ζ := ζ) hδ hδ1 hρ hρ1 hn hN
    (by linarith) (by linarith) hreg
  have hchi : c ≤ δ ^ (ε / 8) * (1 / δ) / F'.card :=
    prescribed_length_le_single_tube hδ hδ1 hFne.card_pos hFcard (by linarith)
  have hwidth : 16 * δ ≤ c := by
    have h16 : (16 : ℝ) ≤ δ ^ (-θ) := (by norm_num : (16 : ℝ) ≤ 16000000000002).trans hfixed
    have hh := rpow_absorb hδ hδ1 h16 (a := 1) (b := 1 - ζ / 2) (by linarith)
    have hh' : 16 * δ ≤ δ ^ (1 - ζ / 2) := by simpa only [Real.rpow_one] using hh
    exact hh'.trans hclo
  obtain ⟨U, g, hg, hU, hUret, hbU, hHU⟩ := hnew c hclo hchi hwidth
  have hfinalret : O (δ ^ ε) * ∑ i, μ (Y i) ≤ ∑ i ∈ F', μ (U i) := by
    calc
      _ ≤ O (δ ^ (ε / 8 + 2 * θ)) * ∑ i, μ (Y i) := by
        apply mul_le_mul' _ le_rfl
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = O (δ ^ (ε / 8)) * (O (δ ^ (2 * θ)) * ∑ i, μ (Y i)) := by
        simp only [O, Real.rpow_add hδ,
          ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le (ε / 8)), mul_assoc]
      _ ≤ O (δ ^ (ε / 8)) * ∑ i ∈ F', μ (W i) := mul_le_mul' le_rfl hret
      _ ≤ _ := hUret
  refine ⟨F', U, yp, wp, c, g, ?_, hg,
    Broad_mono hδ hδ1 (by linarith) hbU, H_mono hδ hδ1 (by linarith) hHU, hlen⟩
  refine singleton_unit_cover hδ hδ1 hε.le ?_ hfinalret hwp ?_
  · exact fun i => ⟨(hU i).1, (hU i).2.1.trans ((hW i).2.1.trans (hC.1 i).2.1), (hU i).2.2⟩
  · exact fun i hi => (hFT i hi).trans (thickening_mono (by norm_num) _)

end WangZahlLot.Obl.wz_coarse_grains_assembly
