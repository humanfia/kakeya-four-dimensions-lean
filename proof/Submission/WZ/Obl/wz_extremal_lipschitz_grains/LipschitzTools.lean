-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.LipschitzTools.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzCounting
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.PlaneGeometry
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.ParityCubes
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.StrongPlaneMap

/-!
# Tools for the Lipschitz plane map

Per-cube selection of heavy parts (`measure_iUnion_select`), cells of side `r` covering a ball
(`exists_cells_cover`), stability of unoriented direction separation (`min_sep_triangle`), and
the normal cap at a point carrying a transverse coarse pair (`cap_of_pair`).
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

theorem iUnion_gridCube_eq_univ {s : ℝ} (hs : 0 < s) : (⋃ m, gridCube s m) = univ :=
  eq_univ_of_forall fun p => mem_iUnion.2 ⟨_, mem_gridCube_cubeIndex hs p⟩

/-- Choosing in every grid cube a measurable part carrying a fraction `c` of the cube's share of
`E` gives a set carrying the fraction `c` of `E`. -/
theorem measure_iUnion_select (ν : Measure Space) {s : ℝ} (hs : 0 < s) (E : Set Space)
    (hE : MeasurableSet E) (K : (Fin 3 → ℤ) → Set Space) (hKm : ∀ m, MeasurableSet (K m))
    (hKsub : ∀ m, K m ⊆ gridCube s m) (c : ℝ≥0∞)
    (hK : ∀ m, c * ν (E ∩ gridCube s m) ≤ ν (K m)) :
    c * ν E ≤ ν (⋃ m, K m) := by
  have hdisjQ : Pairwise (Function.onFun Disjoint (gridCube s)) :=
    fun m m' h => gridCube_disjoint hs h
  have hdisjK : Pairwise (Function.onFun Disjoint K) :=
    fun m m' h => (hdisjQ h).mono (hKsub m) (hKsub m')
  have hE' : ν E = ∑' m, ν (E ∩ gridCube s m) := by
    rw [← measure_iUnion (fun m m' h => (hdisjQ h).mono inter_subset_right inter_subset_right)
      (fun m => hE.inter (measurableSet_gridCube s m)), ← inter_iUnion,
      iUnion_gridCube_eq_univ hs, inter_univ]
  rw [hE', measure_iUnion hdisjK hKm, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hK


theorem abs_apply_sub_le_dist (p q : Space) (j : Fin 3) : |p j - q j| ≤ dist p q := by
  rw [← Real.dist_eq, EuclideanSpace.dist_eq]
  calc dist (p j) (q j) = Real.sqrt (dist (p j) (q j) ^ 2) := by rw [Real.sqrt_sq dist_nonneg]
    _ ≤ Real.sqrt (∑ i, dist (p i) (q i) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => dist (p i) (q i) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j))

/-- Finitely many cells of side `r` cover a closed ball of radius `R`. -/
theorem exists_cells_cover (N : Space) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ S : Finset (Fin 3 → ℤ), S.card ≤ (⌊2 * R / r⌋₊ + 3) ^ 3 ∧
      ∀ q, dist q N ≤ R → cubeIndex r q ∈ S := by
  classical
  refine ⟨Fintype.piFinset fun j => Finset.Icc ⌊(N j - R) / r⌋ ⌊(N j + R) / r⌋, ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    calc ∏ i, (Finset.Icc ⌊(N i - R) / r⌋ ⌊(N i + R) / r⌋).card
        ≤ (⌊2 * R / r⌋₊ + 3) ^ (Finset.univ : Finset (Fin 3)).card := by
          apply Finset.prod_le_pow_card
          intro i _
          rw [Int.card_Icc]
          have h1 := Int.floor_le ((N i + R) / r)
          have h2 := Int.lt_floor_add_one ((N i - R) / r)
          have h3 := Nat.lt_floor_add_one (2 * R / r)
          have hdiff : (N i + R) / r - (N i - R) / r = 2 * R / r := by ring
          have hlt : ((⌊(N i + R) / r⌋ - ⌊(N i - R) / r⌋ : ℤ) : ℝ) < (⌊2 * R / r⌋₊ : ℝ) + 2 := by
            push_cast; linarith
          have hlt' : ⌊(N i + R) / r⌋ - ⌊(N i - R) / r⌋ < (⌊2 * R / r⌋₊ : ℤ) + 2 := by
            exact_mod_cast hlt
          omega
      _ = (⌊2 * R / r⌋₊ + 3) ^ 3 := by rw [Finset.card_univ, Fintype.card_fin]
  · intro q hq
    rw [Fintype.mem_piFinset]
    intro j
    have h := (abs_apply_sub_le_dist q N j).trans hq
    rw [abs_le] at h
    rw [Finset.mem_Icc]
    constructor
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hr.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hr.le)


theorem min_sep_triangle {u u' v v' : Space} {d β : ℝ}
    (hu : min ‖u - v‖ ‖u + v‖ ≤ d) (hu' : min ‖u' - v'‖ ‖u' + v'‖ ≤ d)
    (hvv : β < min ‖v - v'‖ ‖v + v'‖) : β - 2 * d ≤ min ‖u - u'‖ ‖u + u'‖ := by
  -- every sign combination
  have key : ∀ σ τ : ℝ, |σ| = 1 → |τ| = 1 → ‖u - σ • v‖ ≤ d → ‖u' - τ • v'‖ ≤ d →
      β - 2 * d ≤ min ‖u - u'‖ ‖u + u'‖ := by
    intro σ τ hσ hτ h1 h2
    have hv' : ∀ ε : ℝ, |ε| = 1 → β < ‖v - ε • v'‖ := by
      intro ε hε
      rcases abs_eq (zero_le_one) |>.1 hε with h | h
      · rw [h, one_smul]; exact lt_of_lt_of_le hvv (min_le_left _ _)
      · rw [h, neg_one_smul, sub_neg_eq_add]; exact lt_of_lt_of_le hvv (min_le_right _ _)
    have hsep : ∀ ε : ℝ, |ε| = 1 → β - 2 * d ≤ ‖u - ε • u'‖ := by
      intro ε hε
      have hεστ : |σ * ε * τ| = 1 := by rw [abs_mul, abs_mul, hσ, hε, hτ]; norm_num
      have h3 := hv' (σ * ε * τ) hεστ
      -- `v - (σ ε τ) v' = σ (σ v - ε τ v')` up to sign
      have hσσ : σ * σ = 1 := by
        rcases abs_eq (zero_le_one) |>.1 hσ with h | h <;> rw [h] <;> norm_num
      have he : v - (σ * ε * τ) • v' = σ • ((σ • v - u) + (u - ε • u') + ε • (u' - τ • v')) := by
        rw [smul_add, smul_add, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, hσσ, one_smul,
          smul_sub, smul_smul, mul_assoc]
        abel
      rw [he, norm_smul, Real.norm_eq_abs, hσ, one_mul] at h3
      have h4 : ‖(σ • v - u) + (u - ε • u') + ε • (u' - τ • v')‖ ≤
          ‖u - σ • v‖ + ‖u - ε • u'‖ + ‖u' - τ • v'‖ := by
        calc _ ≤ ‖(σ • v - u) + (u - ε • u')‖ + ‖ε • (u' - τ • v')‖ := norm_add_le _ _
          _ ≤ ‖σ • v - u‖ + ‖u - ε • u'‖ + ‖ε • (u' - τ • v')‖ := by gcongr; exact norm_add_le _ _
          _ = ‖u - σ • v‖ + ‖u - ε • u'‖ + ‖u' - τ • v'‖ := by
              rw [norm_sub_rev, norm_smul, Real.norm_eq_abs, hε, one_mul]
      linarith
    exact le_min (by simpa using hsep 1 (by norm_num))
      (by simpa [sub_neg_eq_add] using hsep (-1) (by norm_num))
  rcases le_total ‖u - v‖ ‖u + v‖ with h1 | h1 <;> rcases le_total ‖u' - v'‖ ‖u' + v'‖ with h2 | h2
  · exact key 1 1 (by norm_num) (by norm_num) (by simpa [min_eq_left h1] using hu)
      (by simpa [min_eq_left h2] using hu')
  · exact key 1 (-1) (by norm_num) (by norm_num) (by simpa [min_eq_left h1] using hu)
      (by simpa [min_eq_right h2, sub_neg_eq_add] using hu')
  · exact key (-1) 1 (by norm_num) (by norm_num) (by simpa [min_eq_right h1, sub_neg_eq_add] using hu)
      (by simpa [min_eq_left h2] using hu')
  · exact key (-1) (-1) (by norm_num) (by norm_num)
      (by simpa [min_eq_right h1, sub_neg_eq_add] using hu)
      (by simpa [min_eq_right h2, sub_neg_eq_add] using hu')


/-- At a point carrying two transverse tubes with coarse directions `w, w'`, a plane map of
precision `e₀` is close (up to sign) to the normal of `w, w'`. -/
theorem cap_of_pair {V v v' w w' : Space} (hV : ‖V‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) {e₀ d₀ β : ℝ} (hβ : 2 * d₀ < β)
    (hVv : |inner ℝ v V| ≤ e₀) (hVv' : |inner ℝ v' V| ≤ e₀)
    (hwv : min ‖w - v‖ ‖w + v‖ ≤ d₀) (hwv' : min ‖w' - v'‖ ‖w' + v'‖ ≤ d₀)
    (hvv : β < min ‖v - v'‖ ‖v + v'‖) :
    min ‖V - ‖cross w w'‖⁻¹ • cross w w'‖ ‖V + ‖cross w w'‖⁻¹ • cross w w'‖ ≤
      4 * (e₀ + d₀) / ((β - 2 * d₀) / 2) := by
  have hsep := min_sep_triangle hwv hwv' hvv
  have hcross := cross_norm_lower hw hw' (by linarith) hsep
  have hVw : |inner ℝ V w| ≤ e₀ + d₀ := by
    rw [real_inner_comm]
    exact (abs_inner_le_of_dir hV).trans (add_le_add hVv hwv)
  have hVw' : |inner ℝ V w'| ≤ e₀ + d₀ := by
    rw [real_inner_comm]
    exact (abs_inner_le_of_dir hV).trans (add_le_add hVv' hwv')
  exact near_normal_of_two hw hw' hV (by linarith) hcross hVw hVw'

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
