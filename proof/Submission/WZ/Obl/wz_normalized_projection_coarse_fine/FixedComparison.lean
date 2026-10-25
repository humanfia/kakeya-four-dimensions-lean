-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.FixedComparison.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.AssemblyArithmetic
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.CoarseClassMass
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.SmallIteration

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_normalized_projection_iteration (Family Frostman Slope Projection)
open scoped ENNReal

noncomputable section

/-- Assemble the geometric partition, common scale selection, and light-class estimates.
All small-scale numerical requirements are supplied by `ComparisonBudget`. -/
theorem comparison_from_budget {δ ε κ η s e vloss t P ηC dC : ℝ} {q : ℕ}
    (hδ : 0 < δ) (hε : 0 < ε) (hvLoss : 0 < vloss) (hq : 0 < q)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (he : ε / 2 ≤ 3 * s - 3 + ε - 2 * e)
    (hbudget : ComparisonBudget δ ε κ η s vloss t P ηC dC q)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hH : Family η δ n x v Y) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hFrostman : Frostman η δ n x v) (hpack : (n : ℝ) * δ ^ 6 ≤ P)
    {f : ℝ → ℝ} (hf : Slope f) (hf0 : |f 0| ≤ 1)
    (hC : ∀ τ : ℝ, 0 < τ → τ ≤ dC → τ ≤ 1 / 100 → CinematicMomentAt τ ηC e f) :
    ∃ ρ : ℝ, δ ^ (1 - ε ^ 2) < ρ ∧ ρ < 1 ∧
      ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧
        ENNReal.ofReal (δ ^ κ * n * δ ^ 2) ≤ ∑ i, volume (Z i) ∧
        ENNReal.ofReal ((δ / ρ) ^ ε) * volume (thickening ρ (Projection f (⋃ i, Z i))) ≤
          volume (Projection f (⋃ i, Z i)) := by
  classical
  obtain ⟨hn, hv, hball, hsep, hYmeas, hYtube, hmass⟩ := hH
  have hδ1 : δ ≤ 1 := by linarith [hbudget.small]
  have hδlt1 : δ < 1 := by linarith [hbudget.small]
  obtain ⟨L, hL3, hwidth, hwidth'⟩ := exists_dyadic_strip_scale hδ hbudget.small
  have hδL : δ ≤ ((2 : ℝ) ^ L)⁻¹ := by linarith
  obtain ⟨F, hF, hdisj, hrem⟩ := global_coarse_partition hδ hδ1 hn hL3 x v hv htrans hball
    hFrostman hδL hs (hs1.trans (by norm_num)) hbudget.root
  have hYbound (i : Fin n) : volume (Y i) ≤ ENNReal.ofReal (56 * δ ^ 2) :=
    (measure_mono (hYtube i)).trans (tube_volume_upper hδ.le hδ1 (x i) (v i) (hv i))
  have hYfinite (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hYbound i)
  have hremain := residual_weight_bound hδ (fun i => volume (Y i)) hYbound
    (Finset.univ \ F.biUnion id) hrem hbudget.residual
  have hkeep := retained_class_mass F hdisj (fun i => volume (Y i)) hYfinite hmass hremain
  let C : Finset (Fin n) → ℕ → Prop := fun Q j =>
    3 ≤ j ∧ δ ^ (1 - ε ^ 2) < ((2 : ℝ) ^ j)⁻¹ ∧
      ∃ c : ℝ, |c| ≤ 3 ∧ (∀ i ∈ Q, |slope (v i) 0 - c| ≤ δ) ∧
        ∃ i₀ ∈ Q, (∀ i ∈ Q, dyadicLabel j (parameters (x i) (v i)) =
          dyadicLabel j (parameters (x i₀) (v i₀))) ∧
          ∀ k, j ≤ k → k ≤ L → ∀ l : Fin 3 → ℤ,
            ((Q.filter (fun i => dyadicLabel k (parameters (x i) (v i)) = l)).card : ℝ) ≤
              (Q.card : ℝ) * ((((2 : ℝ) ^ k)⁻¹ / ((2 : ℝ) ^ j)⁻¹) ^ s)
  have hClevel : ∀ Q ∈ F, ∃ j, j ≤ L ∧ C Q j := by
    intro Q hQ
    obtain ⟨_, c, hc, hthin, j, hj3, hjL, hcoarse, i₀, hi₀, hcell, hcount⟩ := hF Q hQ
    exact ⟨j, hjL, hj3, hcoarse, c, hc, hthin, i₀, hi₀, hcell, hcount⟩
  obtain ⟨j, hjL, G, hGF, hGclass, hcolor⟩ := weighted_level_selection F
    (fun Q => ∑ i ∈ Q, volume (Y i)) L C hClevel
  have hselected : ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤
      (2 * (L + 1 : ℝ≥0∞)) * ∑ Q ∈ G, ∑ i ∈ Q, volume (Y i) := by
    calc
      _ ≤ 2 * ∑ Q ∈ F, ∑ i ∈ Q, volume (Y i) := hkeep
      _ ≤ 2 * ((L + 1 : ℝ≥0∞) * ∑ Q ∈ G, ∑ i ∈ Q, volume (Y i)) :=
        mul_le_mul' le_rfl hcolor
      _ = _ := by ring
  have hGne : G.Nonempty := by
    by_contra hh
    have hG0 : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    have hpos : 0 < ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
      apply ENNReal.ofReal_pos.mpr
      have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      positivity
    exact (not_le_of_gt hpos) (by
      simpa only [hG0, Finset.sum_empty, mul_zero] using hselected)
  obtain ⟨Q₀, hQ₀⟩ := hGne
  have hj3 := (hGclass Q₀ hQ₀).1
  have hcoarse := (hGclass Q₀ hQ₀).2.1
  have hGdisj : (G : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro Q hQ Q' hQ' hne
    exact hdisj (hGF hQ) (hGF hQ') hne
  let ρ := 2 * ((2 : ℝ) ^ j)⁻¹
  let τ := ((2 : ℝ) ^ (L - j + 1))⁻¹
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hρcoarse : δ ^ (1 - ε ^ 2) < ρ := by
    dsimp [ρ]
    nlinarith [show (0 : ℝ) < ((2 : ℝ) ^ j)⁻¹ by positivity]
  have hρ1 : ρ < 1 := by
    have hh := (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj3)
    norm_num at hh
    dsimp [ρ]
    linarith
  have hρτ : ρ * τ = ((2 : ℝ) ^ L)⁻¹ := (relative_dyadic_scale hjL).symm
  have hupper : ρ * τ ≤ 26 * δ := by rw [hρτ]; exact hwidth'.le
  have hlower : δ ≤ ρ * τ := by rw [hρτ]; exact hδL
  have hτscale := relative_scale_bound hδ hτ hρcoarse.le hupper hbudget.ratio
  obtain ⟨hτC, hτ100, hητ⟩ := hbudget.relative τ hτ hτscale
  have hτ1 : τ ≤ 1 := hτ100.trans (by norm_num)
  have hR : 1 < δ ^ (-vloss) := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt hδ hδlt1 (show -vloss < 0 by linarith)
    simpa only [Real.rpow_zero] using hh
  have hbins := hbudget.size n hpack
  have hbudgets := hbudget.level L hδL
  refine ⟨ρ, hρcoarse, hρ1, ?_⟩
  apply disjoint_light_refinement hf.1.continuous Y hYmeas hYfinite G hGdisj hρ
    (show 0 ≤ δ ^ t * δ ^ 2 by positivity) (ENNReal.ofReal ((δ / ρ) ^ ε))
    (ENNReal.ofReal (δ ^ η * n * δ ^ 2)) (ENNReal.ofReal (δ ^ κ * n * δ ^ 2)) hselected
  · convert cast_mass_budget hδ hbudgets.1 (n := n) using 1 <;> congr 2 <;> ring
  · exact cast_mass_budget hδ hbudgets.2
  · intro A hA hlight Q hQ
    obtain ⟨_, _, c, hc, hthin, i₀, hi₀, hcell, hcount⟩ := hGclass Q hQ
    have hQsize : 2 * (Q.card : ℝ) < (δ ^ (-vloss)) ^ q := by
      have hh : (Q.card : ℝ) ≤ n := by
        exact_mod_cast (show Q.card ≤ n by simpa using Finset.card_le_card (Finset.subset_univ Q))
      linarith
    have hX : ∀ i ∈ Q, projection f '' Y i ⊆
        projection f '' (⋃ i, restrictShading (G.biUnion id) Y i) := by
      intro i hi
      apply image_mono
      intro z hz
      apply mem_iUnion_of_mem i
      have hiG : i ∈ G.biUnion id := Finset.mem_biUnion.mpr ⟨Q, hQ, hi⟩
      simpa only [restrictShading, if_pos hiG] using hz
    have hm := coarse_cell_light_mass hδ hj3 hjL hwidth x v Y Q i₀ hi₀ hv htrans hball
      (fun i _ => hYtube i) hc hthin hcell hs hs1 hcount hR hq hQsize hf.1
      (fun z hz => (hf.2 z hz).2.1) hf0 hητ (hC τ hτ hτC hτ100) hX hlight
    have hb := light_mass_of_cubic_bound hδ hρ hτ hτ1 hε.le (Nat.cast_nonneg q)
      (Nat.cast_nonneg Q.card) hlower hupper hτscale he hbudget.light hm
    convert hb using 1 <;> congr 1 <;> ring

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
