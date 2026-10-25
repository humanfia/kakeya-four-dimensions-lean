-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_horizontal_tube_exclusion.Vertical.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_horizontal_tube_exclusion.Charts
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Extremal

/-!
# Emptying the shadings of nearly horizontal tubes

Take an input example at a small error `η` and empty the shadings of the tubes with
`|v i 2| < θ := δ ^ c`, where `c = min (ε / 2) (1 / 2)` and `η = c σ / 32`.  By
`near_horizontal_mass_lipschitz` these tubes carry at most
`K (1 + log (1 / δ)) δ ^ (-2 η) θ ^ (σ / 4) n δ ^ 2 ≤ δ ^ η n δ ^ 2 / 2`, at most half of the
mass, so the remaining shadings keep `δ ^ ε n δ ^ 2` once `δ ^ (ε - η) ≤ 1 / 2`.  Tubes,
slope and plane map are unchanged: the cover condition and the grains only get weaker.

`ExP` is the frozen example predicate with its slope predicate seeing
`(η, δ, n, v, Y, f, P)`; `FrozenS` is the frozen cover condition (seven conditions,
right-nested), equivalent to `wz_separated_cover_refinement.Strong`.
-/

namespace WangZahlLot.Obl.wz_horizontal_tube_exclusion

open Set Metric MeasureTheory Filter Topology
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open WangZahlLot.Obl.wz_grains_nonsingular_slices
open scoped ENNReal

/-- The frozen multiscale cover condition `S`. -/
def FrozenS (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ, r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧
    ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space, (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
        (1 / 2 : ENNReal) * volume (Tube ρ (z j) (w j))) ∧
      (∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j, ∃ i, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j j', (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ) ≤
        δ ^ (-η) * (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j') (w j')} : ℝ)) ∧
      (∀ j, ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ∧
          Tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) *
          (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ)) * volume W) ∧
      (∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
        Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j')

theorem strong_of_frozenS {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : FrozenS η δ n x v) : Strong η δ n x v := by
  intro r hr hr1
  obtain ⟨ρ, h1, h2, h3, k, hk, z, w, a, b, c, d, e, f, g⟩ := h r hr hr1
  exact ⟨ρ, h1, h2, h3, k, hk, z, w, ⟨a, b, c, d, e, f⟩, g⟩

theorem frozenS_of_strong {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Strong η δ n x v) : FrozenS η δ n x v := by
  intro r hr hr1
  obtain ⟨ρ, h1, h2, h3, k, hk, z, w, ⟨a, b, c, d, e, f⟩, g⟩ := h r hr hr1
  exact ⟨ρ, h1, h2, h3, k, hk, z, w, a, b, c, d, e, f, g⟩

/-- The frozen example predicate, with the slope predicate seeing `(η, δ, n, v, Y, f, P)`. -/
def ExP (Q : ℝ → ℝ → (n : ℕ) → (Fin n → Space) → (Fin n → Set Space) → (ℝ → ℝ) →
    (Space → Space) → Prop) (σ : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y ∧ FrozenS η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
      ∃ (f : ℝ → ℝ) (P : Space → Space), Q η δ n v Y f P ∧
        (∀ z : ℝ, z ∈ Set.Icc (-1) 1 → AD δ (1 - σ) (δ ^ (-η)) (PS f (⋃ i, Y i) z)) ∧
        LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y i) → ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
        (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
          AD ρ (1 - σ) (δ ^ (-η))
            ((fun q : Space => inner ℝ (P p) q) '' ((⋃ i, Y i) ∩ Metric.ball p (Real.sqrt ρ))))

/-! ### Scale cutoffs -/

/-- A positive power absorbs a logarithmic factor at small scales. -/
theorem exists_log_power_cutoff (A : ℝ) {B e : ℝ} (hB : 0 < B) (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      A * (1 + Real.log (1 / δ)) * δ ^ e ≤ B := by
  have hp : Tendsto (fun δ : ℝ => δ ^ e) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow he.ne'] using
      (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero he
  have ht : Tendsto (fun δ : ℝ => A * (1 + Real.log (1 / δ)) * δ ^ e)
      (𝓝[>] 0) (𝓝 0) := by
    convert (hp.sub hl).const_mul A using 1
    · funext δ
      rw [one_div, Real.log_inv]
      ring
    · simp
  have hmem : {δ : ℝ | A * (1 + Real.log (1 / δ)) * δ ^ e < B} ∈ 𝓝[>] 0 :=
    ht (gt_mem_nhds hB)
  obtain ⟨d, hd, hcut⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hmem
  exact ⟨d, hd, fun δ hδ hδd => (hcut ⟨hδ, hδd⟩).le⟩

/-- A strict exponent gap absorbs constants and one logarithmic factor. -/
theorem exists_log_power_comparison (A : ℝ) {B e₁ e₂ : ℝ}
    (hB : 0 < B) (he : e₂ < e₁) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      A * (1 + Real.log (1 / δ)) * δ ^ e₁ ≤ B * δ ^ e₂ := by
  obtain ⟨d, hd, hcut⟩ := exists_log_power_cutoff A hB (sub_pos.mpr he)
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have h := mul_le_mul_of_nonneg_right (hcut δ hδ hδd) (Real.rpow_nonneg hδ.le e₂)
  have hp : δ ^ (e₁ - e₂) * δ ^ e₂ = δ ^ e₁ := by
    rw [← Real.rpow_add hδ, sub_add_cancel]
  simpa only [mul_assoc, hp] using h

/-- Deleting a subcollection of mass at most one half keeps at least one half. -/
theorem half_mass_after_deletion {I : Type*} [Fintype I]
    (w : I → ENNReal) (p : I → Prop) [DecidablePred p]
    (hfinite : ∀ i, w i ≠ ⊤)
    (hbad : ∑ i ∈ Finset.univ.filter p, w i ≤ (1 / 2 : ENNReal) * ∑ i, w i) :
    (1 / 2 : ENNReal) * ∑ i, w i ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬p i), w i := by
  classical
  have hM : (∑ i, w i) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hfinite i)
  have hhalf : (1 / 2 : ENNReal) + 1 / 2 = 1 := ENNReal.add_halves 1
  apply (ENNReal.add_le_add_iff_left
    (ENNReal.mul_ne_top (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hM)).mp
  calc
    (1 / 2 : ENNReal) * (∑ i, w i) + (1 / 2 : ENNReal) * (∑ i, w i)
        = ∑ i, w i := by rw [← add_mul, hhalf, one_mul]
    _ = (∑ i ∈ Finset.univ.filter p, w i) +
        ∑ i ∈ Finset.univ.filter (fun i => ¬p i), w i :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ p w).symm
    _ ≤ _ := add_le_add hbad le_rfl

/-! ### The exclusion -/

/-- Examples whose slope is 1-Lipschitz with `|f| ≤ 3` on `[-1, 1]` yield examples with the
same slope in which every tube with a nonempty shading has `|v i 2| ≥ δ ^ η`. -/
theorem exclusion {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (h : ExP (fun _ _ _ _ _ f _ => LipschitzWith 1 f ∧
      ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → |f z| ≤ 3) σ) :
    ExP (fun η δ _ v Y f _ => (LipschitzWith 1 f ∧
      ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → |f z| ≤ 3) ∧ ∀ i, Y i ≠ ∅ → δ ^ η ≤ |v i 2|) σ := by
  classical
  intro ε d₀ hε hd₀
  obtain ⟨K, hK, hnear⟩ := near_horizontal_mass_lipschitz
  set c : ℝ := min (ε / 2) (1 / 2) with hc_def
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  have hcε : c ≤ ε / 2 := min_le_left _ _
  have hc1 : c ≤ 1 / 2 := min_le_right _ _
  set η : ℝ := c * σ / 32 with hη_def
  have hη : 0 < η := by positivity
  have hηε : η < ε := by
    have hcs : c * σ < c := by nlinarith
    linarith
  have hgap : η < c * σ / 4 - 2 * η := by
    rw [hη_def]
    nlinarith [mul_pos hc hσ0]
  obtain ⟨d₁, hd₁, hlog⟩ := exists_log_power_comparison K
    (B := 1 / 2) (by norm_num) hgap
  obtain ⟨d₂, hd₂, hsmall⟩ := exists_rpow_cutoff hc (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨d₃, hd₃, hhalf⟩ :=
    exists_rpow_cutoff (sub_pos.mpr hηε) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, hH, hS, hYc, hvol, f, P, ⟨hfL, hf3⟩, hG, hPL,
    hPu, hPo, hloc⟩ :=
    h η (min d₀ (min d₁ (min d₂ d₃))) hη (lt_min hd₀ (lt_min hd₁ (lt_min hd₂ hd₃)))
  have hδ1 : δ ≤ 1 := by linarith
  have hδd₀ : δ ≤ d₀ := hδd.trans (min_le_left _ _)
  have hδd₁ : δ ≤ d₁ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₂ : δ ≤ d₂ :=
    hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₃ : δ ≤ d₃ :=
    hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set θ : ℝ := δ ^ c with hθ_def
  have hδθ : δ ≤ θ := by
    conv_lhs => rw [← Real.rpow_one δ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hθ100 : θ ≤ 1 / 100 := hsmall δ hδ hδd₂
  have hcoef : K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * θ ^ (σ / 4) ≤
      (1 / 2 : ℝ) * δ ^ η := by
    calc
      K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * θ ^ (σ / 4)
          = K * (1 + Real.log (1 / δ)) * (δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4)) := by ring
      _ = K * (1 + Real.log (1 / δ)) * δ ^ (c * σ / 4 - 2 * η) := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ _ := hlog δ hδ hδd₁
  have hfam : Family δ n x v Y :=
    ⟨hH.2.1, hH.2.2.1, hH.2.2.2.2.1, hH.2.2.2.2.2.1⟩
  have hcount : GlobalCount η δ n x v := globalCount_of_strong hδ hδ1 (strong_of_frozenS hS)
  have hGG : GlobalGrains σ η δ f (⋃ i, Y i) := hG
  have hbad : ∑ i ∈ Finset.univ.filter (fun i => |v i 2| < θ), volume (Y i) ≤
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) := by
    calc
      _ ≤ ENNReal.ofReal (K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) *
          θ ^ (σ / 4) * n * δ ^ 2) :=
        hnear σ η θ δ hσ0 hσ1 hη hδ hδ100 hδθ hθ100 n x v Y hfam hcount f hfL hGG
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (δ ^ η * n * δ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ ((1 / 2 : ℝ) * δ ^ η) * n * δ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) (sq_nonneg _)
          _ = _ := by ring
      _ = (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      _ ≤ _ := mul_le_mul' le_rfl hH.2.2.2.2.2.2
  let Z : Fin n → Set Space := fun i => if |v i 2| < θ then ∅ else Y i
  have hZY : ∀ i, Z i ⊆ Y i := by
    intro i
    dsimp only [Z]
    split_ifs <;> simp
  have hZc : ∀ i, IsCompact (Z i) := by
    intro i
    dsimp only [Z]
    split_ifs
    · exact isCompact_empty
    · exact hYc i
  have hmass : (1 / 2 : ENNReal) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) := by
    have h := half_mass_after_deletion (fun i => volume (Y i))
      (fun i => |v i 2| < θ) (fun i => (hYc i).measure_lt_top.ne) hbad
    simpa only [Finset.sum_filter, ite_not, Z, apply_ite, measure_empty] using h
  have hhalf' : ENNReal.ofReal (δ ^ (ε - η)) ≤ (1 / 2 : ENNReal) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal (hhalf δ hδ hδd₃)
  have hdense : ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Z i) := by
    have hsplit : δ ^ ε = δ ^ (ε - η) * δ ^ η := by
      rw [← Real.rpow_add hδ, sub_add_cancel]
    calc
      ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2)
          = ENNReal.ofReal (δ ^ (ε - η)) * ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), hsplit]
        ring_nf
      _ ≤ (1 / 2 : ENNReal) * ∑ i, volume (Y i) := mul_le_mul' hhalf' hH.2.2.2.2.2.2
      _ ≤ _ := hmass
  have hZsub : (⋃ i, Z i) ⊆ ⋃ i, Y i := iUnion_mono hZY
  have hpow : δ ^ (-η) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηε.le)
  refine ⟨δ, hδ, hδd₀, hδ100, n, x, v, Z,
    ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1, fun i => (hZc i).measurableSet,
      fun i => (hZY i).trans (hH.2.2.2.2.2.1 i), hdense⟩,
    frozenS_of_strong (strong_mono_error hδ hδ1 hηε.le (strong_of_frozenS hS)),
    hZc, ?_, f, P, ⟨⟨hfL, hf3⟩, ?_⟩, ?_, hPL, fun p hp => hPu p (hZsub hp),
    fun i p hp => hPo i p (hZY i hp), ?_⟩
  · exact (measure_mono hZsub).trans (hvol.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))))
  · intro i hi
    have hnot : ¬ |v i 2| < θ := by
      intro hlt
      exact hi (by simp [Z, hlt])
    exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : c ≤ ε)).trans
      (le_of_not_gt hnot)
  · intro z hz
    exact ad_mono_const hδ (ad_mono (hG z hz) (ps_mono hZsub z)) hpow
  · intro ρ hδρ hρ1 p hp
    exact ad_mono_const (hδ.trans_le hδρ)
      (ad_mono (hloc ρ hδρ hρ1 p (hZsub hp))
        (image_mono (inter_subset_inter_left _ hZsub))) hpow

end WangZahlLot.Obl.wz_horizontal_tube_exclusion
