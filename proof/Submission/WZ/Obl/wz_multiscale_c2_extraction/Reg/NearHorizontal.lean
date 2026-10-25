-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.NearHorizontal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.SlopeCharts
import Submission.WZ.Obl.wz_grains_nonsingular_slices.NearHorizontal

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal

abbrev BasicFamily := WangZahlLot.Obl.wz_grains_nonsingular_slices.Family
abbrev GlobalCount := WangZahlLot.Obl.wz_grains_nonsingular_slices.GlobalCount
abbrev GlobalGrains := WangZahlLot.Obl.wz_grains_nonsingular_slices.GlobalGrains

theorem basicFamily_isometry (e : Space ≃ₗᵢ[ℝ] Space) {δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space} (h : BasicFamily δ n x v Y) :
    BasicFamily δ n (fun i => e (x i)) (fun i => e (v i)) (fun i => e '' Y i) := by
  refine ⟨fun i => (e.norm_map _).trans (h.unit i), ?_, ?_, ?_⟩
  · intro i
    change Tube δ (e (x i)) (e (v i)) ⊆ ball 0 1
    rw [tube_isometry]
    rintro _ ⟨p, hp, rfl⟩
    simpa only [mem_ball, dist_zero_right, e.norm_map] using h.ball i hp
  · intro i
    exact e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (h.meas i)
  · intro i
    change e '' Y i ⊆ Tube δ (e (x i)) (e (v i))
    rw [tube_isometry]
    exact image_mono (h.sub i)

theorem globalCount_isometry (e : Space ≃ₗᵢ[ℝ] Space) {η δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} (h : GlobalCount η δ n x v) :
    GlobalCount η δ n (fun i => e (x i)) (fun i => e (v i)) := by
  intro W hW
  have h' := h (e ⁻¹' W) (hW.linear_preimage e.toLinearMap)
  have hvol : volume (e ⁻¹' W) = volume W :=
    e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding W
  simpa only [tube_isometry, image_subset_iff, hvol] using h'

theorem projectedSlice_congr_on {f g : ℝ → ℝ} {E : Set Space}
    (h : ∀ p ∈ E, f (p 2) = g (p 2)) (z : ℝ) :
    ProjectedSlice f E z = ProjectedSlice g E z := by
  have he : (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' E =
      (fun p : Space => (p 0 + g (p 2) * p 1, p 2)) '' E := by
    apply image_congr
    intro p hp
    rw [h p hp]
  unfold ProjectedSlice
  rw [he]

/-- The bounded reciprocal chart inherits the original covering constant. -/
theorem globalGrains_swap_reciprocal {σ η δ : ℝ} {f g : ℝ → ℝ} {E : Set Space}
    (hδ : 0 < δ) (h : GlobalGrains σ η δ f E)
    (hlarge : ∀ p ∈ E, 1 ≤ |f (p 2)|)
    (heq : ∀ z, 1 ≤ |f z| → g z = (f z)⁻¹) :
    GlobalGrains σ η δ g (swapXY '' E) := by
  intro z hz
  by_cases hlargez : 1 ≤ |f z|
  · have hn : f z ≠ 0 := abs_pos.mp (zero_lt_one.trans_le hlargez)
    change Assouad δ (1 - σ) (δ ^ (-η)) (ProjectedSlice g (swapXY '' E) z)
    rw [projectedSlice_swapXY hn (heq z hlargez)]
    apply Assouad.contract_image hδ (inv_ne_zero hn) _ (h z hz)
    rw [abs_inv, ← one_div]
    exact (div_le_one (zero_lt_one.trans_le hlargez)).mpr hlargez
  · have hempty : ProjectedSlice g (swapXY '' E) z = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro u ⟨_, ⟨p, hp, rfl⟩, he⟩
      have hpz : p 2 = z := congrArg Prod.snd he
      exact hlargez (hpz ▸ hlarge p hp)
    change Assouad δ (1 - σ) (δ ^ (-η)) (ProjectedSlice g (swapXY '' E) z)
    rw [hempty]
    exact Assouad.mono_set (h z hz) (empty_subset _)

/-- Near-horizontal tubes have little shading mass without any bound on the slope.
The proof uses the two horizontal coordinate charts and the accepted bounded-slope estimate. -/
theorem near_horizontal_mass_unbounded : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (σ η θ δ : ℝ), 0 < σ → σ < 1 → 0 < η → 0 < δ →
    δ ≤ 1 / 100 → δ ≤ θ → θ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    BasicFamily δ n x v Y → GlobalCount η δ n x v →
    ∀ f : ℝ → ℝ, LipschitzWith 1 f → GlobalGrains σ η δ f (⋃ i, Y i) →
    ∑ i ∈ Finset.univ.filter (fun i => |v i 2| < θ), volume (Y i) ≤
      ENNReal.ofReal (K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) *
        θ ^ (σ / 4) * n * δ ^ 2) := by
  classical
  obtain ⟨K, hK, hnear⟩ := WangZahlLot.Obl.wz_grains_nonsingular_slices.near_horizontal_mass
  refine ⟨2 * K, by linarith, ?_⟩
  intro σ η θ δ hσ0 hσ1 hη hδ hδ100 hδθ hθ100 n x v Y hfamily hcount f hf hgrains
  obtain ⟨g, h, hg, hh, hgb, hhb, hgeq, hheq⟩ := exists_bounded_slope_charts hf
  let A : Set Space := {p | |f (p 2)| ≤ 1}
  have hA : MeasurableSet A := by
    apply isClosed_le _ continuous_const |>.measurableSet
    exact (hf.continuous.comp (show Continuous (fun p : Space => p 2) by fun_prop)).abs
  let Y₁ : Fin n → Set Space := fun i => Y i ∩ A
  let Y₂ : Fin n → Set Space := fun i => Y i \ A
  have hfam₁ : BasicFamily δ n x v Y₁ :=
    ⟨hfamily.unit, hfamily.ball, fun i => (hfamily.meas i).inter hA,
      fun i => (inter_subset_left).trans (hfamily.sub i)⟩
  have hfam₂ : BasicFamily δ n x v Y₂ :=
    ⟨hfamily.unit, hfamily.ball, fun i => (hfamily.meas i).diff hA,
      fun i => sdiff_subset.trans (hfamily.sub i)⟩
  have hsub₁ : (⋃ i, Y₁ i) ⊆ ⋃ i, Y i := iUnion_mono fun _ => inter_subset_left
  have hsub₂ : (⋃ i, Y₂ i) ⊆ ⋃ i, Y i := iUnion_mono fun _ => sdiff_subset
  have hgrains₁ : GlobalGrains σ η δ g (⋃ i, Y₁ i) := by
    intro z hz
    change Assouad δ (1 - σ) (δ ^ (-η)) (ProjectedSlice g (⋃ i, Y₁ i) z)
    rw [projectedSlice_congr_on (f := g) (g := f) (fun p hp => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact hgeq (p 2) hi.2)]
    exact Assouad.mono_set (hgrains z hz) (fun _ hu => image_mono hsub₁ hu)
  have hgrains₂ : GlobalGrains σ η δ h (⋃ i, swapXY '' Y₂ i) := by
    rw [← image_iUnion]
    apply globalGrains_swap_reciprocal hδ
    · intro z hz
      exact Assouad.mono_set (hgrains z hz) (fun _ hu => image_mono hsub₂ hu)
    · intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact (not_le.mp hi.2).le
    · exact hheq
  have hgdist : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1,
      |g z - g z'| ≤ |z - z'| := by
    intro z _ z' _
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hg.dist_le_mul z z'
  have hhdist : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1,
      |h z - h z'| ≤ |z - z'| := by
    intro z _ z' _
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hh.dist_le_mul z z'
  have h₁ := hnear σ η θ δ hσ0 hσ1 hη hδ hδ100 hδθ hθ100 n x v Y₁
    hfam₁ hcount g hg.continuous (fun z _ => hgb z) hgdist hgrains₁
  have h₂ := hnear σ η θ δ hσ0 hσ1 hη hδ hδ100 hδθ hθ100 n
    (fun i => swapXY (x i)) (fun i => swapXY (v i)) (fun i => swapXY '' Y₂ i)
    (basicFamily_isometry swapXY hfam₂) (globalCount_isometry swapXY hcount)
    h hh.continuous (fun z _ => hhb z) hhdist hgrains₂
  simp only [swapXY_two, isometry_volume_image] at h₂
  have hmass : ∀ i, volume (Y i) = volume (Y₁ i) + volume (Y₂ i) := by
    intro i
    exact (measure_inter_add_sdiff (Y i) hA).symm
  simp_rw [hmass]
  rw [Finset.sum_add_distrib]
  refine (add_le_add h₁ h₂).trans ?_
  have hbase : 0 ≤ K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2 := by
    have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by
      apply (le_div_iff₀ hδ).mpr
      linarith)
    have hK0 : 0 ≤ K := by linarith
    have hθ0 : 0 ≤ θ := hδ.le.trans hδθ
    positivity
  rw [← ENNReal.ofReal_add hbase hbase]
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  rfl

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
