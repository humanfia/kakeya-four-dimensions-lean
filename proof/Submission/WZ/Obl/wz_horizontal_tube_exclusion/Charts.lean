-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_horizontal_tube_exclusion.Charts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.NearHorizontal

/-!
# Nearly horizontal tubes carry little mass, for any 1-Lipschitz slope

The accepted estimate `wz_grains_nonsingular_slices.near_horizontal_mass` assumes `|f| ≤ 1`
on `[-1, 1]`.  Where `|f| ≥ 1`, exchanging the first two coordinates turns the twisted
coordinate `p 0 + f z * p 1` into `f z * (p 1 + (f z)⁻¹ * p 0)`: the twisted slices for the
reciprocal slope are contractions of the original ones, and the reciprocal of a 1-Lipschitz
function is 1-Lipschitz where its absolute value is at least one.  Clamping gives globally
bounded 1-Lipschitz charts, and the shading of each tube splits along `|f (p 2)| ≤ 1`.

Adapted from the o105 branch of session x0274 (`SlopeCharts`, `Isometry`, `NearHorizontal`).
-/

namespace WangZahlLot.Obl.wz_horizontal_tube_exclusion

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open WangZahlLot.Obl.wz_grains_nonsingular_slices
open scoped ENNReal

/-! ### Covering numbers under rescaling -/

theorem ad_mono_scale {d d' α C : ℝ} {B : Set ℝ}
    (h : AD d α C B) (hdd' : d ≤ d') : AD d' α C B :=
  fun r R a hdr hrR => h r R a (hdd'.trans hdr) hrR

theorem ad_mono_const {d α C C' : ℝ} {B : Set ℝ}
    (hd : 0 < d) (h : AD d α C B) (hCC' : C ≤ C') : AD d α C' B := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hdr hrR
  refine ⟨m, c, hc, hm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hCC'
    (Real.rpow_nonneg (div_nonneg (hd.le.trans (hdr.trans hrR)) (hd.le.trans hdr)) _)

theorem ad_neg_image {d α C : ℝ} {B : Set ℝ}
    (h : AD d α C B) : AD d α C ((fun x => -x) '' B) := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R (-a - R) hdr hrR
  refine ⟨m, (fun j => -c j), ?_, hm⟩
  rintro _ ⟨⟨v, hv, rfl⟩, hlo, hhi⟩
  have hvI : v ∈ Icc (-a - R) (-a - R + R) := ⟨by linarith, by linarith⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hv, hvI⟩)
  refine mem_iUnion.mpr ⟨j, ?_⟩
  simpa only [mem_closedBall, Real.dist_eq, neg_sub_neg, abs_sub_comm] using hj

/-- Positive affine coordinate changes preserve the covering constants. -/
theorem ad_affine_image {d α C a b : ℝ} {B : Set ℝ}
    (hd : 0 < d) (ha : 0 < a) (h : AD d α C B) :
    AD (a * d) α C ((fun x => a * x + b) '' B) := by
  intro r R q hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h (r / a) (R / a) ((q - b) / a)
    ((le_div_iff₀ ha).mpr (by nlinarith)) (div_le_div_of_nonneg_right hrR ha.le)
  refine ⟨m, (fun j => a * c j + b), ?_, ?_⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hxq, hxR⟩
    have hxI : x ∈ Icc ((q - b) / a) ((q - b) / a + R / a) := by
      constructor
      · apply (div_le_iff₀ ha).mpr
        linarith
      · rw [← add_div]
        apply (le_div_iff₀ ha).mpr
        linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hx, hxI⟩)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    have hj' : |x - c j| ≤ r / a := by
      simpa only [mem_closedBall, Real.dist_eq] using hj
    rw [mem_closedBall, Real.dist_eq]
    calc |a * x + b - (a * c j + b)| = a * |x - c j| := by
          rw [show a * x + b - (a * c j + b) = a * (x - c j) by ring,
            abs_mul, abs_of_pos ha]
      _ ≤ r := by simpa only [mul_comm] using (le_div_iff₀ ha).mp hj'
  · have hratio : (R / a) / (r / a) = R / r := by
      rw [div_div_div_cancel_right₀ ha.ne']
    simpa only [hratio] using hm

/-- A nonzero scalar contraction preserves the minimum scale and the constant. -/
theorem ad_contract_image {d α C a : ℝ} {B : Set ℝ}
    (hd : 0 < d) (ha : a ≠ 0) (ha1 : |a| ≤ 1) (h : AD d α C B) :
    AD d α C ((fun x => a * x) '' B) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha1
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have heq : ((fun x : ℝ => (-a) * x + 0) '' ((fun x => -x) '' B)) =
        (fun x => a * x) '' B := by
      rw [image_image]
      congr 1
      funext x
      ring
    have hscaled := ad_affine_image (a := -a) (b := 0) hd (neg_pos.mpr hneg) (ad_neg_image h)
    rw [heq] at hscaled
    exact ad_mono_scale hscaled (by nlinarith)
  · have hscaled := ad_affine_image (a := a) (b := 0) hd hpos h
    simp only [add_zero] at hscaled
    exact ad_mono_scale hscaled (by nlinarith)

/-! ### Exchanging the horizontal coordinates -/

/-- Exchange the first two coordinates, keeping the height. -/
noncomputable def swapXY : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 1)

theorem swapXY_zero (p : Space) : swapXY p 0 = p 1 := by
  simp [swapXY, Equiv.piCongrLeft'_apply]

theorem swapXY_one (p : Space) : swapXY p 1 = p 0 := by
  simp [swapXY, Equiv.piCongrLeft'_apply]

theorem swapXY_two (p : Space) : swapXY p 2 = p 2 := by
  rfl

/-- Swapping the horizontal coordinates replaces a nonzero slope by its reciprocal, and
contracts each twisted slice by that reciprocal. -/
theorem ps_swapXY {f g : ℝ → ℝ} {z : ℝ}
    (hfn : f z ≠ 0) (hg : g z = (f z)⁻¹) (E : Set Space) :
    PS g (swapXY '' E) z = (fun u => (f z)⁻¹ * u) '' PS f E z := by
  ext u
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, he⟩
    have hz : p 2 = z := by simpa only [swapXY_two] using congrArg Prod.snd he
    have hu : p 1 + g z * p 0 = u := by
      simpa only [swapXY_zero, swapXY_one, swapXY_two, hz] using congrArg Prod.fst he
    refine ⟨p 0 + f z * p 1, ⟨p, hp, ?_⟩, ?_⟩
    · exact Prod.ext (by simp only [hz]) hz
    · rw [← hu, hg]
      field_simp
      ring
  · rintro ⟨v, ⟨p, hp, he⟩, rfl⟩
    have hz : p 2 = z := congrArg Prod.snd he
    have hu : p 0 + f z * p 1 = v := by simpa only [hz] using congrArg Prod.fst he
    refine ⟨swapXY p, ⟨p, hp, rfl⟩, ?_⟩
    apply Prod.ext
    · simp only [swapXY_zero, swapXY_one, swapXY_two, hz, hg]
      rw [← hu]
      field_simp
      ring
    · exact (swapXY_two p).trans hz

/-- Reciprocation is nonexpanding where the slope has absolute value at least one. -/
theorem reciprocal_lipschitzOn {f : ℝ → ℝ} {D : Set ℝ}
    (hf : LipschitzWith 1 f) (hlarge : ∀ z ∈ D, 1 ≤ |f z|) :
    LipschitzOnWith 1 (fun z => (f z)⁻¹) D := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxpos : 0 < |f x| := zero_lt_one.trans_le (hlarge x hx)
  have hypos : 0 < |f y| := zero_lt_one.trans_le (hlarge y hy)
  have hden : 1 ≤ |f x| * |f y| := by
    nlinarith [hlarge x hx, hlarge y hy]
  have hdist : dist ((f x)⁻¹) ((f y)⁻¹) ≤ dist (f x) (f y) := by
    rw [Real.dist_eq, inv_sub_inv (abs_pos.mp hxpos) (abs_pos.mp hypos), abs_div, abs_mul,
      Real.dist_eq, abs_sub_comm (f y) (f x)]
    exact div_le_self (abs_nonneg _) hden
  exact hdist.trans (hf.dist_le_mul x y)

/-- Clamping gives a globally bounded 1-Lipschitz extension. -/
theorem bounded_lipschitz_extension {g : ℝ → ℝ} {D : Set ℝ}
    (hg : LipschitzOnWith 1 g D) (hbound : ∀ z ∈ D, |g z| ≤ 1) :
    ∃ h : ℝ → ℝ, LipschitzWith 1 h ∧ (∀ z, |h z| ≤ 1) ∧ EqOn g h D := by
  obtain ⟨h, hh, heq⟩ := hg.extend_real
  refine ⟨fun z => max (-1) (min 1 (h z)), (hh.const_min 1).const_max (-1), ?_, ?_⟩
  · intro z
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · intro z hz
    dsimp only
    rw [← heq hz]
    have hb := abs_le.mp (hbound z hz)
    rw [min_eq_right hb.2, max_eq_right hb.1]

/-- The two horizontal charts of a 1-Lipschitz slope have bounded 1-Lipschitz slopes. -/
theorem exists_bounded_slope_charts {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    ∃ g h : ℝ → ℝ, LipschitzWith 1 g ∧ LipschitzWith 1 h ∧
      (∀ z, |g z| ≤ 1) ∧ (∀ z, |h z| ≤ 1) ∧
      (∀ z, |f z| ≤ 1 → g z = f z) ∧
      (∀ z, 1 ≤ |f z| → h z = (f z)⁻¹) := by
  obtain ⟨g, hg, hgb, hgeq⟩ := bounded_lipschitz_extension
    (D := {z | |f z| ≤ 1}) hf.lipschitzOnWith (fun _ hz => hz)
  obtain ⟨h, hh, hhb, hheq⟩ := bounded_lipschitz_extension
    (reciprocal_lipschitzOn hf (D := {z | 1 ≤ |f z|}) (fun _ hz => hz))
    (fun z hz => by
      rw [abs_inv, ← one_div]
      exact (div_le_one (zero_lt_one.trans_le hz)).mpr hz)
  exact ⟨g, h, hg, hh, hgb, hhb, fun z hz => (hgeq hz).symm,
    fun z hz => (hheq hz).symm⟩

/-! ### Isometries move the families -/

theorem isometry_volume_image (e : Space ≃ₗᵢ[ℝ] Space) (E : Set Space) :
    volume (e '' E) = volume E := by
  have h := e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding (e '' E)
  simpa only [preimage_image_eq _ e.injective] using h.symm

theorem isometry_thickening (e : Space ≃ₗᵢ[ℝ] Space) (d : ℝ) (E : Set Space) :
    thickening d (e '' E) = e '' thickening d E := by
  ext q
  constructor
  · intro hq
    obtain ⟨_, ⟨p, hp, rfl⟩, hdist⟩ := mem_thickening_iff.mp hq
    refine ⟨e.symm q, mem_thickening_iff.mpr ⟨p, hp, ?_⟩, e.apply_symm_apply q⟩
    rw [← e.dist_map (e.symm q) p, e.apply_symm_apply]
    exact hdist
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hdist⟩ := mem_thickening_iff.mp hq
    exact mem_thickening_iff.mpr ⟨e p, ⟨p, hp, rfl⟩, by simpa using hdist⟩

theorem isometry_segment (e : Space ≃ₗᵢ[ℝ] Space) (x y : Space) :
    segment ℝ (e x) (e y) = e '' segment ℝ x y :=
  (image_segment ℝ e.toLinearMap.toAffineMap x y).symm

theorem tube_isometry (e : Space ≃ₗᵢ[ℝ] Space) (d : ℝ) (x v : Space) :
    Tube d (e x) (e v) = e '' Tube d x v := by
  change thickening d (segment ℝ (e x) (e x + e v)) = _
  rw [← map_add, isometry_segment, isometry_thickening]

theorem family_isometry (e : Space ≃ₗᵢ[ℝ] Space) {δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space} (h : Family δ n x v Y) :
    Family δ n (fun i => e (x i)) (fun i => e (v i)) (fun i => e '' Y i) := by
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

/-! ### The two slope charts -/

theorem ps_congr_on {f g : ℝ → ℝ} {E : Set Space}
    (h : ∀ p ∈ E, f (p 2) = g (p 2)) (z : ℝ) :
    PS f E z = PS g E z := by
  have he : (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' E =
      (fun p : Space => (p 0 + g (p 2) * p 1, p 2)) '' E := by
    apply image_congr
    intro p hp
    rw [h p hp]
  unfold PS
  rw [he]

/-- The reciprocal chart inherits the global grains, with the same constant. -/
theorem globalGrains_swap_reciprocal {σ η δ : ℝ} {f g : ℝ → ℝ} {E : Set Space}
    (hδ : 0 < δ) (h : GlobalGrains σ η δ f E)
    (hlarge : ∀ p ∈ E, 1 ≤ |f (p 2)|)
    (heq : ∀ z, 1 ≤ |f z| → g z = (f z)⁻¹) :
    GlobalGrains σ η δ g (swapXY '' E) := by
  intro z hz
  by_cases hlargez : 1 ≤ |f z|
  · have hn : f z ≠ 0 := abs_pos.mp (zero_lt_one.trans_le hlargez)
    rw [ps_swapXY hn (heq z hlargez)]
    apply ad_contract_image hδ (inv_ne_zero hn) _ (h z hz)
    rw [abs_inv, ← one_div]
    exact (div_le_one (zero_lt_one.trans_le hlargez)).mpr hlargez
  · have hempty : PS g (swapXY '' E) z = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro u ⟨_, ⟨p, hp, rfl⟩, he⟩
      have hpz : p 2 = z := congrArg Prod.snd he
      exact hlargez (hpz ▸ hlarge p hp)
    rw [hempty]
    exact ad_mono (h z hz) (empty_subset _)

/-- Nearly horizontal tubes carry little shading mass, for any 1-Lipschitz slope.
The shading splits along `|f (p 2)| ≤ 1`; the first part is handled by the bounded chart,
the second, after exchanging the horizontal coordinates, by the reciprocal chart. -/
theorem near_horizontal_mass_lipschitz : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (σ η θ δ : ℝ), 0 < σ → σ < 1 → 0 < η → 0 < δ →
    δ ≤ 1 / 100 → δ ≤ θ → θ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Family δ n x v Y → GlobalCount η δ n x v →
    ∀ f : ℝ → ℝ, LipschitzWith 1 f → GlobalGrains σ η δ f (⋃ i, Y i) →
    ∑ i ∈ Finset.univ.filter (fun i => |v i 2| < θ), volume (Y i) ≤
      ENNReal.ofReal (K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) *
        θ ^ (σ / 4) * n * δ ^ 2) := by
  classical
  obtain ⟨K, hK, hnear⟩ := near_horizontal_mass
  refine ⟨2 * K, by linarith, ?_⟩
  intro σ η θ δ hσ0 hσ1 hη hδ hδ100 hδθ hθ100 n x v Y hfamily hcount f hf hgrains
  obtain ⟨g, h, hg, hh, hgb, hhb, hgeq, hheq⟩ := exists_bounded_slope_charts hf
  let A : Set Space := {p | |f (p 2)| ≤ 1}
  have hA : MeasurableSet A := by
    apply isClosed_le _ continuous_const |>.measurableSet
    exact (hf.continuous.comp (show Continuous (fun p : Space => p 2) by fun_prop)).abs
  let Y₁ : Fin n → Set Space := fun i => Y i ∩ A
  let Y₂ : Fin n → Set Space := fun i => Y i \ A
  have hfam₁ : Family δ n x v Y₁ :=
    ⟨hfamily.unit, hfamily.ball, fun i => (hfamily.meas i).inter hA,
      fun i => (inter_subset_left).trans (hfamily.sub i)⟩
  have hfam₂ : Family δ n x v Y₂ :=
    ⟨hfamily.unit, hfamily.ball, fun i => (hfamily.meas i).diff hA,
      fun i => sdiff_subset.trans (hfamily.sub i)⟩
  have hsub₁ : (⋃ i, Y₁ i) ⊆ ⋃ i, Y i := iUnion_mono fun _ => inter_subset_left
  have hsub₂ : (⋃ i, Y₂ i) ⊆ ⋃ i, Y i := iUnion_mono fun _ => sdiff_subset
  have hgrains₁ : GlobalGrains σ η δ g (⋃ i, Y₁ i) := by
    intro z hz
    rw [ps_congr_on (f := g) (g := f) (fun p hp => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact hgeq (p 2) hi.2)]
    exact ad_mono (hgrains z hz) (ps_mono hsub₁ z)
  have hgrains₂ : GlobalGrains σ η δ h (⋃ i, swapXY '' Y₂ i) := by
    rw [← image_iUnion]
    apply globalGrains_swap_reciprocal hδ
    · intro z hz
      exact ad_mono (hgrains z hz) (ps_mono hsub₂ z)
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
    (family_isometry swapXY hfam₂) (globalCount_isometry swapXY hcount)
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
  apply le_of_eq
  ring

end WangZahlLot.Obl.wz_horizontal_tube_exclusion
