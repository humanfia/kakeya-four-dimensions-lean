-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormDiff.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDefs
import Submission.WZ.Obl.wz_direction_convex_count

/-!
# Difference bodies and enlargements of convex sets

`diffBody U = {u₁ - u₂ | u₁ u₂ ∈ U}`. For an open convex set, `vol (diffBody U) ≤ 64 vol U`
(o007's slice estimates). If the original piece of a tube lies in a convex set `U`, the whole
tube lies in `a₀ + κ • diffBody U` for any `a₀ ∈ U` and an explicit `κ`.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise

/-- The difference body of a set. -/
def diffBody (U : Set Space) : Set Space := {y | ∃ u₁ ∈ U, ∃ u₂ ∈ U, y = u₁ - u₂}

theorem convex_diffBody {U : Set Space} (hU : Convex ℝ U) : Convex ℝ (diffBody U) := by
  rintro _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩ _ ⟨b₁, hb₁, b₂, hb₂, rfl⟩ s t hs ht hst
  refine ⟨s • a₁ + t • b₁, hU ha₁ hb₁ hs ht hst, s • a₂ + t • b₂, hU ha₂ hb₂ hs ht hst, ?_⟩
  module

theorem zero_mem_diffBody {U : Set Space} {u : Space} (hu : u ∈ U) : (0 : Space) ∈ diffBody U :=
  ⟨u, hu, u, hu, by simp⟩

theorem neg_mem_diffBody {U : Set Space} {y : Space} (hy : y ∈ diffBody U) : -y ∈ diffBody U := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  exact ⟨b, hb, a, ha, by abel⟩

/-- Scaling inside a convex symmetric body containing `0`. -/
theorem smul_mem_smul_diffBody {U : Set Space} (hU : Convex ℝ U) {y : Space} (hy : y ∈ diffBody U)
    {s κ : ℝ} (hsκ : |s| ≤ κ) : s • y ∈ κ • diffBody U := by
  have hκ : 0 ≤ κ := (abs_nonneg s).trans hsκ
  rcases eq_or_lt_of_le hκ with h0 | hpos
  · subst h0
    have hs : s = 0 := abs_nonpos_iff.mp hsκ
    subst hs
    exact Set.smul_mem_smul_set hy
  · refine ⟨(s / κ) • y, ?_, by
      show κ • (s / κ) • y = s • y
      rw [smul_smul, mul_div_cancel₀ _ hpos.ne']⟩
    have hconv := convex_diffBody hU
    have h0 : (0 : Space) ∈ diffBody U := by
      obtain ⟨a, ha, b, hb, rfl⟩ := hy; exact zero_mem_diffBody ha
    rcases le_total 0 s with hs | hs
    · exact hconv.smul_mem_of_zero_mem h0 hy
        ⟨div_nonneg hs hpos.le, by rw [div_le_one hpos]; exact (le_abs_self s).trans hsκ⟩
    · have he : (s / κ) • y = (-s / κ) • (-y) := by rw [smul_neg, neg_div, neg_smul, neg_neg]
      rw [he]
      exact hconv.smul_mem_of_zero_mem h0 (neg_mem_diffBody hy)
        ⟨div_nonneg (by linarith) hpos.le,
          by rw [div_le_one hpos]; exact (neg_le_abs s).trans hsκ⟩

/-- Sums in a convex body: `a • D + b • D ⊆ (a + b) • D`. -/
theorem add_mem_smul_diffBody {U : Set Space} (hU : Convex ℝ U) {y₁ y₂ : Space} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h₁ : y₁ ∈ a • diffBody U) (h₂ : y₂ ∈ b • diffBody U) :
    y₁ + y₂ ∈ (a + b) • diffBody U := by
  rw [(convex_diffBody hU).add_smul ha hb]
  exact Set.add_mem_add h₁ h₂

theorem isOpen_diffBody {U : Set Space} (hU : IsOpen U) : IsOpen (diffBody U) := by
  have he : diffBody U = ⋃ u₂ ∈ U, (fun y => y - u₂) '' U := by
    ext y
    simp only [diffBody, mem_ofPred_eq, mem_iUnion, mem_image, exists_prop]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, rfl⟩
    · rintro ⟨b, hb, a, ha, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  rw [he]
  refine isOpen_biUnion fun u₂ _ => ?_
  have : (fun y => y - u₂) '' U = (fun y => y + u₂) ⁻¹' U := by
    ext y; simp [sub_eq_iff_eq_add]
  rw [this]
  exact hU.preimage (continuous_id.add continuous_const)

/-- Rogers–Shephard type bound with constant `64`. -/
theorem volume_diffBody_le {U : Set Space} (hUo : IsOpen U) (hU : Convex ℝ U) :
    volume (diffBody U) ≤ 64 * volume U := by
  by_cases h0 : volume U = 0
  · have hUe : U = ∅ := (hUo.measure_eq_zero_iff volume).mp h0
    have : diffBody U = ∅ := by
      ext y; simp [diffBody, hUe]
    simp [this]
  by_cases htop : volume U = ∞
  · simp [htop]
  -- half the difference body
  set D : Set Space := {y | (2 : ℝ) • y ∈ diffBody U} with hD
  have hDo : IsOpen D := (isOpen_diffBody hUo).preimage (continuous_const_smul _)
  have hslice : ∀ y ∈ D, ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume U ≤
      volume {p | p ∈ U ∧ p + y ∈ U} := by
    rintro y ⟨w₁, h₁, w₂, h₂, hy⟩
    exact WangZahlLot.Obl.wz_direction_convex_count.vol_slice_ge hU h₁ h₂ hy
  have hint := WangZahlLot.Obl.wz_direction_convex_count.lintegral_vol_slice hUo.measurableSet
  have hDle : ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume U * volume D ≤ volume U * volume U := by
    rw [← hint]
    calc ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume U * volume D =
          ∫⁻ y in D, ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume U := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ y in D, volume {p | p ∈ U ∧ p + y ∈ U} :=
          setLIntegral_mono' hDo.measurableSet hslice
      _ ≤ ∫⁻ y, volume {p | p ∈ U ∧ p + y ∈ U} := setLIntegral_le_lintegral _ _
  have hD8 : volume D ≤ 8 * volume U := by
    have h8 : ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) = 8⁻¹ := by
      rw [show ((1 / 2 : ℝ) ^ 3) = (8 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    rw [h8] at hDle
    have hle : volume U * (8⁻¹ * volume D) ≤ volume U * volume U := by
      calc volume U * (8⁻¹ * volume D) = 8⁻¹ * volume U * volume D := by ring
        _ ≤ _ := hDle
    have := (ENNReal.mul_le_mul_iff_right h0 htop).mp hle
    calc volume D = 8 * (8⁻¹ * volume D) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 8 * volume U := by gcongr
  have hsmul : diffBody U = (2 : ℝ) • D := by
    ext y
    constructor
    · intro hy
      refine ⟨(1 / 2 : ℝ) • y, ?_, ?_⟩
      · show (2 : ℝ) • (1 / 2 : ℝ) • y ∈ diffBody U
        rwa [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
      · simp only [smul_smul]; norm_num
    · rintro ⟨y', hy', rfl⟩
      exact hy'
  rw [hsmul, Measure.addHaar_smul, finrank_euclideanSpace_fin]
  calc ENNReal.ofReal |(2 : ℝ) ^ 3| * volume D ≤ 8 * (8 * volume U) := by
        gcongr
        · norm_num
    _ = 64 * volume U := by rw [← mul_assoc]; norm_num

/-- The enlargement `a₀ + κ • diffBody U`. -/
def enlarge (a₀ : Space) (κ : ℝ) (U : Set Space) : Set Space :=
  (fun y => a₀ + y) '' (κ • diffBody U)

theorem convex_enlarge {U : Set Space} (hU : Convex ℝ U) (a₀ : Space) (κ : ℝ) :
    Convex ℝ (enlarge a₀ κ U) :=
  ((convex_diffBody hU).smul κ).translate a₀

theorem volume_enlarge_le {U : Set Space} (hUo : IsOpen U) (hU : Convex ℝ U) (a₀ : Space) {κ : ℝ}
    (hκ : 0 ≤ κ) : volume (enlarge a₀ κ U) ≤ ENNReal.ofReal (κ ^ 3) * (64 * volume U) := by
  rw [enlarge, Set.image_add_left, measure_preimage_add, Measure.addHaar_smul,
    finrank_euclideanSpace_fin, abs_of_nonneg (by positivity)]
  gcongr
  exact volume_diffBody_le hUo hU

/-- If the original piece of a tube lies in a convex set `U`, the whole tube lies in an
explicit enlargement of `U`. -/
theorem tube_subset_enlarge {c : Space} {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) {x v : Space}
    {U : Set Space} (hU : Convex ℝ U) (hsub : subTube c lam δ x v ⊆ U)
    {a₀ : Space} (ha₀ : a₀ ∈ U) {K : ℝ} (hK : |inner ℝ (c - x) v| ≤ K) :
    tube δ x v ⊆ enlarge a₀ (2 + (1 + K) * lam) U := by
  have hax0 : foot c x v - (1 / (2 * lam)) • v + (0 : ℝ) • (1 / lam) • v ∈
      subTube c lam δ x v := axis_mem_tube hδ _ _ ⟨le_rfl, zero_le_one⟩
  have hax1 : foot c x v - (1 / (2 * lam)) • v + (1 : ℝ) • (1 / lam) • v ∈
      subTube c lam δ x v := axis_mem_tube hδ _ _ ⟨zero_le_one, le_rfl⟩
  have he₁U : foot c x v - (1 / (2 * lam)) • v ∈ U := by
    have := hsub hax0; rwa [zero_smul, add_zero] at this
  have he₂U : foot c x v - (1 / (2 * lam)) • v + (1 / lam) • v ∈ U := by
    have := hsub hax1; rwa [one_smul] at this
  have hmidU : ∀ e : Space, ‖e‖ < δ → foot c x v + e ∈ U := by
    intro e he
    apply hsub
    refine mem_tube_iff.mpr ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    have h2 : (1 / 2 : ℝ) * (1 / lam) = 1 / (2 * lam) := by field_simp
    have h : foot c x v + e - (foot c x v - (1 / (2 * lam)) • v + (1 / 2 : ℝ) • (1 / lam) • v)
        = e := by
      rw [smul_smul, h2]; abel
    rwa [h]
  have hfootU : foot c x v ∈ U := by simpa using hmidU 0 (by simpa using hδ)
  intro p hp
  obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp
  have hd₁ : foot c x v - a₀ ∈ diffBody U := ⟨_, hfootU, _, ha₀, rfl⟩
  have hd₂ : (1 / lam) • v ∈ diffBody U :=
    ⟨_, he₂U, _, he₁U, by abel⟩
  have hd₃ : p - (x + t • v) ∈ diffBody U :=
    ⟨_, hmidU _ hpt, _, hfootU, by abel⟩
  have hs : |(t - inner ℝ (c - x) v) * lam| ≤ (1 + K) * lam := by
    rw [abs_mul, abs_of_pos hlam]
    apply mul_le_mul_of_nonneg_right _ hlam.le
    calc |t - inner ℝ (c - x) v| ≤ |t| + |inner ℝ (c - x) v| := abs_sub _ _
      _ ≤ 1 + K := by
          gcongr
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hK0 : 0 ≤ 1 + K := by linarith [abs_nonneg (inner ℝ (c - x) v)]
  have h1 : foot c x v - a₀ ∈ (1 : ℝ) • diffBody U := by rwa [one_smul]
  have h2 := smul_mem_smul_diffBody hU hd₂ hs
  have h3 : p - (x + t • v) ∈ (1 : ℝ) • diffBody U := by rwa [one_smul]
  have h12 := add_mem_smul_diffBody hU zero_le_one (by positivity) h1 h2
  have h123 := add_mem_smul_diffBody hU (by positivity) zero_le_one h12 h3
  have hdecomp : foot c x v - a₀ + ((t - inner ℝ (c - x) v) * lam) • (1 / lam) • v +
      (p - (x + t • v)) = p - a₀ := by
    rw [smul_smul, show (t - inner ℝ (c - x) v) * lam * (1 / lam) = t - inner ℝ (c - x) v by
      field_simp]
    simp only [foot]
    module
  refine ⟨p - a₀, ?_, by abel⟩
  rw [← hdecomp]
  convert h123 using 2
  ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
