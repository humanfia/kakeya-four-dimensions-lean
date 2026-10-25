-- Adapted from LOT tree g-oai-074, obligation o245, session x0854, commit 3602b8f657fd9f9293587a9dd3e1bdba2451d373.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RegSlope/Cluster.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope.Pair
-- Use the coefficient-cover module on the accepted integration line.
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.HeavyCoefficientCover

/-!
# Slope regularization: scalar clustering in one static group

In the static `s`-group `Y` of `y`, the auxiliary prior `ν_Y = s⁻² ν|(group ∩ long labels)`
has mass `≤ (4K + 5) K / δ` and coefficient-ball masses `≤ 4 (4K + 5) K r^d / δ` (from the mixed
cap at the times of the long labels), and the pair-prepared incidences occupy few spacetime
cells (`spacetime_count`). The accepted scalar clustering (`scalar_heavy_coefficient_cover`,
o235) then gives few heavy codes of `(β, γ)` at width `s` carrying all but `s² N^(-η)` of the
group's incidence mass (`group_cluster`).
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

open FirstJet Submission.Obl.k4_scalar_coefficient_clustering

/-- The conclusion of `scalar_heavy_coefficient_cover` at one `N`. -/
def HeavyCoverAt (d c ε η N : ℝ) : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (a : α → EuclideanSpace ℝ (Fin 3))
    (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
    Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
    (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) →
    (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
    (∀ l t, (l, t) ∈ E →
      (⌊t / (N ^ (-c))⌋, ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-c))⌋) ∈ F) →
    (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r →
      ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d)) →
    ∃ G : Finset (Fin 3 → ℤ),
      (∀ q ∈ G, ENNReal.ofReal (N ^ (-c * d - ε)) ≤
        ((ν.prod volume).restrict E) {p | coefficientCode (N ^ (-c)) (a p.1) = q}) ∧
      (G.card : ℝ) ≤ (ν.prod volume).real E / N ^ (-c * d - ε) ∧
      ((ν.prod volume).restrict E) {p | coefficientCode (N ^ (-c)) (a p.1) ∉ G} <
        ENNReal.ofReal (N ^ (-η))

theorem heavyCoverAt_eventually (d c ε : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c)
    (hε : 0 < ε) : ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      HeavyCoverAt d c ε η N :=
  Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.scalar_heavy_coefficient_cover
    d c ε hd hd1 hc hε

/-- The coefficient vector `(β, γ, 0)`. -/
def coefVec {Ω : Type*} (β γ : Ω → ℝ) (l : Ω) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![β l, γ l, 0]

@[simp] theorem coefVec_zero {Ω : Type*} (β γ : Ω → ℝ) (l : Ω) : coefVec β γ l 0 = β l := by
  simp [coefVec]

@[simp] theorem coefVec_one {Ω : Type*} (β γ : Ω → ℝ) (l : Ω) : coefVec β γ l 1 = γ l := by
  simp [coefVec]

@[simp] theorem coefVec_two {Ω : Type*} (β γ : Ω → ℝ) (l : Ω) : coefVec β γ l 2 = 0 := by
  simp [coefVec]

theorem measurable_coefVec {Ω : Type*} [MeasurableSpace Ω] {β γ : Ω → ℝ} (hβ : Measurable β)
    (hγ : Measurable γ) : Measurable (coefVec β γ) := by
  unfold coefVec
  refine (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp ?_
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · exact hβ
  · exact hγ
  · exact measurable_const

theorem norm_coefVec_le {Ω : Type*} {β γ : Ω → ℝ} {K : ℝ} (hβ : ∀ l, |β l| ≤ K)
    (hγ : ∀ l, |γ l| ≤ K) (l : Ω) : ‖coefVec β γ l‖ ≤ 2 * K := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hβ l)
  have h := EuclideanSpace.real_norm_sq_eq (coefVec β γ l)
  simp only [Fin.sum_univ_three, coefVec_zero, coefVec_one, coefVec_two] at h
  have h1 : β l ^ 2 ≤ K ^ 2 := by
    have := hβ l; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : γ l ^ 2 ≤ K ^ 2 := by
    have := hγ l; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  nlinarith [norm_nonneg (coefVec β γ l)]

section slices

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Incidence mass over a label set from bounds on its time slices. -/
theorem mass_le_of_slices {ν : Measure Ω} [SFinite ν] {E₀ : Set (Ω × ℝ)}
    (hE₀ : MeasurableSet E₀) (hE01 : E₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1) {S : Set Ω}
    (hS : MeasurableSet S) {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ν {l | (l, t) ∈ E₀ ∧ l ∈ S} ≤ ENNReal.ofReal B) :
    (ν.prod volume) (E₀ ∩ S ×ˢ univ) ≤ ENNReal.ofReal B := by
  rw [Measure.prod_apply_symm (hE₀.inter (hS.prod MeasurableSet.univ))]
  calc ∫⁻ t, ν ((fun l => (l, t)) ⁻¹' (E₀ ∩ S ×ˢ univ))
      ≤ ∫⁻ t, (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal B) t := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ Icc (0 : ℝ) 1
        · rw [indicator_of_mem ht]
          refine le_trans (measure_mono ?_) (hB t ht)
          intro l hl; exact ⟨hl.1, hl.2.1⟩
        · rw [indicator_of_notMem ht]
          have : (fun l => (l, t)) ⁻¹' (E₀ ∩ S ×ˢ univ) = ∅ := by
            ext l
            simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false]
            intro h; exact ht (hE01 h.1).2
          rw [this, measure_empty]
    _ = ENNReal.ofReal B := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]; simp

/-- Long labels: `δ ν(S)` is at most the incidence mass of `S`. -/
theorem duration_mul_le {ν : Measure Ω} [SFinite ν] {E₀ : Set (Ω × ℝ)}
    (hE₀ : MeasurableSet E₀) {S : Set Ω} (hS : MeasurableSet S) {δ : ℝ}
    (hSL : ∀ l ∈ S, ENNReal.ofReal δ ≤ duration E₀ l) :
    ENNReal.ofReal δ * ν S ≤ (ν.prod volume) (E₀ ∩ S ×ˢ univ) := by
  have hm : MeasurableSet (E₀ ∩ S ×ˢ univ) := hE₀.inter (hS.prod MeasurableSet.univ)
  rw [Measure.prod_apply hm]
  calc ENNReal.ofReal δ * ν S = ∫⁻ _l in S, ENNReal.ofReal δ ∂ν := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ l in S, volume (Prod.mk l ⁻¹' (E₀ ∩ S ×ˢ univ)) ∂ν := by
        refine setLIntegral_mono (measurable_measure_prodMk_left hm) fun l hl => ?_
        refine (hSL l hl).trans (le_of_eq ?_)
        unfold duration; congr 1; ext t; simp [hl]
    _ ≤ ∫⁻ l, volume (Prod.mk l ⁻¹' (E₀ ∩ S ×ˢ univ)) ∂ν := setLIntegral_le_lintegral _ _

theorem card_Icc_symm {R : ℤ} (hR : 0 ≤ R) : ((Finset.Icc (-R) R).card : ℝ) = 2 * R + 1 := by
  rw [Int.card_Icc]
  have : R + 1 - -R = 2 * R + 1 := by ring
  rw [this]
  have h : (((2 * R + 1).toNat : ℤ) : ℝ) = ((2 * R + 1 : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  push_cast at h ⊢
  exact h

/-- The labeled mass of one static group at one time. -/
theorem slice_group_le {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (hU : UnregularizedChart ν y β γ E F d K ζ)
    {s : ℝ} (hs : ζ ≤ s) (hs1 : s ≤ 1) (Y : Fin 2 → ℤ) (t : ℝ) :
    ν {l | (l, t) ∈ E ∧ ∀ i, ⌊y l i / s⌋ = Y i} ≤ ENNReal.ofReal ((4 * K + 5) * (K * s ^ 2)) := by
  classical
  have hK : 0 ≤ K := (abs_nonneg _).trans (hU.bound_F 0 0)
  have hζ1 : ζ ≤ 1 := hs.trans hs1
  set R : ℤ := ⌈2 * K / 1⌉ + 1 with hR
  have hR0 : 0 ≤ R := by
    have : (0 : ℝ) ≤ ⌈2 * K / 1⌉ := (by positivity : (0:ℝ) ≤ 2 * K / 1).trans (Int.le_ceil _)
    have : (0 : ℤ) ≤ ⌈2 * K / 1⌉ := by exact_mod_cast this
    omega
  have hsub : {l | (l, t) ∈ E ∧ ∀ i, ⌊y l i / s⌋ = Y i} ⊆
      ⋃ j ∈ Finset.Icc (-R) R, {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / 1⌋ = j ∧
        ⌊y l 0 / s⌋ = Y 0 ∧ ⌊y l 1 / s⌋ = Y 1} := by
    rintro l ⟨hl, hY⟩
    have ht := (hU.subset_E hl).2
    have hx := floor_mem_range (s := 1) one_pos (abs_xbar_le hU.bound_β hU.bound_γ (l := l) ht)
    exact mem_biUnion hx ⟨hl, rfl, hY 0, hY 1⟩
  calc ν {l | (l, t) ∈ E ∧ ∀ i, ⌊y l i / s⌋ = Y i}
      ≤ ∑ j ∈ Finset.Icc (-R) R, ν {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / 1⌋ = j ∧
        ⌊y l 0 / s⌋ = Y 0 ∧ ⌊y l 1 / s⌋ = Y 1} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _j ∈ Finset.Icc (-R) R, ENNReal.ofReal (K * s ^ 2 * 1 ^ d) :=
        Finset.sum_le_sum fun j _ => hU.mixedCap t s 1 hs hs1 hζ1 le_rfl Y j
    _ = ENNReal.ofReal ((2 * R + 1) * (K * s ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_Icc_symm hR0, Real.one_rpow, mul_one]
    _ ≤ ENNReal.ofReal ((4 * K + 5) * (K * s ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have hc : (⌈2 * K / 1⌉ : ℝ) < 2 * K / 1 + 1 := Int.ceil_lt_add_one _
        have hd1 : (2 * K / 1 : ℝ) = 2 * K := div_one _
        have h1 : (2 * (R : ℝ) + 1) ≤ 4 * K + 5 := by
          rw [hR]; push_cast; linarith
        exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- Labels of one static group whose coefficients lie within `r` of `(b₀, b₁)`, at one time. -/
theorem slice_ball_le {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (hU : UnregularizedChart ν y β γ E F d K ζ)
    {s r : ℝ} (hs0 : 0 < s) (hs : ζ ≤ s) (hsr : s ≤ r) (hr : 4 * r ≤ 1) (Y : Fin 2 → ℤ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (b₀ b₁ : ℝ) :
    ν {l | (l, t) ∈ E ∧ (∀ i, ⌊y l i / s⌋ = Y i) ∧ |β l - b₀| < r ∧ |γ l - b₁| < r} ≤
      ENNReal.ofReal (2 * (K * s ^ 2 * (4 * r) ^ d)) := by
  classical
  have hK : 0 ≤ K := (abs_nonneg _).trans (hU.bound_F 0 0)
  have hr0 : 0 < r := lt_of_lt_of_le hs0 hsr
  have hs1 : s ≤ 1 := by linarith
  set w := 4 * r with hw
  have hw0 : 0 < w := by positivity
  set c₀ := b₀ + t * b₁ with hc₀
  set j₀ : ℤ := ⌊(c₀ - 2 * r) / w⌋ with hj₀
  have hsub : {l | (l, t) ∈ E ∧ (∀ i, ⌊y l i / s⌋ = Y i) ∧ |β l - b₀| < r ∧ |γ l - b₁| < r} ⊆
      ⋃ j ∈ ({j₀, j₀ + 1} : Finset ℤ), {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / w⌋ = j ∧
        ⌊y l 0 / s⌋ = Y 0 ∧ ⌊y l 1 / s⌋ = Y 1} := by
    rintro l ⟨hl, hY, hβl, hγl⟩
    have hx : |xbar β γ l t - c₀| < 2 * r := by
      have e : xbar β γ l t - c₀ = (β l - b₀) + t * (γ l - b₁) := by
        simp only [xbar, hc₀]; ring
      rw [e]
      have : |t * (γ l - b₁)| < r := by
        rw [abs_mul, abs_of_nonneg ht.1]
        calc t * |γ l - b₁| ≤ 1 * |γ l - b₁| := by gcongr; exact ht.2
          _ < r := by rw [one_mul]; exact hγl
      calc |(β l - b₀) + t * (γ l - b₁)| ≤ |β l - b₀| + |t * (γ l - b₁)| := abs_add_le _ _
        _ < 2 * r := by linarith
    rw [abs_lt] at hx
    have h1 : j₀ ≤ ⌊xbar β γ l t / w⌋ := by
      rw [Int.le_floor]
      calc (j₀ : ℝ) ≤ (c₀ - 2 * r) / w := Int.floor_le _
        _ ≤ xbar β γ l t / w := by gcongr; linarith
    have h2 : ⌊xbar β γ l t / w⌋ < j₀ + 2 := by
      rw [Int.floor_lt]
      have h3 : (c₀ - 2 * r) / w < j₀ + 1 := Int.lt_floor_add_one _
      have h4 : xbar β γ l t / w < (c₀ - 2 * r) / w + 1 := by
        rw [div_add_one hw0.ne', div_lt_div_iff_of_pos_right hw0]; linarith
      push_cast; linarith
    have hmem : ⌊xbar β γ l t / w⌋ ∈ ({j₀, j₀ + 1} : Finset ℤ) := by
      rw [Finset.mem_insert, Finset.mem_singleton]; omega
    exact mem_biUnion hmem ⟨hl, rfl, hY 0, hY 1⟩
  calc ν {l | (l, t) ∈ E ∧ (∀ i, ⌊y l i / s⌋ = Y i) ∧ |β l - b₀| < r ∧ |γ l - b₁| < r}
      ≤ ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ), ν {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / w⌋ = j ∧
        ⌊y l 0 / s⌋ = Y 0 ∧ ⌊y l 1 / s⌋ = Y 1} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _j ∈ ({j₀, j₀ + 1} : Finset ℤ), ENNReal.ofReal (K * s ^ 2 * w ^ d) :=
        Finset.sum_le_sum fun j _ => hU.mixedCap t s w hs hs1 (by linarith) hr Y j
    _ ≤ ENNReal.ofReal (2 * (K * s ^ 2 * w ^ d)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := Finset.card_insert_le j₀ ({j₀ + 1} : Finset ℤ)
        rw [Finset.card_singleton] at this
        exact_mod_cast this

end slices

theorem le_ofReal_div_of_mul_le {x : ENNReal} {δ B : ℝ} (hδ : 0 < δ)
    (h : ENNReal.ofReal δ * x ≤ ENNReal.ofReal B) : x ≤ ENNReal.ofReal (B / δ) := by
  rw [ENNReal.ofReal_div_of_pos hδ, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hδ))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h

/-- The pair-prepared long-label incidences of one static group at width `s`. -/
def groupSet {Ω : Type*} [MeasurableSpace Ω] (E₀ : Set (Ω × ℝ)) (δ s K₂ : ℝ)
    (y : Ω → Fin 2 → ℝ) (Y : Fin 2 → ℤ) : Set (Ω × ℝ) :=
  pairGood (E₀ ∩ longLabels E₀ δ ×ˢ univ) s K₂ ∩ {l | ∀ i, ⌊y l i / s⌋ = Y i} ×ˢ univ

theorem measurableSet_group {Ω : Type*} [MeasurableSpace Ω] {y : Ω → Fin 2 → ℝ}
    (hy : Measurable y) (s : ℝ) (Y : Fin 2 → ℤ) :
    MeasurableSet {l : Ω | ∀ i, ⌊y l i / s⌋ = Y i} := by
  have : {l : Ω | ∀ i, ⌊y l i / s⌋ = Y i} = ⋂ i, {l | ⌊y l i / s⌋ = Y i} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (Int.measurable_floor.comp (((measurable_pi_apply i).comp hy).div_const s))
      (measurableSet_singleton _)

/-- **Scalar clustering in one static group.** -/
theorem group_cluster {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (hd : 0 ≤ d) (hd1 : d < 1)
    {c' ε₂ ηc N : ℝ} (hN : 0 < N) (hHC : HeavyCoverAt d c' ε₂ ηc N)
    (hs : ζ ≤ N ^ (-c')) (hs1 : N ^ (-c') ≤ 1)
    {E₀ : Set (Ω × ℝ)} (hE₀ : MeasurableSet E₀) (hE₀E : E₀ ⊆ E) {δ K₂ : ℝ} (hδ : 0 < δ)
    (hK₂ : 0 < K₂) (n1 : 2 * K ≤ N ^ ηc) (n2 : 4 * ((4 * K + 5) * K) / δ ≤ N ^ ηc)
    (n3 : 2 * (K₂ * ((4 * K + 3) * K)) ≤ N ^ ηc) (Y : Fin 2 → ℤ) :
    ∃ G : Finset (Fin 3 → ℤ),
      (G.card : ℝ) * ((N ^ (-c')) ^ 2 * ((N ^ (-c')) ^ d * N ^ (-ε₂))) ≤
        (ν.prod volume).real (groupSet E₀ δ (N ^ (-c')) K₂ y Y) ∧
      (ν.prod volume) (groupSet E₀ δ (N ^ (-c')) K₂ y Y ∩
        {p | coefficientCode (N ^ (-c')) (coefVec β γ p.1) ∉ G}) ≤
        ENNReal.ofReal ((N ^ (-c')) ^ 2 * N ^ (-ηc)) := by
  classical
  set s := N ^ (-c') with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hN _
  have hK : 0 ≤ K := (abs_nonneg _).trans (hU.bound_F 0 0)
  set L := longLabels E₀ δ with hLdef
  have hLm : MeasurableSet L := measurableSet_longLabels hE₀ δ
  set Ea := E₀ ∩ L ×ˢ univ with hEadef
  have hEam : MeasurableSet Ea := hE₀.inter (hLm.prod MeasurableSet.univ)
  have hEaE : Ea ⊆ E := inter_subset_left.trans hE₀E
  have hEa01 : Ea ⊆ univ ×ˢ Icc (0 : ℝ) 1 := hEaE.trans hU.subset_E
  set GY : Set Ω := {l | ∀ i, ⌊y l i / s⌋ = Y i} with hGYdef
  have hGYm : MeasurableSet GY := measurableSet_group hU.measurable_y s Y
  set EY := groupSet E₀ δ s K₂ y Y with hEYdef
  have hEYm : MeasurableSet EY :=
    (measurableSet_pairGood hEam s K₂).inter (hGYm.prod MeasurableSet.univ)
  have hEY01 : EY ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun p hp => hEa01 hp.1.1
  have hEYsub : EY ⊆ (GY ∩ L) ×ˢ univ := fun p hp => ⟨⟨hp.2.1, hp.1.1.2.1⟩, trivial⟩
  have ha := measurable_coefVec hU.measurable_β hU.measurable_γ
  -- the group's long labels
  have hGL : ν (GY ∩ L) ≤ ENNReal.ofReal ((4 * K + 5) * (K * s ^ 2) / δ) := by
    refine le_ofReal_div_of_mul_le hδ ?_
    refine (duration_mul_le hE₀ (hGYm.inter hLm) fun l hl => hl.2).trans ?_
    refine mass_le_of_slices hE₀ (hE₀E.trans hU.subset_E) (hGYm.inter hLm) fun t _ => ?_
    refine le_trans (measure_mono ?_) (slice_group_le hU hs hs1 Y t)
    intro l hl
    exact ⟨hE₀E hl.1, hl.2.1⟩
  -- the auxiliary prior
  set κ : ENNReal := ENNReal.ofReal (1 / s ^ 2) with hκ
  set νY : Measure Ω := κ • ν.restrict (GY ∩ L) with hνY
  have hνYuniv : νY univ ≤ ENNReal.ofReal ((4 * K + 5) * K / δ) := by
    rw [hνY, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    calc κ * ν (GY ∩ L) ≤ κ * ENNReal.ofReal ((4 * K + 5) * (K * s ^ 2) / δ) := by gcongr
      _ = ENNReal.ofReal ((4 * K + 5) * K / δ) := by
          rw [hκ, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
  -- coefficient-ball caps
  have hball : ∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), s ≤ r →
      νY {l | coefVec β γ l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ ηc * r ^ d) := by
    intro b r hsr
    have hr0 : 0 < r := lt_of_lt_of_le hs0 hsr
    have hBm : MeasurableSet {l | coefVec β γ l ∈ Metric.ball b r} :=
      ha Metric.isOpen_ball.measurableSet
    have hcoef : 0 ≤ 4 * ((4 * K + 5) * K) / δ := by positivity
    by_cases hr4 : 4 * r ≤ 1
    · have hsub : ∀ l ∈ {l | coefVec β γ l ∈ Metric.ball b r},
          |β l - b 0| < r ∧ |γ l - b 1| < r := by
        intro l hl
        simp only [mem_setOf_eq, Metric.mem_ball, dist_eq_norm] at hl
        have h0 := PiLp.norm_apply_le (coefVec β γ l - b) 0
        have h1 := PiLp.norm_apply_le (coefVec β γ l - b) 1
        simp only [WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs] at h0 h1
        have e0 : (coefVec β γ l).ofLp 0 = β l := coefVec_zero β γ l
        have e1 : (coefVec β γ l).ofLp 1 = γ l := coefVec_one β γ l
        rw [e0] at h0; rw [e1] at h1
        exact ⟨lt_of_le_of_lt h0 hl, lt_of_le_of_lt h1 hl⟩
      have hS : ν ({l | coefVec β γ l ∈ Metric.ball b r} ∩ (GY ∩ L)) ≤
          ENNReal.ofReal (2 * (K * s ^ 2 * (4 * r) ^ d) / δ) := by
        refine le_ofReal_div_of_mul_le hδ ?_
        refine (duration_mul_le hE₀ (hBm.inter (hGYm.inter hLm)) fun l hl => hl.2.2).trans ?_
        refine mass_le_of_slices hE₀ (hE₀E.trans hU.subset_E) (hBm.inter (hGYm.inter hLm))
          fun t ht => ?_
        refine le_trans (measure_mono ?_) (slice_ball_le hU hs0 hs hsr hr4 Y ht (b 0) (b 1))
        intro l hl
        exact ⟨hE₀E hl.1, hl.2.2.1, hsub l hl.2.1⟩
      rw [hνY, Measure.smul_apply, Measure.restrict_apply hBm, smul_eq_mul]
      calc κ * ν ({l | coefVec β γ l ∈ Metric.ball b r} ∩ (GY ∩ L))
          ≤ κ * ENNReal.ofReal (2 * (K * s ^ 2 * (4 * r) ^ d) / δ) := by gcongr
        _ = ENNReal.ofReal (2 * (K * (4 * r) ^ d) / δ) := by
            rw [hκ, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; field_simp
        _ ≤ ENNReal.ofReal (N ^ ηc * r ^ d) := by
            apply ENNReal.ofReal_le_ofReal
            have h4 : (4 * r) ^ d ≤ 4 * r ^ d := by
              rw [Real.mul_rpow (by norm_num) hr0.le]
              have : (4 : ℝ) ^ d ≤ 4 := by
                calc (4 : ℝ) ^ d ≤ 4 ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1.le
                  _ = 4 := Real.rpow_one 4
              exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hr0.le _)
            have hrd : 0 ≤ r ^ d := Real.rpow_nonneg hr0.le _
            calc 2 * (K * (4 * r) ^ d) / δ ≤ 2 * (K * (4 * r ^ d)) / δ := by gcongr
              _ = 8 * K / δ * r ^ d := by ring
              _ ≤ 4 * ((4 * K + 5) * K) / δ * r ^ d := by
                  apply mul_le_mul_of_nonneg_right _ hrd
                  apply div_le_div_of_nonneg_right _ hδ.le
                  nlinarith
              _ ≤ N ^ ηc * r ^ d := by gcongr
    · push_neg at hr4
      have hrd : (1 : ℝ) / 4 ≤ r ^ d := by
        calc (1 : ℝ) / 4 = (1 / 4) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (1 / 4) ^ d := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hd1.le
          _ ≤ r ^ d := Real.rpow_le_rpow (by norm_num) (by linarith) hd
      calc νY {l | coefVec β γ l ∈ Metric.ball b r} ≤ νY univ := measure_mono (subset_univ _)
        _ ≤ ENNReal.ofReal ((4 * K + 5) * K / δ) := hνYuniv
        _ ≤ ENNReal.ofReal (N ^ ηc * r ^ d) := by
            apply ENNReal.ofReal_le_ofReal
            calc (4 * K + 5) * K / δ = 4 * ((4 * K + 5) * K) / δ * (1 / 4) := by ring
              _ ≤ N ^ ηc * r ^ d := mul_le_mul n2 hrd (by norm_num) (by positivity)
  -- spacetime cells
  obtain ⟨Fs, hFs, hFsmem⟩ := spacetime_count (y := y) (K := K) (s := s) (K₂ := K₂)
    (B := K * s ^ (-d)) hK hs0 hK₂ (by positivity) hU.bound_β hU.bound_γ hU.bound_F hEam hEa01
    (fun t => by
      obtain ⟨C, hC, hCmem⟩ := hU.support t s hs hs1
      exact ⟨C, hC, fun l hl => hCmem l (hEaE hl)⟩) Y
  have hFscard : (Fs.card : ℝ) ≤ N ^ ηc * (N ^ (-c')) ^ (-1 - d) := by
    rw [← hsdef]
    have e : s ^ (-1 - d) = 1 / s * s ^ (-d) := by
      rw [show (-1 - d) = -1 + -d by ring, Real.rpow_add hs0, Real.rpow_neg_one, one_div]
    rw [e]
    have hsd : 0 ≤ s ^ (-d) := Real.rpow_nonneg hs0.le _
    calc (Fs.card : ℝ) ≤ (1 / s + 1) * (K₂ * ((4 * K + 3) * (K * s ^ (-d)))) := hFs
      _ ≤ (2 / s) * (K₂ * ((4 * K + 3) * (K * s ^ (-d)))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [show (2 : ℝ) / s = 1 / s + 1 / s by ring]
          gcongr
          rw [le_div_iff₀ hs0]; linarith
      _ = 2 * (K₂ * ((4 * K + 3) * K)) * (1 / s * s ^ (-d)) := by ring
      _ ≤ N ^ ηc * (1 / s * s ^ (-d)) := by gcongr
  -- the clustering
  obtain ⟨G, -, hGcard, hGleft⟩ := hHC Ω νY (coefVec β γ) EY Fs ha hEYm hEY01
    (fun l => (norm_coefVec_le hU.bound_β hU.bound_γ l).trans n1)
    (hνYuniv.trans (ENNReal.ofReal_le_ofReal (by
      calc (4 * K + 5) * K / δ ≤ 4 * ((4 * K + 5) * K) / δ := by
            apply div_le_div_of_nonneg_right _ hδ.le; nlinarith
        _ ≤ N ^ ηc := n2)))
    hFscard
    (fun l t hlt => by
      have hx : coefVec β γ l 0 + t * coefVec β γ l 1 + t ^ 2 * coefVec β γ l 2 =
          xbar β γ l t := by simp [xbar]
      rw [hx]
      exact hFsmem l t hlt.1 hlt.2.1)
    hball
  -- back to `ν`
  have hprod : νY.prod (volume : Measure ℝ) =
      κ • (ν.prod (volume : Measure ℝ)).restrict ((GY ∩ L) ×ˢ univ) := by
    have h := Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) (GY ∩ L) univ
    rw [Measure.restrict_univ] at h
    rw [hνY, Measure.prod_smul_left, h]
  have hEYeq : EY ∩ (GY ∩ L) ×ˢ univ = EY := inter_eq_left.mpr hEYsub
  have hcodem : MeasurableSet {p : Ω × ℝ | coefficientCode s (coefVec β γ p.1) ∉ G} :=
    ((measurable_coefficientCode s).comp (ha.comp measurable_fst)) G.measurableSet.compl
  have hs2 : 0 < s ^ 2 := by positivity
  refine ⟨G, ?_, ?_⟩
  · have hreal : (νY.prod (volume : Measure ℝ)).real EY =
        1 / s ^ 2 * (ν.prod (volume : Measure ℝ)).real EY := by
      rw [measureReal_def, hprod, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hEYm,
        hEYeq, ENNReal.toReal_mul, hκ, ENNReal.toReal_ofReal (by positivity), measureReal_def]
    have hexp : N ^ (-c' * d - ε₂) = s ^ d * N ^ (-ε₂) := by
      rw [show -c' * d - ε₂ = -c' * d + -ε₂ by ring, Real.rpow_add hN, Real.rpow_mul hN.le]
    rw [hreal, hexp] at hGcard
    have hpos : 0 < s ^ d * N ^ (-ε₂) := by positivity
    rw [le_div_iff₀ hpos] at hGcard
    calc (G.card : ℝ) * (s ^ 2 * (s ^ d * N ^ (-ε₂)))
        = s ^ 2 * ((G.card : ℝ) * (s ^ d * N ^ (-ε₂))) := by ring
      _ ≤ s ^ 2 * (1 / s ^ 2 * (ν.prod volume).real EY) := by gcongr
      _ = (ν.prod volume).real EY := by field_simp
  · have h1 : ((νY.prod (volume : Measure ℝ)).restrict EY)
          {p | coefficientCode s (coefVec β γ p.1) ∉ G} =
        κ * (ν.prod volume) (EY ∩ {p | coefficientCode s (coefVec β γ p.1) ∉ G}) := by
      rw [Measure.restrict_apply hcodem, hprod, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply (hcodem.inter hEYm), inter_comm _ EY, inter_assoc,
        inter_comm _ ((GY ∩ L) ×ˢ univ), ← inter_assoc, hEYeq]
    rw [h1] at hGleft
    have hκs : ENNReal.ofReal (s ^ 2) * κ = 1 := by
      rw [hκ, ← ENNReal.ofReal_mul hs2.le, show s ^ 2 * (1 / s ^ 2) = 1 by field_simp,
        ENNReal.ofReal_one]
    calc (ν.prod volume) (EY ∩ {p | coefficientCode s (coefVec β γ p.1) ∉ G})
        = ENNReal.ofReal (s ^ 2) * κ *
          (ν.prod volume) (EY ∩ {p | coefficientCode s (coefVec β γ p.1) ∉ G}) := by
          rw [hκs, one_mul]
      _ = ENNReal.ofReal (s ^ 2) * (κ *
          (ν.prod volume) (EY ∩ {p | coefficientCode s (coefVec β γ p.1) ∉ G})) := by ring
      _ ≤ ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (N ^ (-ηc)) := by gcongr
      _ = ENNReal.ofReal (s ^ 2 * N ^ (-ηc)) := (ENNReal.ofReal_mul hs2.le).symm

end Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

end
