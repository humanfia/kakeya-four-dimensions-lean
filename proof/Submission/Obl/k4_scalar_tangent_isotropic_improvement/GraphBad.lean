import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphCore
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.BadCells
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.BadMass

set_option linter.unusedVariables false

/-!
# Bad frozen cells carry little mass

`frozen_bad_mass_le` instantiates the Kakeya contradiction `bad_mass_le` (`n = 3`) on o092's
frozen data: fine cubes of side `b` (`cellSet b`), coarse cubes of side `w₀ = M₀ b`
(`cubeOf`, `cellIdx_coarse`), tangent lines at the clamped central times `cubeTime`, the far-point
physical map `physIn E₁`, tube containment and direction closeness from `GraphGeometry`, bad cells
from `pi_det_lower`, and the visited-cube count `card_visited_le`.
-/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Submission.Lib.K4ContinuousKakeya
open scoped ENNReal NNReal

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The coarse cube (side `M₀ w`) containing the fine cube (side `w`) of index `q`. -/
def cubeOf (M₀ : ℕ) (q : Fin 3 → ℤ) : Fin 3 → ℤ := fun e => q e / (M₀ : ℤ)

lemma cellIdx_coarse {w : ℝ} (hw : 0 < w) (M₀ : ℕ) (x : E3) :
    cellIdx ((M₀ : ℝ) * w) x = cubeOf M₀ (cellIdx w x) := by
  funext e
  simp only [cellIdx, cubeOf]
  rw [← Int.floor_div_natCast, div_div, mul_comm w]

/-- The clamped central time of a coarse cube. -/
def cubeTime (w₀ : ℝ) (Q : Fin 3 → ℤ) : ℝ := max 0 (min 1 (((Q 0 : ℝ) + 1 / 2) * w₀))

lemma abs_cubeTime_le (w₀ : ℝ) (Q : Fin 3 → ℤ) : |cubeTime w₀ Q| ≤ 2 := by
  unfold cubeTime
  rw [abs_le]; constructor
  · have := le_max_left (0 : ℝ) (min 1 (((Q 0 : ℝ) + 1 / 2) * w₀)); linarith
  · exact max_le (by norm_num) ((min_le_left _ _).trans (by norm_num))

lemma abs_sub_cubeTime_le {w₀ t : ℝ} (hw₀ : 0 < w₀) {Q : Fin 3 → ℤ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hQ : ⌊t / w₀⌋ = Q 0) : |t - cubeTime w₀ Q| ≤ w₀ := by
  have h1 := Int.floor_le (t / w₀); have h2 := Int.lt_floor_add_one (t / w₀)
  rw [hQ, le_div_iff₀ hw₀] at h1
  rw [hQ, div_lt_iff₀ hw₀] at h2
  unfold cubeTime
  rw [abs_le]
  constructor
  · -- t - cubeTime ≥ -w₀
    have : max 0 (min 1 (((Q 0 : ℝ) + 1 / 2) * w₀)) ≤ t + w₀ := by
      apply max_le (by linarith [ht.1])
      exact (min_le_right _ _).trans (by nlinarith)
    linarith
  · -- t - cubeTime ≤ w₀
    have : t - w₀ ≤ max 0 (min 1 (((Q 0 : ℝ) + 1 / 2) * w₀)) := by
      refine le_trans ?_ (le_max_right _ _)
      apply le_min (by linarith [ht.2])
      nlinarith
    linarith

/-- **Bad frozen cells carry little mass.** On the incidences `E₁` of the frozen data (times in
`[0,1]`, coefficients `≤ H`) with an incidence law `inc` comparable to `θ × time` on `E₁`, a finite
family of occupied fine cubes of side `b` none of which has a plane through the origin capturing
more than `1 - c` of its unit lifted directions within `ε` carries total mass at most
`3/η · H τ₀ · mc · θ(univ)`, `mc` the number of coarse cubes (side `w₀ = M₀ b`) a trajectory visits,
provided the Kakeya constant inequality `hcontr` holds. -/
theorem frozen_bad_mass_le {C : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK 3 C)
    (θ : Measure (ℕ × (Fin 5 → ℝ))) [IsFiniteMeasure θ] (inc : Measure Inc) [IsFiniteMeasure inc]
    {E₁ : Set Inc} (hE₁ : MeasurableSet E₁) {H : ℝ} (hH : 1 ≤ H)
    (hle : inc ≤ H.toNNReal • (θ.prod volume).restrict E₁)
    (hge : (θ.prod volume).restrict E₁ ≤ H.toNNReal • inc)
    (hE₁H : ∀ p ∈ E₁, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) (hw₀1 : (M₀ : ℝ) * b ≤ 1)
    (BadF : Finset (Fin 3 → ℤ)) (hocc : ∀ q ∈ BadF, ∃ p ∈ E₁, physOf p ∈ cellSet b q)
    {ε c η : ℝ} (τ₀ : ℝ≥0) (hτ₀ : 0 < τ₀) (hε : 0 < ε) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hp₀ : 2 * ((3 : ℕ) : ℝ) * η ≤ c ^ 2)
    (hbad : ∀ q ∈ BadF, ∀ ν : E3, ‖ν‖ = 1 →
      inc {ω | ω ∈ physIn E₁ ⁻¹' cellSet b q ∧ |inner ℝ ν (unitOf ω)| < ε} ≤
        ENNReal.ofReal (1 - c) * inc (physIn E₁ ⁻¹' cellSet b q))
    (S₀ : ℕ) (hS₀ : ∀ Q, (BadF.filter (fun q => cubeOf M₀ q = Q)).card ≤ S₀)
    (hβ' : 0 < ε ^ 2 - (Nat.factorial 3) * (3 : ℕ) * (4 * H * ((M₀ : ℝ) * b)))
    (hcontr : (S₀ : ℝ) ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1)) *
        (2 ^ (3 : ℕ) * C * (2 * b + H * ((M₀ : ℝ) * b) ^ 2) ^ (3 : ℕ) / b ^ 3 *
          ((H.toNNReal * b.toNNReal : ℝ≥0) : ℝ) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1)) /
          ((ε ^ 2 - (Nat.factorial 3) * (3 : ℕ) * (4 * H * ((M₀ : ℝ) * b))) *
            (c ^ 2 - (3 : ℕ) * η)) ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1)) *
          ((H.toNNReal : ℝ) / τ₀) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1))) ≤
        (1 / 2) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1))) :
    ∑ q ∈ BadF, (inc (physIn E₁ ⁻¹' cellSet b q)).toReal ≤
      3 / η * (H.toNNReal * τ₀ *
        (((⌊1 / ((M₀ : ℝ) * b)⌋₊ + 1) * (2 * (⌈H⌉₊ + 1) + 1) * (2 * (⌈3 * H⌉₊ + 1) + 1) : ℕ) *
          (θ Set.univ).toReal)) := by
  classical
  set w₀ : ℝ := (M₀ : ℝ) * b with hw₀
  have hw₀pos : 0 < w₀ := mul_pos (by exact_mod_cast hM₀) hb
  have hH0 : 0 ≤ H := by linarith
  -- occupied bad cells have nonnegative time index
  have hq0 : ∀ q ∈ BadF, 0 ≤ q 0 := by
    intro q hq
    obtain ⟨p, hpE, hpq⟩ := hocc q hq
    have h1 := (time_mem_of_mem_cellSet hb hpq).2
    have h2 := (hE₁H p hpE).1.1
    by_contra hneg
    have hneg' : q 0 + 1 ≤ 0 := by omega
    have : (q 0 : ℝ) + 1 ≤ 0 := by exact_mod_cast hneg'
    nlinarith
  set 𝒬 : Finset (Fin 3 → ℤ) := BadF.image (cubeOf M₀) with h𝒬
  set cells : (Fin 3 → ℤ) → Finset (Fin 3 → ℤ) := fun Q => BadF.filter (fun q => cubeOf M₀ q = Q)
    with hcells
  have hmemcells : ∀ Q, ∀ q ∈ cells Q, q ∈ BadF ∧ cubeOf M₀ q = Q := fun Q q hq =>
    Finset.mem_filter.mp hq
  have hK : (0 : ℝ≥0) < H.toNNReal := by simp; linarith
  have hb' : (0 : ℝ≥0) < b.toNNReal := by simpa using hb
  have hmain := bad_mass_le (n := 3) (by norm_num) hC0 hC θ inc hE₁ H.toNNReal hle hge
    (physIn E₁) (measurable_physIn hE₁) unitOf (fun ω => (norm_unitOf ω).le) 𝒬 cells
    (cellSet b) (measurableSet_cellSet b)
    (by
      intro Q _ q _ q' _ hqq'
      rw [Function.onFun, Set.disjoint_iff]
      intro x ⟨hx, hx'⟩
      exact hqq' (hx.symm.trans hx'))
    (4 + 10 * H)
    (by
      intro Q _ q hq x hx
      obtain ⟨p, hpE, hpq⟩ := hocc q (hmemcells Q q hq).1
      have h1 : ‖physOf p‖ ≤ 2 + 10 * H := norm_physOf_le (hE₁H p hpE).2
        (by rw [abs_le]; constructor <;> linarith [(hE₁H p hpE).1.1, (hE₁H p hpE).1.2])
      have h2 := norm_sub_lt_of_mem_cellSet hb hx hpq
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖x‖ ≤ ‖x - physOf p‖ + ‖physOf p‖ := norm_le_norm_sub_add x _
        _ ≤ 2 * b + (2 + 10 * H) := by linarith
        _ ≤ 4 + 10 * H := by linarith)
    b.toNNReal hb'
    (by
      intro Q _ q hq l
      have hq0' := hq0 q (hmemcells Q q hq).1
      calc volume {t : ℝ | physIn E₁ (l, t) ∈ cellSet b q}
          ≤ volume {t : ℝ | physOf (l, t) ∈ cellSet b q} := by
            apply measure_mono
            intro t ht
            exact (physIn_mem_cellSet hb hq0' ht).2
        _ ≤ ENNReal.ofReal b := volume_time_section_le hb q l
        _ = (b.toNNReal : ℝ≥0∞) := by simp [ENNReal.ofReal])
    (fun Q => tangentBase H (cubeTime w₀ Q)) (fun Q => tangentDir (cubeTime w₀ Q))
    (fun Q => measurable_tangentBase H _) (fun Q => measurable_tangentDir _)
    (fun Q l => norm_tangentDir _ l) (fun Q l => norm_tangentBase_le hH0 (abs_cubeTime_le w₀ Q) l)
    (r := 2 * b + H * w₀ ^ 2) (by positivity)
    (by
      intro Q hQ q hq ω hω x hx
      have hq0' := hq0 q (hmemcells Q q hq).1
      obtain ⟨hωE, hωq⟩ := physIn_mem_cellSet hb hq0' hω
      have hcube : ⌊ω.2 / w₀⌋ = Q 0 := by
        have := cellIdx_coarse hb M₀ (physOf ω)
        have hc : cellIdx b (physOf ω) = q := hωq
        rw [hc, (hmemcells Q q hq).2] at this
        have h0 := congrFun this 0
        simpa [cellIdx, physOf_apply, hw₀] using h0
      exact mem_tube_tangent_of_cell hb (hE₁H ω hωE).2 hωq
        (abs_sub_cubeTime_le hw₀pos (hE₁H ω hωE).1 hcube) le_rfl hx)
    (4 * H * w₀)
    (by
      intro Q hQ q hq ω hω
      have hq0' := hq0 q (hmemcells Q q hq).1
      obtain ⟨hωE, hωq⟩ := physIn_mem_cellSet hb hq0' hω
      have hcube : ⌊ω.2 / w₀⌋ = Q 0 := by
        have := cellIdx_coarse hb M₀ (physOf ω)
        have hc : cellIdx b (physOf ω) = q := hωq
        rw [hc, (hmemcells Q q hq).2] at this
        have h0 := congrFun this 0
        simpa [cellIdx, physOf_apply, hw₀] using h0
      calc ‖unitOf ω - tangentDir (cubeTime w₀ Q) ω.1‖ ≤ 4 * H * |ω.2 - cubeTime w₀ Q| :=
            norm_unitOf_sub_tangentDir_le (hE₁H ω hωE).2
        _ ≤ 4 * H * w₀ := by
            gcongr
            exact abs_sub_cubeTime_le hw₀pos (hE₁H ω hωE).1 hcube)
    S₀ (fun Q _ => hS₀ Q) (b ^ 3) (by positivity)
    (by
      intro Q _ q _
      rw [volume_cellSet hb, ← ENNReal.ofReal_pow hb.le])
    (ε ^ 2) (c ^ 2) η τ₀ hτ₀ hη hη4 hp₀ hK (by simpa using hβ')
    (by
      intro Q _ q hq
      have := pi_det_lower inc ((measurable_physIn hE₁) (measurableSet_cellSet b q)) unitOf
        continuous_unitOf.measurable norm_unitOf hε hc hc1 (hbad q (hmemcells Q q hq).1)
      simpa using this)
    (by simpa using hcontr)
    ((⌊1 / ((M₀ : ℝ) * b)⌋₊ + 1) * (2 * (⌈H⌉₊ + 1) + 1) * (2 * (⌈3 * H⌉₊ + 1) + 1))
    (by
      intro l
      -- a visited cube comes from an incidence of `E₁` in one of its cells
      have hvis : ∀ Q ∈ 𝒬.filter (fun Q => 0 < duration
          (physIn E₁ ⁻¹' (⋃ c ∈ cells Q, cellSet b c) ∩ E₁) l),
          ∃ t ∈ Set.Icc (0 : ℝ) 1, (l, t) ∈ E₁ ∧ cellIdx w₀ (physOf (l, t)) = Q := by
        intro Q hQ
        have hpos := (Finset.mem_filter.mp hQ).2
        obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hpos.ne'
        obtain ⟨htΦ, htE⟩ := ht
        simp only [Set.mem_preimage, Set.mem_iUnion] at htΦ
        obtain ⟨q, hq, hqt⟩ := htΦ
        have hq0' := hq0 q (hmemcells Q q hq).1
        obtain ⟨_, hphys⟩ := physIn_mem_cellSet hb hq0' hqt
        refine ⟨t, (hE₁H _ htE).1, htE, ?_⟩
        rw [hw₀, cellIdx_coarse hb M₀]
        have hc : cellIdx b (physOf (l, t)) = q := hphys
        rw [hc, (hmemcells Q q hq).2]
      by_cases hempty : 𝒬.filter (fun Q => 0 < duration
          (physIn E₁ ⁻¹' (⋃ c ∈ cells Q, cellSet b c) ∩ E₁) l) = ∅
      · rw [hempty, Finset.card_empty]; exact Nat.zero_le _
      · obtain ⟨Q₀, hQ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨t₀, _, ht₀E, _⟩ := hvis Q₀ hQ₀
        exact card_visited_le hw₀pos l (hE₁H _ ht₀E).2 _ (fun Q hQ => by
          obtain ⟨t, ht, _, htQ⟩ := hvis Q hQ
          exact ⟨t, ht, htQ⟩))
  have hfib : ∑ Q ∈ 𝒬, ∑ q ∈ cells Q, (inc (physIn E₁ ⁻¹' cellSet b q)).toReal =
      ∑ q ∈ BadF, (inc (physIn E₁ ⁻¹' cellSet b q)).toReal :=
    Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem _ hq) _
  rw [← hfib]
  exact hmain

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
