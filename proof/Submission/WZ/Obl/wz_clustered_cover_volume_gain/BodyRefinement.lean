-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.BodyRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AverageLevel

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

def bodyCount {n : ℕ} (Y : Fin n → Set Space) (p : Space) : ℝ :=
  ({i : Fin n | p ∈ Y i}.ncard : ℝ)

theorem bodyCount_eq_sum {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    bodyCount Y p = ∑ i, (Y i).indicator (fun _ => (1 : ℝ)) p := by
  classical
  simp [bodyCount, ncard_eq_toFinset_card', Set.indicator, Finset.sum_boole]

theorem measurable_bodyCount {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) : Measurable (bodyCount Y) := by
  classical
  have he : bodyCount Y = fun p => ∑ i, (Y i).indicator (fun _ => (1 : ℝ)) p :=
    funext (bodyCount_eq_sum Y)
  rw [he]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hY i))

theorem bodyCount_inter {n : ℕ} (Y : Fin n → Set Space) (A : Set Space) (p : Space)
    [Decidable (p ∈ A)] :
    bodyCount (fun i => Y i ∩ A) p = if p ∈ A then bodyCount Y p else 0 := by
  classical
  by_cases hp : p ∈ A <;> simp [bodyCount, hp]

theorem bodyCount_diff {n : ℕ} (Y : Fin n → Set Space) (A : Set Space) (p : Space)
    [Decidable (p ∈ A)] :
    bodyCount (fun i => Y i \ A) p = if p ∈ A then 0 else bodyCount Y p := by
  classical
  by_cases hp : p ∈ A <;> simp [bodyCount, hp]

/-- A bound on every dense lower multiplicity level gives a pointwise upper bound
after retaining half the shading mass. -/
theorem low_body_count_refinement {n : ℕ} {Y : Fin n → Set Space}
    (hYm : ∀ i, MeasurableSet (Y i)) (hYfinite : ∑ i, volume (Y i) ≠ ⊤)
    {R : ENNReal} {K : ℝ} (hK : 0 < K)
    (hmass : 2 * R ≤ ∑ i, volume (Y i))
    (H : ∀ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) → (∀ i, Z i ⊆ Y i) →
      R ≤ ∑ i, volume (Z i) → ∀ M : ℝ, 0 ≤ M →
      (∀ p ∈ ⋃ i, Z i, M ≤ bodyCount Z p) → M ≤ K) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ 2 * K := by
  classical
  let A : Set Space := {p | bodyCount Y p ≤ 2 * K}
  have hA : MeasurableSet A := measurableSet_le (measurable_bodyCount hYm) measurable_const
  let Z : Fin n → Set Space := fun i => Y i ∩ A
  let W : Fin n → Set Space := fun i => Y i \ A
  have hWsmall : ∑ i, volume (W i) < R := by
    apply lt_of_not_ge
    intro hWmass
    have hh := H W (fun i => (hYm i).diff hA) (fun _ => sdiff_subset) hWmass
      (2 * K) (by positivity) ?_
    · linarith
    · intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      have hpA : p ∉ A := hi.2
      have hpK : 2 * K < bodyCount Y p := lt_of_not_ge hpA
      simpa only [W, bodyCount_diff, ite_eq_right hpA] using hpK.le
  have hR : R ≤ (1 / 2 : ENNReal) * ∑ i, volume (Y i) := by
    calc
      R = (1 / 2 : ENNReal) * (2 * R) := by
        rw [one_div, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ _ := mul_le_mul' le_rfl hmass
  have hZle : ∑ i, volume (Z i) ≤ ∑ i, volume (Y i) :=
    Finset.sum_le_sum fun _ _ => measure_mono inter_subset_left
  have hWle : ∑ i, volume (W i) ≤ ∑ i, volume (Y i) :=
    Finset.sum_le_sum fun _ _ => measure_mono sdiff_subset
  have hZfinite := ne_top_of_le_ne_top hYfinite hZle
  have hWfinite := ne_top_of_le_ne_top hYfinite hWle
  have hsplit : (∑ i, volume (Z i)) + (∑ i, volume (W i)) = ∑ i, volume (Y i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => measure_inter_add_sdiff (Y i) hA)
  have hhalf : (1 / 2 : ENNReal) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) := by
    have hhalffinite : (1 / 2 : ENNReal) * ∑ i, volume (Y i) ≠ ⊤ := by finiteness
    apply (ENNReal.toReal_le_toReal hhalffinite hZfinite).mp
    have hh := ENNReal.toReal_mono hhalffinite (hWsmall.le.trans hR)
    have hs := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add hZfinite hWfinite] at hs
    norm_num only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat] at hh ⊢
    linarith
  refine ⟨Z, fun i => ⟨(hYm i).inter hA, inter_subset_left⟩, hhalf, ?_⟩
  intro p
  dsimp only [Z]
  rw [bodyCount_inter]
  split_ifs with hp
  · exact hp
  · positivity

/-- The normalized convex-body estimate can be used as a refinement with bounded
pointwise multiplicity, while keeping half of the original shading mass. -/
theorem convex_body_refinement {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (B w m D : ℝ),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m → 0 < D →
      1536 * δ ^ η ≤ D → BodyGeometry U x δ B w → (∀ i, U i ⊆ ball (0 : Space) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      ENNReal.ofReal (D * n * w) ≤ ∑ i, volume (Y i) → BodyConvexCount U w m →
      ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ C * δ ^ (-ε) * D⁻¹ * B ^ (-ω) * m ^ (1 + σ / 2) * w ^ (-σ / 2) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    convex_body_multiplicity_average hσ hσhalf hω hE ε hε
  refine ⟨4 * C, η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x B w m D hn hcount hδB hw hm hD htD hG hball hYm hYU hden hK
  have hB : 0 < B := hδ.trans_le hδB
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  let K := C * δ ^ (-ε) * (D / 2)⁻¹ * B ^ (-ω) * m ^ (1 + σ / 2) * w ^ (-σ / 2)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hYfinite : ∑ i, volume (Y i) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono (hYU i)).trans (hG.volume_bounds i).2)
  have hmass : 2 * ENNReal.ofReal ((D / 2) * n * w) ≤ ∑ i, volume (Y i) := by
    convert hden using 1
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  obtain ⟨Z, hZY, hZmass, hZcount⟩ := low_body_count_refinement hYm hYfinite hKpos hmass
    (fun Z hZm hZY hZden M hM hlevel => H δ hδ hδd n U Z x B w m (D / 2)
      hn hcount hδB hw hm (by positivity) (by linarith) hG hball hZm
      (fun i => (hZY i).trans (hYU i)) hZden hK M hM hlevel)
  refine ⟨Z, hZY, hZmass, fun p => (hZcount p).trans_eq ?_⟩
  dsimp only [K]
  rw [inv_div]
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
