/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/GML3.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/GML3.lean, commit2b232aca. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Group3
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Jitter3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The three-dimensional matching lemma (GML3)

Adapted from LOT tree g-oai-074, o227 (`k4_horizontal_three_projection_wide_return`), session
x0788, branch x0788, commit 0d039ae5, file `MatchGML.lean` (the one-dimensional general matching
lemma): bins of ten coefficients instead of three, base points in `EuclideanSpace ℝ (Fin 3)` with
the cube jitter of `Match3/Jitter3`, closeness on the ball of radius `1/4`, and the frozen
two-colour matching entering through accepted o112 (`Match3/Sheets3`, `Match3/Group3`).
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open MeasureTheory

/-- The admissible bin offsets. -/
def offs3 : Finset (Fin 10 → ℤ) := Fintype.piFinset (fun _ : Fin 10 => Finset.Icc (-2 : ℤ) 2)

lemma card_offs3 : offs3.card = 9765625 := by
  unfold offs3; rw [Fintype.card_piFinset]; simp

lemma bin_diff_mem_offs3 {M : ℝ} (hM : 0 < M) (c c' : Fin 10 → ℝ)
    (h : cnorm3 (c - c') < 2 * M) : binOf3 M c' - binOf3 M c ∈ offs3 := by
  unfold offs3
  rw [Fintype.mem_piFinset]
  intro k
  have hk : |c k - c' k| < 2 * M := lt_of_le_of_lt (by simpa using abs_le_cnorm3 (c - c') k) h
  rw [abs_lt] at hk
  have e1 := Int.floor_le (c k / M)
  have e2 := Int.lt_floor_add_one (c k / M)
  have e3 := Int.floor_le (c' k / M)
  have e4 := Int.lt_floor_add_one (c' k / M)
  have d1 : c' k / M - c k / M < 2 := by
    rw [← sub_div, div_lt_iff₀ hM]; linarith
  have d2 : -2 < c' k / M - c k / M := by
    rw [← sub_div, lt_div_iff₀ hM]; linarith
  simp only [Pi.sub_apply, binOf3, Finset.mem_Icc]
  constructor
  · have : ((⌊c' k / M⌋ - ⌊c k / M⌋ : ℤ) : ℝ) > -3 := by push_cast; linarith
    have : (⌊c' k / M⌋ - ⌊c k / M⌋ : ℤ) > -3 := by exact_mod_cast this
    omega
  · have : ((⌊c' k / M⌋ - ⌊c k / M⌋ : ℤ) : ℝ) < 3 := by push_cast; linarith
    have : (⌊c' k / M⌋ - ⌊c k / M⌋ : ℤ) < 3 := by exact_mod_cast this
    omega

section Scale

variable {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
  [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]

/-- The pairs at dyadic scale `M`. -/
def bandSet3 (M : ℝ) (c₁ : ι₁ → Fin 10 → ℝ) (c₂ : ι₂ → Fin 10 → ℝ) : Set ((ι₁ × ι₂) × E3) :=
  {p | M ≤ cnorm3 (c₁ p.1.1 - c₂ p.1.2) ∧ cnorm3 (c₁ p.1.1 - c₂ p.1.2) < 2 * M}

/-- One dyadic scale. -/
theorem scale_le3 {d η N₀ : ℝ} (hQ : MatchQ3 d η N₀) (hη : 0 < η)
    (c₁ : ι₁ → Fin 10 → ℝ) (c₂ : ι₂ → Fin 10 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
    (Q : Measure ((ι₁ × ι₂) × E3)) [IsFiniteMeasure Q]
    {δ M A : ℝ} (hδ : 0 < δ) (hM : 0 < M) (hN : N₀ ≤ M / δ) (hA1 : 1 ≤ A)
    (hA : A ≤ (M / δ) ^ η)
    (hT₁ : ∀ i, 0 ≤ T₁ i) (hT₂ : ∀ j, 0 ≤ T₂ j)
    (hm₁ : ∀ i (E : Set E3), MeasurableSet E →
      Q {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₁ i) * volume E)
    (hm₂ : ∀ j (E : Set E3), MeasurableSet E →
      Q {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₂ j) * volume E)
    (hc₁ : ∀ r : Fin 10 → ℝ,
      ((Finset.univ.filter (fun i => ∀ k, |c₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d)
    (hc₂ : ∀ r : Fin 10 → ℝ,
      ((Finset.univ.filter (fun j => ∀ k, |c₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d)
    (hae : ∀ᵐ p ∂Q, ‖p.2‖ ≤ 1 / 2 ∧
      |q3E (c₁ p.1.1) p.2 - q3E (c₂ p.1.2) p.2| ≤ 30 * δ) :
    Q (bandSet3 M c₁ c₂) ≤
      ENNReal.ofReal (9765625 * (A * (M / δ) ^ (-η)) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
  classical
  set θ := A * (M / δ) ^ (-η) with hθ
  have hθnn : 0 ≤ θ := mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt (div_pos hM hδ)) _)
  set img := Finset.univ.image (fun i => binOf3 M (c₁ i)) with himg
  let W₁ : (Fin 10 → ℤ) → ℝ := fun β => ∑ i ∈ Finset.univ.filter (fun i => binOf3 M (c₁ i) = β), T₁ i
  let W₂ : (Fin 10 → ℤ) → ℝ := fun γ => ∑ j ∈ Finset.univ.filter (fun j => binOf3 M (c₂ j) = γ), T₂ j
  have hW₁nn : ∀ β, 0 ≤ W₁ β := fun β => Finset.sum_nonneg (fun i _ => hT₁ i)
  have hW₂nn : ∀ γ, 0 ≤ W₂ γ := fun γ => Finset.sum_nonneg (fun j _ => hT₂ j)
  -- the band is covered by the groups
  have hcover : bandSet3 M c₁ c₂ ⊆
      ⋃ β ∈ img, ⋃ δb ∈ offs3, (groupSet3 M c₁ c₂ β δb ∩ farSet3 M c₁ c₂) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    refine ⟨binOf3 M (c₁ p.1.1), by simp [himg], binOf3 M (c₂ p.1.2) - binOf3 M (c₁ p.1.1),
      bin_diff_mem_offs3 hM _ _ h2, ⟨rfl, by simp⟩, h1⟩
  have hgroup : ∀ β δb, δb ∈ offs3 →
      Q (groupSet3 M c₁ c₂ β δb ∩ farSet3 M c₁ c₂) ≤ ENNReal.ofReal (θ * (W₁ β + W₂ (β + δb))) := by
    intro β δb hδb
    have hδb' : ∀ k, |δb k| ≤ 2 := by
      intro k
      have := (Fintype.mem_piFinset.mp hδb) k
      rw [Finset.mem_Icc] at this
      rw [abs_le]; exact this
    exact group_le hQ hη c₁ c₂ T₁ T₂ Q hδ hM hN hA1 hA hT₁ hT₂ hm₁ hm₂ hc₁ hc₂ hae β δb hδb'
  -- sum the group bounds
  have hsumW₁ : ∑ β ∈ img, W₁ β = ∑ i, T₁ i := by
    rw [himg]
    exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) T₁
  have hsumW₂ : ∀ δb, ∑ β ∈ img, W₂ (β + δb) ≤ ∑ j, T₂ j := by
    intro δb
    have himgW : ∑ β ∈ img, W₂ (β + δb) = ∑ γ ∈ img.image (fun β => β + δb), W₂ γ :=
      (Finset.sum_image (s := img) (g := fun β : Fin 10 → ℤ => β + δb) (f := W₂)
        (fun x _ y _ hxy => by simpa using hxy)).symm
    rw [himgW]
    set img₂ := Finset.univ.image (fun j => binOf3 M (c₂ j))
    calc ∑ γ ∈ img.image (fun β => β + δb), W₂ γ
        ≤ ∑ γ ∈ img.image (fun β => β + δb) ∪ img₂, W₂ γ :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun γ _ _ => hW₂nn γ)
      _ = ∑ γ ∈ img₂, W₂ γ := by
          refine (Finset.sum_subset Finset.subset_union_right ?_).symm
          intro γ _ hγ
          apply Finset.sum_eq_zero
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exfalso; apply hγ; rw [← hj]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
      _ = ∑ j, T₂ j :=
          Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem _ hj) T₂
  calc Q (bandSet3 M c₁ c₂)
      ≤ Q (⋃ β ∈ img, ⋃ δb ∈ offs3, (groupSet3 M c₁ c₂ β δb ∩ farSet3 M c₁ c₂)) := measure_mono hcover
    _ ≤ ∑ β ∈ img, Q (⋃ δb ∈ offs3, (groupSet3 M c₁ c₂ β δb ∩ farSet3 M c₁ c₂)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ β ∈ img, ∑ δb ∈ offs3, Q (groupSet3 M c₁ c₂ β δb ∩ farSet3 M c₁ c₂) :=
        Finset.sum_le_sum (fun β _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ β ∈ img, ∑ δb ∈ offs3, ENNReal.ofReal (θ * (W₁ β + W₂ (β + δb))) :=
        Finset.sum_le_sum (fun β _ => Finset.sum_le_sum (fun δb hδb => hgroup β δb hδb))
    _ = ENNReal.ofReal (∑ β ∈ img, ∑ δb ∈ offs3, θ * (W₁ β + W₂ (β + δb))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro δb _; exact mul_nonneg hθnn (add_nonneg (hW₁nn _) (hW₂nn _))
        · intro β _
          exact Finset.sum_nonneg (fun δb _ => mul_nonneg hθnn (add_nonneg (hW₁nn _) (hW₂nn _)))
    _ ≤ ENNReal.ofReal (9765625 * θ * (∑ i, T₁ i + ∑ j, T₂ j)) := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : ∑ β ∈ img, ∑ δb ∈ offs3, θ * (W₁ β + W₂ (β + δb)) =
            θ * (∑ β ∈ img, ∑ δb ∈ offs3, W₁ β + ∑ β ∈ img, ∑ δb ∈ offs3, W₂ (β + δb)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
        have e2 : ∑ β ∈ img, ∑ δb ∈ offs3, W₁ β = 9765625 * ∑ i, T₁ i := by
          simp only [Finset.sum_const, card_offs3, nsmul_eq_mul]
          rw [← Finset.mul_sum, hsumW₁]; norm_num
        have e3 : ∑ β ∈ img, ∑ δb ∈ offs3, W₂ (β + δb) ≤ 9765625 * ∑ j, T₂ j := by
          rw [Finset.sum_comm]
          calc ∑ δb ∈ offs3, ∑ β ∈ img, W₂ (β + δb) ≤ ∑ δb ∈ offs3, ∑ j, T₂ j :=
                Finset.sum_le_sum (fun δb _ => hsumW₂ δb)
            _ = 9765625 * ∑ j, T₂ j := by
                simp only [Finset.sum_const, card_offs3, nsmul_eq_mul]; norm_num
        rw [e1, e2]
        have : θ * (9765625 * ∑ i, T₁ i + ∑ β ∈ img, ∑ δb ∈ offs3, W₂ (β + δb)) ≤
            θ * (9765625 * ∑ i, T₁ i + 9765625 * ∑ j, T₂ j) := by gcongr
        linarith

end Scale

/-- Moving a point of the closed ball of radius `1/4` by a vector of the cube `[0, w]³`, `w ≤ 1/8`,
stays in the closed ball of radius `1/2`. -/
theorem norm_add_cube_le {x u : E3} (hx : ‖x‖ ≤ 1 / 4) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 8)
    (hu : u ∈ cube w) : ‖x + u‖ ≤ 1 / 2 := by
  have hu' : ‖u‖ ≤ 1 / 4 := by
    rw [EuclideanSpace.norm_eq]
    have h : ∀ i, ‖u i‖ ^ 2 ≤ (1 / 8) ^ 2 := fun i => by
      rw [Real.norm_eq_abs, sq_abs]
      obtain ⟨h0, h1⟩ := hu i
      nlinarith
    calc Real.sqrt (∑ i, ‖u i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin 3, (1 / 8 : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h i)
      _ ≤ 1 / 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc ‖x + u‖ ≤ ‖x‖ + ‖u‖ := norm_add_le _ _
    _ ≤ 1 / 4 + 1 / 4 := add_le_add hx hu'
    _ = 1 / 2 := by norm_num

/-- A quadratic with coefficients bounded by `B` moves by at most `21 B w` under a shift by the
cube `[0, w]³`, at points of the unit ball. -/
theorem q3E_shift_le {a : Fin 10 → ℝ} {B : ℝ} (ha : ∀ k, |a k| ≤ B) {x u : E3}
    (hx : ‖x‖ ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hu : u ∈ cube w) :
    |q3E a (x + u) - q3E a x| ≤ 21 * B * w := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have hxk : ∀ k, |x k| ≤ 1 := fun k => abs_coord_le_one hx k
  have huk : ∀ k, 0 ≤ u k ∧ u k ≤ w := fun k => hu k
  have hs : ∀ k, (x + u) k = x k + u k := fun k => rfl
  simp only [q3E, q3, hs]
  have e : ∀ k l : Fin 3, |(x k + u k) * (x l + u l) - x k * x l| ≤ 3 * w := by
    intro k l
    have h1 := hxk k; have h2 := hxk l; obtain ⟨h3, h4⟩ := huk k; obtain ⟨h5, h6⟩ := huk l
    have : (x k + u k) * (x l + u l) - x k * x l = x k * u l + u k * x l + u k * u l := by ring
    rw [this]
    rw [abs_le] at h1 h2
    rw [abs_le]; constructor <;> nlinarith
  have e2 : ∀ k : Fin 3, |(x k + u k) ^ 2 - x k ^ 2| ≤ 3 * w := fun k => by
    have := e k k; simpa [sq] using this
  have e1 : ∀ k : Fin 3, |(x k + u k) - x k| ≤ w := fun k => by
    rw [add_sub_cancel_left, abs_of_nonneg (huk k).1]; exact (huk k).2
  have hdiff : (a 0 + a 1 * (x 0 + u 0) + a 2 * (x 1 + u 1) + a 3 * (x 2 + u 2) +
        a 4 * (x 0 + u 0) ^ 2 + a 5 * (x 1 + u 1) ^ 2 + a 6 * (x 2 + u 2) ^ 2 +
        a 7 * ((x 0 + u 0) * (x 1 + u 1)) + a 8 * ((x 0 + u 0) * (x 2 + u 2)) +
        a 9 * ((x 1 + u 1) * (x 2 + u 2))) -
      (a 0 + a 1 * x 0 + a 2 * x 1 + a 3 * x 2 + a 4 * x 0 ^ 2 + a 5 * x 1 ^ 2 + a 6 * x 2 ^ 2 +
        a 7 * (x 0 * x 1) + a 8 * (x 0 * x 2) + a 9 * (x 1 * x 2)) =
      a 1 * ((x 0 + u 0) - x 0) + a 2 * ((x 1 + u 1) - x 1) + a 3 * ((x 2 + u 2) - x 2) +
      a 4 * ((x 0 + u 0) ^ 2 - x 0 ^ 2) + a 5 * ((x 1 + u 1) ^ 2 - x 1 ^ 2) +
      a 6 * ((x 2 + u 2) ^ 2 - x 2 ^ 2) + a 7 * ((x 0 + u 0) * (x 1 + u 1) - x 0 * x 1) +
      a 8 * ((x 0 + u 0) * (x 2 + u 2) - x 0 * x 2) +
      a 9 * ((x 1 + u 1) * (x 2 + u 2) - x 1 * x 2) := by ring
  rw [hdiff]
  have t : ∀ (k : Fin 10) (m : ℝ) (c : ℝ), |m| ≤ c → |a k * m| ≤ B * c := fun k m c hm => by
    rw [abs_mul]; exact mul_le_mul (ha k) hm (abs_nonneg _) hB
  calc _ ≤ B * w + B * w + B * w + B * (3 * w) + B * (3 * w) + B * (3 * w) + B * (3 * w) +
        B * (3 * w) + B * (3 * w) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ (t 9 _ _ (e 1 2)))
        refine (abs_add_le _ _).trans (add_le_add ?_ (t 8 _ _ (e 0 2)))
        refine (abs_add_le _ _).trans (add_le_add ?_ (t 7 _ _ (e 0 1)))
        refine (abs_add_le _ _).trans (add_le_add ?_ (t 6 _ _ (e2 2)))
        refine (abs_add_le _ _).trans (add_le_add ?_ (t 5 _ _ (e2 1)))
        refine (abs_add_le _ _).trans (add_le_add ?_ (t 4 _ _ (e2 0)))
        refine (abs_add_le _ _).trans (add_le_add ?_ (t 3 _ _ (e1 2)))
        exact (abs_add_le _ _).trans (add_le_add (t 1 _ _ (e1 0)) (t 2 _ _ (e1 1)))
    _ = 21 * B * w := by ring

/-- **The three-dimensional matching lemma.**  Two finite families of three-variable quadratics
(coefficients `c₁ i`, `c₂ j`, bounded by `B`) with reference weights `T₁, T₂`, and a finite pair
law `P` on `(ι₁ × ι₂) × E3` with cube ceilings `≤ A T w³` at resolution `w`, closeness `≤ δ` at
base points of the ball of radius `1/4`, and jet counts `≤ A (M/δ)^d` at every scale `M ≥ M*`:
the pairs whose coefficient vectors differ by `≥ M*` carry at most
`A (M*/δ)^(-η) (Σ T₁ + Σ T₂)`. -/
theorem gml3 (hM : Matching) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (c₁ : ι₁ → Fin 10 → ℝ) (c₂ : ι₂ → Fin 10 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
      (P : Measure ((ι₁ × ι₂) × E3)) [IsFiniteMeasure P] (δ Mst A B w : ℝ),
      0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
      0 < w → w ≤ 1 / 8 → 42 * B * w ≤ δ →
      (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
      (∀ i k, |c₁ i k| ≤ B) → (∀ j k, |c₂ j k| ≤ B) →
      (∀ i (y : E3), P {p | p.1.1 = i ∧ y - p.2 ∈ cube w} ≤ ENNReal.ofReal (A * T₁ i * w ^ 3)) →
      (∀ j (y : E3), P {p | p.1.2 = j ∧ y - p.2 ∈ cube w} ≤ ENNReal.ofReal (A * T₂ j * w ^ 3)) →
      (∀ (r : Fin 10 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun i => ∀ k, |c₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d) →
      (∀ (r : Fin 10 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun j => ∀ k, |c₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d) →
      (∀ᵐ p ∂P, ‖p.2‖ ≤ 1 / 4 ∧ |q3E (c₁ p.1.1) p.2 - q3E (c₂ p.1.2) p.2| ≤ δ) →
      P {p | Mst ≤ cnorm3 (c₁ p.1.1 - c₂ p.1.2)} ≤
        ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
  obtain ⟨η₀, hη₀, N₀, hN₀, hQ⟩ := matchQ3_of_hyp hM hd0 hd1
  set ρ : ℝ := (2:ℝ) ^ (-η₀) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℝ := 9765625 / (1 - ρ) with hK
  have hKpos : 0 < K := div_pos (by norm_num) (by linarith)
  refine ⟨η₀ / 2, by positivity, max (max N₀ 1) (K ^ (2 / η₀)),
    le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
  intro ι₁ ι₂ _ _ _ _ _ _ c₁ c₂ T₁ T₂ P _ δ Mst A B w hδ hMst hA1 hA hw hw8 hwδ hT₁ hT₂
    hB₁ hB₂ hi₁ hi₂ hc₁ hc₂ hae
  classical
  have hR : max (max N₀ 1) (K ^ (2 / η₀)) ≤ Mst / δ := by
    rw [le_div_iff₀ hδ]; exact hMst
  have hN₀M : N₀ ≤ Mst / δ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have h1M : 1 ≤ Mst / δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hKM : K ^ (2 / η₀) ≤ Mst / δ := le_trans (le_max_right _ _) hR
  have hMstpos : 0 < Mst := by
    have := mul_le_mul_of_nonneg_right h1M (le_of_lt hδ)
    rw [div_mul_cancel₀ _ (ne_of_gt hδ), one_mul] at this; linarith
  -- the jittered law
  set Q := jitter3 P w with hQdef
  have hQidx : ∀ S : Set (ι₁ × ι₂), Q {p | p.1 ∈ S} = P {p | p.1 ∈ S} :=
    fun S => jitter3_index P hw (measurableSet_index S)
  haveI : IsFiniteMeasure Q := ⟨by
    have := hQidx Set.univ
    simp only [Set.mem_univ, Set.ofPred_true] at this
    rw [this]; exact measure_lt_top P _⟩
  have hm₁ : ∀ i (E : Set E3), MeasurableSet E →
      Q {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₁ i) * volume E := by
    intro i E hE
    have := jitter3_marginal P hw (S := {x : ι₁ × ι₂ | x.1 = i}) (measurableSet_index _)
      (C := ENNReal.ofReal (A * T₁ i)) (by
        intro y
        rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) (hT₁ i))]
        exact hi₁ i y) hE
    simpa using this
  have hm₂ : ∀ j (E : Set E3), MeasurableSet E →
      Q {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₂ j) * volume E := by
    intro j E hE
    have := jitter3_marginal P hw (S := {x : ι₁ × ι₂ | x.2 = j}) (measurableSet_index _)
      (C := ENNReal.ofReal (A * T₂ j)) (by
        intro y
        rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) (hT₂ j))]
        exact hi₂ j y) hE
    simpa using this
  have hQae : ∀ᵐ p ∂Q, ‖p.2‖ ≤ 1 / 2 ∧
      |q3E (c₁ p.1.1) p.2 - q3E (c₂ p.1.2) p.2| ≤ 30 * δ := by
    refine ae_jitter3 P (R := fun x y => ‖y‖ ≤ 1 / 4 ∧
        |q3E (c₁ x.1) y - q3E (c₂ x.2) y| ≤ δ)
      (R' := fun x y => ‖y‖ ≤ 1 / 2 ∧ |q3E (c₁ x.1) y - q3E (c₂ x.2) y| ≤ 30 * δ)
      ?_ hae ?_
    · have hf : Measurable (fun p : (ι₁ × ι₂) × E3 =>
          |q3E (c₁ p.1.1) p.2 - q3E (c₂ p.1.2) p.2|) := by
        apply measurable_from_prod_countable_right
        intro x
        simp only [q3E, q3]
        fun_prop
      exact (measurableSet_le (measurable_snd.norm) measurable_const).inter
        (measurableSet_le hf measurable_const)
    · intro x y u ⟨hy, hval⟩ hu
      refine ⟨norm_add_cube_le hy hw.le hw8 hu, ?_⟩
      have hy1 : ‖y‖ ≤ 1 := hy.trans (by norm_num)
      have hw1 : w ≤ 1 := hw8.trans (by norm_num)
      have h1 := q3E_shift_le (hB₁ x.1) hy1 hw.le hw1 hu
      have h2 := q3E_shift_le (hB₂ x.2) hy1 hw.le hw1 hu
      have : |q3E (c₁ x.1) (y + u) - q3E (c₂ x.2) (y + u)| ≤
          |q3E (c₁ x.1) y - q3E (c₂ x.2) y| + 21 * B * w + 21 * B * w := by
        have e : q3E (c₁ x.1) (y + u) - q3E (c₂ x.2) (y + u) =
            (q3E (c₁ x.1) y - q3E (c₂ x.2) y) + (q3E (c₁ x.1) (y + u) - q3E (c₁ x.1) y) -
              (q3E (c₂ x.2) (y + u) - q3E (c₂ x.2) y) := by ring
        rw [e]
        calc _ ≤ |(q3E (c₁ x.1) y - q3E (c₂ x.2) y) + (q3E (c₁ x.1) (y + u) - q3E (c₁ x.1) y)| +
              |q3E (c₂ x.2) (y + u) - q3E (c₂ x.2) y| := abs_sub _ _
          _ ≤ |q3E (c₁ x.1) y - q3E (c₂ x.2) y| + |q3E (c₁ x.1) (y + u) - q3E (c₁ x.1) y| +
              |q3E (c₂ x.2) (y + u) - q3E (c₂ x.2) y| := by
                gcongr; exact abs_add_le _ _
          _ ≤ _ := by gcongr
      linarith
  -- each dyadic band
  have hband : ∀ k : ℕ, Q (bandSet3 (Mst * 2 ^ k) c₁ c₂) ≤
      ENNReal.ofReal (9765625 * A * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) * ρ ^ k) := by
    intro k
    have hMk : 0 < Mst * 2 ^ k := by positivity
    have hMkδ : Mst * 2 ^ k / δ = (Mst / δ) * 2 ^ k := by ring
    have hge : Mst / δ ≤ Mst * 2 ^ k / δ := by
      rw [hMkδ]; exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
    have hA' : A ≤ (Mst * 2 ^ k / δ) ^ η₀ := by
      refine le_trans hA ?_
      calc (Mst / δ) ^ (η₀ / 2) ≤ (Mst / δ) ^ η₀ :=
            Real.rpow_le_rpow_of_exponent_le h1M (by linarith)
        _ ≤ (Mst * 2 ^ k / δ) ^ η₀ := Real.rpow_le_rpow (by linarith) hge (le_of_lt hη₀)
    have := scale_le3 hQ hη₀ c₁ c₂ T₁ T₂ Q hδ hMk (le_trans hN₀M hge) hA1 hA' hT₁ hT₂ hm₁ hm₂
      (fun r => hc₁ r _ (le_mul_of_one_le_right (le_of_lt hMstpos) (one_le_pow₀ (by norm_num))))
      (fun r => hc₂ r _ (le_mul_of_one_le_right (le_of_lt hMstpos) (one_le_pow₀ (by norm_num))))
      hQae
    refine le_trans this (le_of_eq ?_)
    congr 1
    rw [hMkδ, Real.mul_rpow (by linarith) (by positivity)]
    have : ((2:ℝ) ^ k) ^ (-η₀) = ρ ^ k := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [this]; ring
  -- cover the far set by the bands
  have hcover : {p : (ι₁ × ι₂) × E3 | Mst ≤ cnorm3 (c₁ p.1.1 - c₂ p.1.2)} ⊆
      ⋃ k : ℕ, bandSet3 (Mst * 2 ^ k) c₁ c₂ := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    have h1 : 1 ≤ cnorm3 (c₁ p.1.1 - c₂ p.1.2) / Mst := by rw [le_div_iff₀ hMstpos]; linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1:ℝ) < 2)
    simp only [Set.mem_iUnion]
    refine ⟨n, ?_, ?_⟩
    · rw [le_div_iff₀ hMstpos] at hn1; linarith
    · rw [div_lt_iff₀ hMstpos] at hn2; rw [pow_succ] at hn2; linarith
  have hsum : Summable (fun k : ℕ =>
      9765625 * A * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) * ρ ^ k) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hWnn : 0 ≤ ∑ i, T₁ i + ∑ j, T₂ j :=
    add_nonneg (Finset.sum_nonneg (fun i _ => hT₁ i)) (Finset.sum_nonneg (fun j _ => hT₂ j))
  have hCnn : 0 ≤ 9765625 * A * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) := by
    have := Real.rpow_nonneg (le_trans zero_le_one h1M) (-η₀)
    positivity
  calc P {p | Mst ≤ cnorm3 (c₁ p.1.1 - c₂ p.1.2)}
      = Q {p | Mst ≤ cnorm3 (c₁ p.1.1 - c₂ p.1.2)} :=
        (hQidx {x | Mst ≤ cnorm3 (c₁ x.1 - c₂ x.2)}).symm
    _ ≤ Q (⋃ k : ℕ, bandSet3 (Mst * 2 ^ k) c₁ c₂) := measure_mono hcover
    _ ≤ ∑' k : ℕ, Q (bandSet3 (Mst * 2 ^ k) c₁ c₂) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal
          (9765625 * A * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) * ρ ^ k) :=
        ENNReal.tsum_le_tsum hband
    _ = ENNReal.ofReal (∑' k : ℕ,
          9765625 * A * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) * ρ ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hCnn (pow_nonneg hρ0 k)) hsum).symm
    _ = ENNReal.ofReal (9765625 * A * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) *
          (1 - ρ)⁻¹) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ ≤ ENNReal.ofReal (A * (Mst / δ) ^ (-(η₀ / 2)) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
        apply ENNReal.ofReal_le_ofReal
        have hMδ : 0 < Mst / δ := lt_of_lt_of_le zero_lt_one h1M
        have hsplit : (Mst / δ) ^ (-η₀) = (Mst / δ) ^ (-(η₀ / 2)) * (Mst / δ) ^ (-(η₀ / 2)) := by
          rw [← Real.rpow_add hMδ]; ring_nf
        have hKle : K ≤ (Mst / δ) ^ (η₀ / 2) := by
          have := Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hKpos) _) hKM
            (by positivity : (0:ℝ) ≤ η₀ / 2)
          rwa [← Real.rpow_mul (le_of_lt hKpos), div_mul_div_comm, mul_comm 2 η₀,
            div_self (by positivity), Real.rpow_one] at this
        have hinv : (Mst / δ) ^ (-(η₀ / 2)) * K ≤ 1 := by
          rw [Real.rpow_neg (le_of_lt hMδ)]
          rw [inv_mul_le_iff₀ (Real.rpow_pos_of_pos hMδ _)]; linarith
        have hpos : 0 ≤ A * (Mst / δ) ^ (-(η₀ / 2)) * (∑ i, T₁ i + ∑ j, T₂ j) := by
          have := Real.rpow_nonneg (le_of_lt hMδ) (-(η₀ / 2)); positivity
        calc 9765625 * A * (Mst / δ) ^ (-η₀) * (∑ i, T₁ i + ∑ j, T₂ j) * (1 - ρ)⁻¹
            = (A * (Mst / δ) ^ (-(η₀ / 2)) * (∑ i, T₁ i + ∑ j, T₂ j)) *
                ((Mst / δ) ^ (-(η₀ / 2)) * K) := by rw [hsplit, hK]; ring
          _ ≤ (A * (Mst / δ) ^ (-(η₀ / 2)) * (∑ i, T₁ i + ∑ j, T₂ j)) * 1 := by gcongr
          _ = _ := mul_one _

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
