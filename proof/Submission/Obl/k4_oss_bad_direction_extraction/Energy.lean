import Mathlib

/-!
# Energy side of `k4_oss_bad_direction_extraction`

* `card_le_of_separated_of_subset_ball`: a `δ`-separated finite set in a closed interval of
  radius `ρ` has at most `2 ρ / δ + 1` points.
* `energy_le`: for `t ∈ [1/4, 1]` and `δ`-separated `B`, the finite energy is at most
  `129 |A|² |B|`.
* `bad_mass`: if the `ν`-average of the energy exceeds `κ |A|² |B|`, the slopes of
  `[1/4, 1]` with energy at least `(κ / 2) |A|² |B|` have `ν`-mass at least `κ / 258`
  (no measurability of that set is needed).
* `measurable_energy`, `measurableSet_bad`: the energy is measurable in the slope, and so is
  the set of slopes of `[1/4, 1]` with energy at least a given constant.
* `exponent_conditions`, `relation_of_large_energy`: the per-slope step, from o041's
  statement (a hypothesis) at `τ = δ^θ / 2` to the relation and cover of the conclusion.
-/

namespace Submission.Obl.k4_oss_bad_direction_extraction

open MeasureTheory

/-- A `δ`-separated finite set inside a closed interval of radius `ρ` has at most
`2 ρ / δ + 1` points: the grid index `⌊(x - c + ρ) / δ⌋₊` is injective on it. -/
theorem card_le_of_separated_of_subset_ball (S : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → δ ≤ dist a a') {c ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsub : ∀ x ∈ S, |x - c| ≤ ρ) : (S.card : ℝ) ≤ 2 * ρ / δ + 1 := by
  set f : ℝ → ℕ := fun x => ⌊(x - c + ρ) / δ⌋₊ with hf
  have hmaps : Set.MapsTo f (S : Set ℝ) (Finset.range (⌊2 * ρ / δ⌋₊ + 1) : Set ℕ) := by
    intro x hx
    have hx' := hsub x hx
    rw [abs_le] at hx'
    simp only [Finset.coe_range, Set.mem_Iio, hf]
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hδ.le
    linarith [hx'.2]
  have hinj : Set.InjOn f (S : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hsep := hS x hx y hy hne
    rw [Real.dist_eq] at hsep
    have hx' := hsub x hx
    have hy' := hsub y hy
    rw [abs_le] at hx' hy'
    have h0x : 0 ≤ (x - c + ρ) / δ := div_nonneg (by linarith) hδ.le
    have h0y : 0 ≤ (y - c + ρ) / δ := div_nonneg (by linarith) hδ.le
    rcases le_or_gt x y with hle | hlt
    · have hd : δ ≤ y - x := by
        rw [abs_of_nonpos (by linarith)] at hsep; linarith
      have : (x - c + ρ) / δ + 1 ≤ (y - c + ρ) / δ := by
        rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; linarith
      have h1 : ⌊(x - c + ρ) / δ⌋₊ + 1 ≤ ⌊(y - c + ρ) / δ⌋₊ := by
        rw [← Nat.floor_add_one h0x]; exact Nat.floor_le_floor this
      simp only [hf] at hxy
      omega
    · have hd : δ ≤ x - y := by
        rw [abs_of_nonneg (by linarith)] at hsep; linarith
      have : (y - c + ρ) / δ + 1 ≤ (x - c + ρ) / δ := by
        rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; linarith
      have h1 : ⌊(y - c + ρ) / δ⌋₊ + 1 ≤ ⌊(x - c + ρ) / δ⌋₊ := by
        rw [← Nat.floor_add_one h0y]; exact Nat.floor_le_floor this
      simp only [hf] at hxy
      omega
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_range] at hcard
  have h2 : ((⌊2 * ρ / δ⌋₊ : ℕ) : ℝ) ≤ 2 * ρ / δ :=
    Nat.floor_le (div_nonneg (by linarith) hδ.le)
  calc (S.card : ℝ) ≤ ((⌊2 * ρ / δ⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((⌊2 * ρ / δ⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ 2 * ρ / δ + 1 := by linarith

/-- For a fixed slope `t ≥ 1/4` and fixed `a, b, a'`, at most `129` points `b'` of a
`δ`-separated set satisfy the energy condition. -/
theorem card_filter_window_le (B : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hB : ∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') {t : ℝ} (ht : 1 / 4 ≤ t) (a b a' : ℝ) :
    (B.filter (fun b' => |a + t * b - (a' + t * b')| ≤ 16 * δ)).card ≤ 129 := by
  have ht0 : 0 < t := by linarith
  have h := card_le_of_separated_of_subset_ball (B.filter (fun b' => |a + t * b - (a' + t * b')| ≤ 16 * δ))
    hδ (fun x hx y hy hxy => hB x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
    (c := (a + t * b - a') / t) (ρ := 64 * δ) (by linarith) (by
      intro x hx
      have hx' := (Finset.mem_filter.1 hx).2
      have heq : x - (a + t * b - a') / t = -(a + t * b - (a' + t * x)) / t := by
        field_simp; ring
      rw [heq, abs_div, abs_neg, abs_of_pos ht0, div_le_iff₀ ht0]
      nlinarith)
  have h2 : 2 * (64 * δ) / δ + 1 = 129 := by field_simp; norm_num
  rw [h2] at h
  exact_mod_cast h

/-- The uniform bound on the finite energy at slopes `t ∈ [1/4, 1]`. -/
theorem energy_le (A B : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hB : ∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ) ≤
      129 * (A.card : ℝ) ^ 2 * (B.card : ℝ) := by
  have key : (((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card ≤
      (A.card * B.card) * (A.card * 129) := by
    rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
    calc ∑ x ∈ A ×ˢ B, ∑ y ∈ A ×ˢ B,
          (if |(x, y).1.1 + t * (x, y).1.2 - ((x, y).2.1 + t * (x, y).2.2)| ≤ 16 * δ then 1 else 0)
        ≤ ∑ x ∈ A ×ˢ B, (A.card * 129) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.sum_product]
          calc ∑ a' ∈ A, ∑ b' ∈ B,
                (if |(x, (a', b')).1.1 + t * (x, (a', b')).1.2 -
                  ((x, (a', b')).2.1 + t * (x, (a', b')).2.2)| ≤ 16 * δ then 1 else 0)
              ≤ ∑ a' ∈ A, 129 := by
                apply Finset.sum_le_sum
                intro a' ha'
                rw [← Finset.card_filter]
                exact card_filter_window_le B hδ hB ht.1 x.1 x.2 a'
            _ = A.card * 129 := by rw [Finset.sum_const, smul_eq_mul]
      _ = (A.card * B.card) * (A.card * 129) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_product]
  calc _ ≤ (((A.card * B.card) * (A.card * 129) : ℕ) : ℝ) := by exact_mod_cast key
    _ = 129 * (A.card : ℝ) ^ 2 * (B.card : ℝ) := by push_cast; ring

/-- If the `ν`-average of the finite energy exceeds `κ |A|² |B|`, the slopes in `[1/4, 1]`
whose energy is at least `(κ / 2) |A|² |B|` have `ν`-mass at least `κ / 258`. -/
theorem bad_mass (A B : Finset ℝ) {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hB : ∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a')
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0)
    (hE : ¬ (MeasureTheory.lintegral ν (fun t : ℝ => ENNReal.ofReal
      (((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ))) ≤
      ENNReal.ofReal (κ * (A.card : ℝ) ^ 2 * (B.card : ℝ)))) :
    ENNReal.ofReal (κ / 258) ≤ ν {t : ℝ | t ∈ Set.Icc (1 / 4 : ℝ) 1 ∧
      κ / 2 * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤
        ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
          |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ)} := by
  set E : ℝ → ℝ := fun t => ((((A.product B).product (A.product B)).filter
    (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ)
    with hEdef
  set M : ℝ := (A.card : ℝ) ^ 2 * (B.card : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  set T : Set ℝ := {t : ℝ | t ∈ Set.Icc (1 / 4 : ℝ) 1 ∧ κ / 2 * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ E t}
    with hT
  have hae : ∀ᵐ t ∂ν, ENNReal.ofReal (E t) ≤
      ENNReal.ofReal (κ / 2 * M) + T.indicator (fun _ => ENNReal.ofReal (129 * M)) t := by
    have hmem : Set.Icc (1 / 4 : ℝ) 1 ∈ ae ν := mem_ae_iff.2 hν
    filter_upwards [hmem] with t ht
    by_cases htT : t ∈ T
    · rw [Set.indicator_of_mem htT]
      refine le_trans ?_ le_add_self
      apply ENNReal.ofReal_le_ofReal
      have := energy_le A B hδ hB ht
      simpa [hEdef, hM, mul_assoc] using this
    · rw [Set.indicator_of_notMem htT, add_zero]
      apply ENNReal.ofReal_le_ofReal
      have : ¬ (κ / 2 * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ E t) := fun h => htT ⟨ht, h⟩
      rw [hM]; linarith [not_le.mp this]
  have hint : MeasureTheory.lintegral ν (fun t => ENNReal.ofReal (E t)) ≤
      ENNReal.ofReal (κ / 2 * M) + ENNReal.ofReal (129 * M) * ν T := by
    calc MeasureTheory.lintegral ν (fun t => ENNReal.ofReal (E t))
        ≤ ∫⁻ t, (ENNReal.ofReal (κ / 2 * M) + T.indicator (fun _ => ENNReal.ofReal (129 * M)) t) ∂ν :=
          lintegral_mono_ae hae
      _ = ENNReal.ofReal (κ / 2 * M) * ν Set.univ +
            ∫⁻ t, T.indicator (fun _ => ENNReal.ofReal (129 * M)) t ∂ν := by
          rw [lintegral_add_left measurable_const, lintegral_const]
      _ ≤ ENNReal.ofReal (κ / 2 * M) + ENNReal.ofReal (129 * M) * ν T := by
          rw [measure_univ, mul_one]
          gcongr
          calc ∫⁻ t, T.indicator (fun _ => ENNReal.ofReal (129 * M)) t ∂ν
              ≤ ∫⁻ t in T, ENNReal.ofReal (129 * M) ∂ν := lintegral_indicator_le _ _
            _ = ENNReal.ofReal (129 * M) * ν T := setLIntegral_const _ _
  by_contra hlt
  replace hlt := not_le.mp hlt
  apply hE
  calc MeasureTheory.lintegral ν (fun t => ENNReal.ofReal (E t))
      ≤ ENNReal.ofReal (κ / 2 * M) + ENNReal.ofReal (129 * M) * ν T := hint
    _ ≤ ENNReal.ofReal (κ / 2 * M) + ENNReal.ofReal (129 * M) * ENNReal.ofReal (κ / 258) := by
        gcongr
    _ = ENNReal.ofReal (κ * (A.card : ℝ) ^ 2 * (B.card : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hM]; ring

/-- The finite energy is a measurable function of the slope: a finite sum of indicators of
closed sets. -/
theorem measurable_energy (A B : Finset ℝ) (δ : ℝ) :
    Measurable (fun t : ℝ => ((((A.product B).product (A.product B)).filter
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ)) := by
  simp_rw [Finset.card_filter]
  push_cast
  apply Finset.measurable_sum
  intro q _
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurable_const
  · exact measurable_const

/-- The set of slopes of `[1/4, 1]` with energy at least `c` is measurable. -/
theorem measurableSet_bad (A B : Finset ℝ) (δ c : ℝ) :
    MeasurableSet {t : ℝ | t ∈ Set.Icc (1 / 4 : ℝ) 1 ∧
      c ≤ ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
          |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ)} :=
  measurableSet_Icc.inter (measurableSet_le measurable_const (measurable_energy A B δ))

/-- Exponent bookkeeping for the per-slope step: with `4 θ ≤ η` and `40000 δ^(η/4) ≤ 1`,
the relation density `δ^θ / 20000` beats `δ^η` and the cover size `20000 δ^(-3θ)` stays
below `δ^(-η)`. -/
theorem exponent_conditions {δ θ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ)
    (hθη : 4 * θ ≤ η) (hsmall : 40000 * δ ^ (η / 4) ≤ 1) :
    20000 * δ ^ η ≤ δ ^ θ ∧ 20000 * δ ^ (-3 * θ) < δ ^ (-η) := by
  have hη : 0 ≤ η := by linarith
  have hq : 0 < δ ^ (η / 4) := Real.rpow_pos_of_pos hδ _
  constructor
  · have h1 : δ ^ η = δ ^ θ * δ ^ (η - θ) := by
      rw [← Real.rpow_add hδ]; ring_nf
    have h2 : δ ^ (η - θ) ≤ δ ^ (η / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h3 : 0 < δ ^ θ := Real.rpow_pos_of_pos hδ _
    rw [h1]
    nlinarith
  · have h1 : δ ^ (-η) = δ ^ (-3 * θ) * δ ^ (-(η - 3 * θ)) := by
      rw [← Real.rpow_add hδ]; ring_nf
    have h2 : δ ^ (-(η / 4)) ≤ δ ^ (-(η - 3 * θ)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h3 : δ ^ (-(η / 4)) = (δ ^ (η / 4))⁻¹ := Real.rpow_neg hδ.le _
    have h4 : 40000 ≤ δ ^ (-(η / 4)) := by
      rw [h3, ← one_div, le_div_iff₀ hq]; exact hsmall
    have h5 : 0 < δ ^ (-3 * θ) := Real.rpow_pos_of_pos hδ _
    rw [h1]
    nlinarith

/-- The per-slope step. The finite energy-to-relation lemma (the statement of o041, taken
as the hypothesis `H`) at `τ = δ^θ / 2` turns a slope `t ∈ [1/4, 1]` of energy at least
`(δ^θ / 2) |A|² |B|` into a relation of density at least `δ^η` whose projection `a + t b`
is covered by fewer than `δ^(-η) |A|` closed `δ`-balls, given `|B| ≤ δ^(-2θ) |A|` and the
exponent conditions of `exponent_conditions`. -/
theorem relation_of_large_energy
    (H : ∀ δ τ : ℝ, 0 < δ → 0 < τ → τ ≤ 1 → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty →
      ∀ t : ℝ, t ∈ Set.Icc (1 / 4 : ℝ) 1 → (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') →
      (∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') →
      τ * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤
        ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
          |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ) →
      ∃ R : A → B → Prop, (τ / 10000) * (A.card : ℝ) * (B.card : ℝ) ≤
        (Set.ncard {p : A × B | R p.1 p.2} : ℝ) ∧ ∃ (m : ℕ) (z : Fin m → ℝ),
          (m : ℝ) ≤ (10000 / τ) * (B.card : ℝ) ∧
          ∀ (a : A) (b : B), R a b → ∃ i : Fin m, dist ((a : ℝ) + t * (b : ℝ)) (z i) ≤ δ)
    {δ θ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ)
    (h1 : 20000 * δ ^ η ≤ δ ^ θ) (h2 : 20000 * δ ^ (-3 * θ) < δ ^ (-η))
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a')
    (hBsep : ∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a')
    (hcard : (B.card : ℝ) ≤ δ ^ (-2 * θ) * (A.card : ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hlarge : δ ^ θ / 2 * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤
      ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ)) :
    ∃ R : A → B → Prop, δ ^ η * (A.card : ℝ) * (B.card : ℝ) ≤
      (Set.ncard {p : A × B | R p.1 p.2} : ℝ) ∧ ∃ (m : ℕ) (z : Fin m → ℝ),
        (m : ℝ) < δ ^ (-η) * (A.card : ℝ) ∧
        ∀ (a : A) (b : B), R a b → ∃ i : Fin m, dist ((a : ℝ) + t * (b : ℝ)) (z i) ≤ δ := by
  have hθpos : 0 < δ ^ θ := Real.rpow_pos_of_pos hδ _
  have hθle : δ ^ θ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hθ
  obtain ⟨R, hR, m, z, hm, hz⟩ := H δ (δ ^ θ / 2) hδ (by positivity) (by linarith) A B hA hB t ht
    hAsep hBsep hlarge
  refine ⟨R, ?_, m, z, ?_, hz⟩
  · refine le_trans ?_ hR
    have hAB : 0 ≤ (A.card : ℝ) * (B.card : ℝ) := by positivity
    have : δ ^ η ≤ δ ^ θ / 2 / 10000 := by linarith
    calc δ ^ η * (A.card : ℝ) * (B.card : ℝ) = δ ^ η * ((A.card : ℝ) * (B.card : ℝ)) := by ring
      _ ≤ δ ^ θ / 2 / 10000 * ((A.card : ℝ) * (B.card : ℝ)) := by gcongr
      _ = _ := by ring
  · have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hτ : 10000 / (δ ^ θ / 2) = 20000 * δ ^ (-θ) := by
      rw [Real.rpow_neg hδ.le]; field_simp; norm_num
    have hexp : δ ^ (-θ) * δ ^ (-2 * θ) = δ ^ (-3 * θ) := by
      rw [← Real.rpow_add hδ]; ring_nf
    have hnθ : 0 < δ ^ (-θ) := Real.rpow_pos_of_pos hδ _
    calc (m : ℝ) ≤ 10000 / (δ ^ θ / 2) * (B.card : ℝ) := hm
      _ = 20000 * δ ^ (-θ) * (B.card : ℝ) := by rw [hτ]
      _ ≤ 20000 * δ ^ (-θ) * (δ ^ (-2 * θ) * (A.card : ℝ)) := by gcongr
      _ = 20000 * δ ^ (-3 * θ) * (A.card : ℝ) := by rw [← hexp]; ring
      _ < δ ^ (-η) * (A.card : ℝ) := by gcongr

end Submission.Obl.k4_oss_bad_direction_extraction
