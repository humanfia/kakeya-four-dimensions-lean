import Mathlib

/-!
# Density tails under covered and related relabellings

Abstract measure lemmas for comparing densities of two observations of one law.

* `cover_upper_tail`: if every source observation is one of finitely many images of the target
  observation, under maps which do not enlarge reference measure, then high target densities
  of a restricted law have mass bounded by a multiple of the high source densities.
  This generalizes the two-shift tail estimate of this tree (o129, `TwoShift.lean`, session
  x0350's `two_shift_upper_tail`) to arbitrary finite covers.
* `relation_low_density_mass_dep`: the low-density comparison of two label refinements of one
  observation with a relation that may depend on the continuous coordinate. It is adapted from
  this tree's o126, `GridRelation.lean` (`relation_low_density_mass`), where the relation was
  independent of the coordinate.
* `prod_count_image`: label maps along a fixed base point do not enlarge `ref × count`.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set
open scoped ENNReal

section Cover

variable {X O₁ O₂ ι : Type*} [MeasurableSpace X] [MeasurableSpace O₁] [MeasurableSpace O₂]
  [Fintype ι]

/-- Upper tails of a restricted law whose source observation is one of finitely many images of
its target observation. -/
theorem cover_upper_tail (ref₁ : Measure O₁) (ref₂ : Measure O₂) (μ : Measure X)
    [IsFiniteMeasure μ] {Φ : X → O₁} {Ψ : X → O₂} (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    {H : O₁ → ℝ≥0∞} (hH : Measurable H) (hHlaw : μ.map Φ = ref₁.withDensity H)
    (S : Set X) {D : O₂ → ℝ≥0∞} (hD : Measurable D)
    (hDlaw : (μ.restrict S).map Ψ = ref₂.withDensity D)
    (G : ι → O₂ → O₁) (hcover : ∀ x, ∃ j, Φ x = G j (Ψ x))
    (hG : ∀ j (A : Set O₂), MeasurableSet A →
      ∃ M : Set O₁, MeasurableSet M ∧ G j '' A ⊆ M ∧ ref₁ M ≤ ref₂ A)
    {T θ : ℝ≥0∞} (hθ : 2 * (Fintype.card ι : ℝ≥0∞) * θ ≤ T) :
    μ (S ∩ {x | T < D (Ψ x)}) ≤ 2 * (Fintype.card ι : ℝ≥0∞) * μ (S ∩ {x | θ < H (Φ x)}) := by
  classical
  set K : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) with hKdef
  set A : Set O₂ := {o | T < D o} with hAdef
  have hA : MeasurableSet A := measurableSet_lt measurable_const hD
  set lam := μ (S ∩ {x | T < D (Ψ x)}) with hlamdef
  set B := μ (S ∩ {x | θ < H (Φ x)}) with hBdef
  have hlam : (μ.restrict S).map Ψ A = lam := by
    rw [Measure.map_apply hΨ hA, Measure.restrict_apply (hΨ hA), inter_comm]
    rfl
  have hTA : T * ref₂ A ≤ lam := by
    rw [← hlam, hDlaw, withDensity_apply _ hA, ← setLIntegral_const]
    exact setLIntegral_mono hD (fun y hy => hy.le)
  have hpiece : ∀ j : ι, μ (S ∩ {x | T < D (Ψ x)} ∩ {x | Φ x = G j (Ψ x)}) ≤
      B + θ * ref₂ A := by
    intro j
    obtain ⟨M, hM, hAM, hMA⟩ := hG j A hA
    have hB' : MeasurableSet (M ∩ {o | H o ≤ θ}) := hM.inter (measurableSet_le hH measurable_const)
    calc μ (S ∩ {x | T < D (Ψ x)} ∩ {x | Φ x = G j (Ψ x)})
        ≤ μ ((S ∩ {x | θ < H (Φ x)}) ∪ Φ ⁻¹' (M ∩ {o | H o ≤ θ})) := by
          apply measure_mono
          rintro x ⟨⟨hxS, hxD⟩, hxe⟩
          by_cases hH4 : θ < H (Φ x)
          · exact Or.inl ⟨hxS, hH4⟩
          · refine Or.inr ⟨?_, not_lt.mp hH4⟩
            have hxe' : Φ x = G j (Ψ x) := hxe
            rw [hxe']
            exact hAM ⟨Ψ x, hxD, rfl⟩
      _ ≤ B + μ (Φ ⁻¹' (M ∩ {o | H o ≤ θ})) := measure_union_le _ _
      _ ≤ B + θ * ref₂ A := by
          gcongr
          rw [← Measure.map_apply hΦ hB', hHlaw, withDensity_apply _ hB']
          calc ∫⁻ o in M ∩ {o | H o ≤ θ}, H o ∂ref₁
              ≤ ∫⁻ _ in M ∩ {o | H o ≤ θ}, θ ∂ref₁ :=
                setLIntegral_mono measurable_const (fun o ho => ho.2)
            _ = θ * ref₁ (M ∩ {o | H o ≤ θ}) := setLIntegral_const _ _
            _ ≤ θ * ref₁ M := by gcongr; exact inter_subset_left
            _ ≤ θ * ref₂ A := by gcongr
  have hsplit : lam ≤ ∑ j : ι, μ (S ∩ {x | T < D (Ψ x)} ∩ {x | Φ x = G j (Ψ x)}) := by
    refine (measure_mono ?_).trans (measure_iUnion_fintype_le μ _)
    intro x hx
    obtain ⟨j, hj⟩ := hcover x
    exact mem_iUnion.mpr ⟨j, hx, hj⟩
  have hfin : lam ≠ ∞ := measure_ne_top μ _
  have h1 : lam ≤ K * B + K * (θ * ref₂ A) := by
    calc lam ≤ ∑ _j : ι, (B + θ * ref₂ A) := hsplit.trans (Finset.sum_le_sum fun j _ => hpiece j)
      _ = K * B + K * (θ * ref₂ A) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hKdef]
          ring
  have h2 : 2 * (K * (θ * ref₂ A)) ≤ lam := by
    calc 2 * (K * (θ * ref₂ A)) = (2 * K * θ) * ref₂ A := by ring
      _ ≤ T * ref₂ A := by gcongr
      _ ≤ lam := hTA
  have h3 : lam + lam ≤ 2 * K * B + lam := by
    calc lam + lam = 2 * lam := by ring
      _ ≤ 2 * (K * B + K * (θ * ref₂ A)) := by gcongr
      _ = 2 * K * B + 2 * (K * (θ * ref₂ A)) := by ring
      _ ≤ 2 * K * B + lam := by gcongr
  exact ENNReal.le_of_add_le_add_right hfin h3

end Cover

section Image

variable {Y L₁ L₂ : Type*} [MeasurableSpace Y] [MeasurableSpace L₁] [MeasurableSpace L₂]
  [Countable L₁] [Countable L₂] [MeasurableSingletonClass L₁]

/-- The image of a set under a label map along base points. -/
def labelImage (g : Y × L₂ → L₁) (A : Set (Y × L₂)) : Set (Y × L₁) :=
  {q | ∃ ℓ, (q.1, ℓ) ∈ A ∧ g (q.1, ℓ) = q.2}

lemma measurableSet_labelImage {g : Y × L₂ → L₁} (hg : Measurable g) {A : Set (Y × L₂)}
    (hA : MeasurableSet A) : MeasurableSet (labelImage g A) := by
  have h : labelImage g A = ⋃ ℓ : L₂, ((fun q : Y × L₁ => (q.1, ℓ)) ⁻¹' A ∩
      {q : Y × L₁ | g (q.1, ℓ) = q.2}) := by
    ext q
    simp [labelImage]
  rw [h]
  refine MeasurableSet.iUnion fun ℓ => ?_
  exact (hA.preimage (measurable_fst.prodMk measurable_const)).inter
    (measurableSet_eq_fun (hg.comp (measurable_fst.prodMk measurable_const)) measurable_snd)

omit [MeasurableSpace Y] [MeasurableSpace L₁] [MeasurableSpace L₂] [Countable L₁] [Countable L₂]
  [MeasurableSingletonClass L₁] in
lemma image_subset_labelImage (g : Y × L₂ → L₁) (A : Set (Y × L₂)) :
    (fun q : Y × L₂ => (q.1, g q)) '' A ⊆ labelImage g A := by
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨q.2, hq, rfl⟩

/-- Label maps along base points do not enlarge `ref × count`. -/
lemma prod_count_labelImage_le [MeasurableSingletonClass L₂] (ref : Measure Y) [SFinite ref] {g : Y × L₂ → L₁}
    (hg : Measurable g) {A : Set (Y × L₂)} (hA : MeasurableSet A) :
    (ref.prod (Measure.count : Measure L₁)) (labelImage g A) ≤
      (ref.prod (Measure.count : Measure L₂)) A := by
  rw [Measure.prod_apply (measurableSet_labelImage hg hA), Measure.prod_apply hA]
  apply lintegral_mono
  intro y
  simp only
  have hfib : Prod.mk y ⁻¹' labelImage g A = (fun ℓ => g (y, ℓ)) '' (Prod.mk y ⁻¹' A) := by
    ext ℓ₁
    simp [labelImage]
  rw [hfib, Measure.count_apply (Set.to_countable _).measurableSet,
    Measure.count_apply (Set.to_countable _).measurableSet]
  exact_mod_cast Set.encard_image_le _ _

/-- The covering hypothesis of `cover_upper_tail` for label maps along base points. -/
lemma labelImage_cover [MeasurableSingletonClass L₂] (ref : Measure Y) [SFinite ref] {g : Y × L₂ → L₁}
    (hg : Measurable g) (A : Set (Y × L₂)) (hA : MeasurableSet A) :
    ∃ M : Set (Y × L₁), MeasurableSet M ∧ (fun q : Y × L₂ => (q.1, g q)) '' A ⊆ M ∧
      (ref.prod (Measure.count : Measure L₁)) M ≤ (ref.prod (Measure.count : Measure L₂)) A :=
  ⟨labelImage g A, measurableSet_labelImage hg hA, image_subset_labelImage g A,
    prod_count_labelImage_le ref hg hA⟩

end Image

section Relation

open Classical in
/-- The low-density comparison for two label refinements of a common observation, with a
relation depending on the common coordinate. Adapted from this tree's o126,
`GridRelation.lean` (`relation_low_density_mass`). -/
theorem relation_low_density_mass_dep {Ω Z L₁ L₂ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable L₁] [Countable L₂]
    (μ : Measure Ω) (ρ : Measure Z) (z : Ω → Z) (ℓ₁ : Ω → L₁) (ℓ₂ : Ω → L₂)
    (hℓ₂ : ∀ b, MeasurableSet {p | ℓ₂ p = b})
    (g₁ : Z → L₁ → ℝ≥0∞) (g₂ : Z → L₂ → ℝ≥0∞)
    (hg₁ : ∀ a, Measurable (fun x => g₁ x a)) (hg₂ : ∀ b, Measurable (fun x => g₂ x b))
    (h₁ : ∀ a S, MeasurableSet S → μ {p | ℓ₁ p = a ∧ z p ∈ S} = ∫⁻ x in S, g₁ x a ∂ρ)
    (h₂ : ∀ b S, MeasurableSet S → μ {p | ℓ₂ p = b ∧ z p ∈ S} = ∫⁻ x in S, g₂ x b ∂ρ)
    (R : Z → L₁ → L₂ → Prop) (hRm : ∀ a b, MeasurableSet {x | R x a b})
    (hR : ∀ᵐ p ∂μ, R (z p) (ℓ₁ p) (ℓ₂ p))
    (D : ℝ≥0∞) (hD : ∀ x b, ∑' a, (if R x a b then (1 : ℝ≥0∞) else 0) ≤ D)
    (ε : ℝ≥0∞) :
    μ {p | g₁ (z p) (ℓ₁ p) < ε * g₂ (z p) (ℓ₂ p)} ≤ ε * D * μ univ := by
  classical
  let S : L₁ → L₂ → Set Z := fun a b => {x | g₁ x a < ε * g₂ x b} ∩ {x | R x a b}
  have hS (a : L₁) (b : L₂) : MeasurableSet (S a b) :=
    (measurableSet_lt (hg₁ a) (measurable_const.mul (hg₂ b))).inter (hRm a b)
  let T : L₁ × L₂ → Set Ω := fun ab => {p | ℓ₁ p = ab.1 ∧ z p ∈ S ab.1 ab.2} ∩ {p | ℓ₂ p = ab.2}
  have hsub : {p | g₁ (z p) (ℓ₁ p) < ε * g₂ (z p) (ℓ₂ p)} ≤ᵐ[μ] ⋃ ab, T ab := by
    filter_upwards [hR] with p hp hbad
    refine mem_iUnion.mpr ⟨(ℓ₁ p, ℓ₂ p), ?_⟩
    exact ⟨⟨rfl, hbad, hp⟩, rfl⟩
  have hind (a : L₁) (b : L₂) (x : Z) :
      ({x | R x a b} : Set Z).indicator (fun x => ε * g₂ x b) x =
        ε * ((if R x a b then (1 : ℝ≥0∞) else 0) * g₂ x b) := by
    by_cases h : R x a b <;> simp [Set.indicator, h]
  have hT (ab : L₁ × L₂) :
      μ (T ab) ≤ ∫⁻ x, ({x | R x ab.1 ab.2} : Set Z).indicator (fun x => ε * g₂ x ab.2) x ∂ρ := by
    obtain ⟨a, b⟩ := ab
    calc
      μ (T (a, b)) ≤ μ {p | ℓ₁ p = a ∧ z p ∈ S a b} := measure_mono inter_subset_left
      _ = ∫⁻ x in S a b, g₁ x a ∂ρ := h₁ a _ (hS a b)
      _ ≤ ∫⁻ x in S a b, ε * g₂ x b ∂ρ := setLIntegral_mono' (hS a b) (fun x hx => hx.1.le)
      _ ≤ ∫⁻ x in {x | R x a b}, ε * g₂ x b ∂ρ := lintegral_mono_set inter_subset_right
      _ = ∫⁻ x, ({x | R x a b} : Set Z).indicator (fun x => ε * g₂ x b) x ∂ρ :=
          (lintegral_indicator (hRm a b) _).symm
  have hslice (b : L₂) : μ {p | ℓ₂ p = b} = ∫⁻ x, g₂ x b ∂ρ := by
    have h := h₂ b univ MeasurableSet.univ
    simp only [mem_univ, and_true, Measure.restrict_univ] at h
    exact h
  have hdisj : Pairwise (Function.onFun Disjoint (fun b : L₂ => {p : Ω | ℓ₂ p = b})) := by
    intro b b' hbb'
    refine Set.disjoint_left.mpr ?_
    intro p hp hp'
    exact hbb' (hp.symm.trans hp')
  have htotal : ∑' b, μ {p | ℓ₂ p = b} = μ univ := by
    rw [← measure_iUnion hdisj hℓ₂]
    congr 1
    ext p
    simp
  have hmeasI (a : L₁) (b : L₂) :
      Measurable (({x | R x a b} : Set Z).indicator (fun x => ε * g₂ x b)) :=
    (measurable_const.mul (hg₂ b)).indicator (hRm a b)
  calc
    μ {p | g₁ (z p) (ℓ₁ p) < ε * g₂ (z p) (ℓ₂ p)} ≤ μ (⋃ ab, T ab) := measure_mono_ae hsub
    _ ≤ ∑' ab, μ (T ab) := measure_iUnion_le _
    _ ≤ ∑' ab : L₁ × L₂,
        ∫⁻ x, ({x | R x ab.1 ab.2} : Set Z).indicator (fun x => ε * g₂ x ab.2) x ∂ρ :=
      ENNReal.tsum_le_tsum hT
    _ = ∑' b, ∑' a, ∫⁻ x, ({x | R x a b} : Set Z).indicator (fun x => ε * g₂ x b) x ∂ρ := by
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ = ∑' b, ∫⁻ x, ∑' a, ({x | R x a b} : Set Z).indicator (fun x => ε * g₂ x b) x ∂ρ := by
      apply tsum_congr
      intro b
      rw [lintegral_tsum (fun a => (hmeasI a b).aemeasurable)]
    _ ≤ ∑' b, ∫⁻ x, ε * (D * g₂ x b) ∂ρ := by
      apply ENNReal.tsum_le_tsum
      intro b
      apply lintegral_mono
      intro x
      simp only [hind]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      gcongr
      exact hD x b
    _ = ε * D * μ univ := by
      have hb : ∀ b, ∫⁻ x, ε * (D * g₂ x b) ∂ρ = ε * D * μ {p | ℓ₂ p = b} := by
        intro b
        rw [hslice b, ← lintegral_const_mul _ (hg₂ b)]
        congr 1
        funext x
        ring
      rw [tsum_congr hb, ENNReal.tsum_mul_left, htotal]

end Relation

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
