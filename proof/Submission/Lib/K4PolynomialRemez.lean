import Mathlib

/-!
# Fixed-degree polynomial Remez comparison

Adapted from: here:o092

An elementary Remez estimate sufficient for the scalar isotropic argument.
A positive-measure set contains a point outside small neighborhoods of every
complex root, and the product formula then compares all values in the block.
-/

namespace Submission.Lib.K4PolynomialRemez

open Set MeasureTheory

/-- A set with more mass than the union of finitely many short intervals
contains a point separated from all their centers. -/
theorem exists_away_from_finset (S : Set ℝ) (F : Finset ℝ) {η δ : ℝ}
    (hη : 0 < η) (_hδ : 0 ≤ δ) (hbudget : 2 * (F.card : ℝ) * δ < η)
    (hS : ENNReal.ofReal η ≤ volume S) :
    ∃ t ∈ S, ∀ c ∈ F, δ ≤ |t - c| := by
  classical
  let U : Set ℝ := ⋃ c ∈ F, Set.Ioo (c - δ) (c + δ)
  have hvol : volume U ≤ ENNReal.ofReal (2 * (F.card : ℝ) * δ) := by
    calc
      volume U ≤ ∑ c ∈ F, volume (Set.Ioo (c - δ) (c + δ)) :=
        measure_biUnion_finset_le _ _
      _ = ∑ _c ∈ F, ENNReal.ofReal (2 * δ) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Real.volume_Ioo]
        congr 1
        ring
      _ = ENNReal.ofReal (2 * (F.card : ℝ) * δ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg F.card)]
        congr 1
        ring
  have hnot : ¬ S ⊆ U := by
    intro hsub
    have hle := hS.trans ((measure_mono hsub).trans hvol)
    exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff hη).mpr hbudget)) hle
  obtain ⟨t, ht, htu⟩ := Set.not_subset.mp hnot
  refine ⟨t, ht, ?_⟩
  intro c hc
  by_contra h
  apply htu
  have habs := abs_lt.mp (lt_of_not_ge h)
  exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, ⟨by linarith, by linarith⟩⟩⟩

/-- Comparing every root factor compares the values of a polynomial. -/
theorem norm_eval_le_of_root_comparison (p : Polynomial ℂ) (x y : ℂ) {A : ℝ}
    (_hA : 0 ≤ A) (hroots : ∀ z ∈ p.roots, ‖x - z‖ ≤ A * ‖y - z‖) :
    ‖p.eval x‖ ≤ A ^ p.natDegree * ‖p.eval y‖ := by
  have hs := IsAlgClosed.splits p
  have hnorm (w : ℂ) : ‖p.eval w‖ = ‖p.leadingCoeff‖ *
      (p.roots.map (fun z => ‖w - z‖)).prod := by
    rw [hs.eval_eq_prod_roots, norm_mul]
    congr 1
    exact (p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun z => w - z)).symm
  have hprod := Multiset.prod_map_le_prod_map₀ (fun z : ℂ => ‖x - z‖)
    (fun z => A * ‖y - z‖) (by intro z hz; exact norm_nonneg _) hroots
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    ← hs.natDegree_eq_card_roots] at hprod
  rw [hnorm, hnorm]
  calc
    _ ≤ ‖p.leadingCoeff‖ * (A ^ p.natDegree * (p.roots.map (fun z => ‖y - z‖)).prod) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := by ring

/-- Univariate fixed-degree Remez on the unit interval. The input set need not
be measurable; outer Lebesgue mass and pointwise bounds suffice. -/
theorem polynomial_remez_unit (p : Polynomial ℝ) (D : ℕ) (hp : p.natDegree ≤ D)
    (S : Set ℝ) {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (_hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ t ∈ S, |p.eval t| ≤ E) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |p.eval x| ≤ (8 * ((D : ℝ) + 1) / η) ^ D * E := by
  classical
  let q : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  let δ : ℝ := η / (4 * ((D : ℝ) + 1))
  let F : Finset ℝ := q.roots.toFinset.image Complex.re
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 4 * ((D : ℝ) + 1) * δ = η := by dsimp [δ]; field_simp
  have hcard : (F.card : ℝ) ≤ D := by
    have h₁ := Finset.card_image_le (s := q.roots.toFinset) (f := Complex.re)
    have h₂ := q.roots.toFinset_card_le
    have h₃ := Polynomial.card_roots' q
    have hqdeg : q.natDegree = p.natDegree := by simp [q]
    exact_mod_cast (h₁.trans (h₂.trans (h₃.trans (by omega))))
  have hbudget : 2 * (F.card : ℝ) * δ < η := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hcard)]
  obtain ⟨t, ht, haway⟩ := exists_away_from_finset S F hη hδ.le hbudget hmass
  have htI := hS ht
  let A : ℝ := 8 * ((D : ℝ) + 1) / η
  have hA : 1 ≤ A := by
    apply (le_div_iff₀ hη).mpr
    nlinarith
  have hδA : 1 + δ⁻¹ ≤ A := by
    dsimp [δ, A]
    rw [inv_div]
    apply (le_div_iff₀ hη).mpr
    field_simp
    nlinarith
  have hqeval (w : ℝ) : ‖q.eval (w : ℂ)‖ = |p.eval w| := by
    rw [Polynomial.eval_map]
    change ‖p.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) w)‖ = _
    rw [Polynomial.eval₂_at_apply]
    exact Complex.norm_real _
  intro x hx
  have hroots : ∀ z ∈ q.roots, ‖(x : ℂ) - z‖ ≤ A * ‖(t : ℂ) - z‖ := by
    intro z hz
    have hzF : z.re ∈ F := Finset.mem_image.mpr ⟨z, Multiset.mem_toFinset.mpr hz, rfl⟩
    have hdist : δ ≤ ‖(t : ℂ) - z‖ := by
      exact (haway z.re hzF).trans (by simpa using Complex.abs_re_le_norm ((t : ℂ) - z))
    have hxt : ‖(x : ℂ) - (t : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2, htI.1, htI.2]
    calc
      ‖(x : ℂ) - z‖ = ‖((x : ℂ) - (t : ℂ)) + ((t : ℂ) - z)‖ := by congr 1; ring
      _ ≤ ‖(x : ℂ) - (t : ℂ)‖ + ‖(t : ℂ) - z‖ := norm_add_le _ _
      _ ≤ 1 + ‖(t : ℂ) - z‖ := add_le_add hxt le_rfl
      _ ≤ (1 + δ⁻¹) * ‖(t : ℂ) - z‖ := by
        have hm := mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr hδ.le)
        rw [inv_mul_cancel₀ hδ.ne'] at hm
        nlinarith
      _ ≤ A * ‖(t : ℂ) - z‖ := mul_le_mul_of_nonneg_right hδA (norm_nonneg _)
  have heval := norm_eval_le_of_root_comparison q (x : ℂ) (t : ℂ) (zero_le_one.trans hA) hroots
  rw [hqeval, hqeval] at heval
  calc
    |p.eval x| ≤ A ^ q.natDegree * |p.eval t| := heval
    _ ≤ A ^ D * E := by
      apply mul_le_mul
      · apply pow_le_pow_right₀ hA
        simpa [q] using hp
      · exact hbound t ht
      · exact abs_nonneg _
      · positivity

/-- A positive-mass event in a product of probability spaces has many fibers
whose mass is at least half the original lower bound. -/
theorem probability_large_fibers {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (α × β)) (hE : MeasurableSet E) {η : ℝ} (hη : 0 ≤ η)
    (hmass : ENNReal.ofReal η ≤ (μ.prod ν) E) :
    ENNReal.ofReal (η / 2) ≤ μ {x | ENNReal.ofReal (η / 2) ≤ ν (Prod.mk x ⁻¹' E)} := by
  let f : α → ENNReal := fun x => ν (Prod.mk x ⁻¹' E)
  let H : Set α := {x | ENNReal.ofReal (η / 2) ≤ f x}
  have hf : Measurable f := measurable_measure_prodMk_left hE
  have hH : MeasurableSet H := measurableSet_le measurable_const hf
  have hf1 (x : α) : f x ≤ 1 := by
    dsimp [f]
    exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ : ν Set.univ = 1)
  have hbound : (μ.prod ν) E ≤ μ H + ENNReal.ofReal (η / 2) := by
    calc
      (μ.prod ν) E = ∫⁻ x, f x ∂μ := Measure.prod_apply hE
      _ ≤ ∫⁻ x, H.indicator (fun _ => (1 : ENNReal)) x + ENNReal.ofReal (η / 2) ∂μ := by
        apply lintegral_mono
        intro x
        change f x ≤ H.indicator (fun _ => (1 : ENNReal)) x + ENNReal.ofReal (η / 2)
        by_cases hx : x ∈ H
        · rw [Set.indicator_of_mem hx]
          exact (hf1 x).trans (le_add_right le_rfl)
        · rw [Set.indicator_of_notMem hx, zero_add]
          exact le_of_lt (lt_of_not_ge hx)
      _ = μ H + ENNReal.ofReal (η / 2) := by
        rw [lintegral_add_left (measurable_const.indicator hH), lintegral_indicator hH]
        simp
  have hsplit : ENNReal.ofReal η = ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have htotal := hmass.trans hbound
  rw [hsplit] at htotal
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top htotal

/-- Remez on a unit square for a function that is polynomial of bounded
degree separately on each coordinate line. -/
theorem separately_polynomial_remez_square (f : ℝ × ℝ → ℝ) (D : ℕ)
    (hrow : ∀ x : ℝ, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ ∀ y, p.eval y = f (x, y))
    (hcol : ∀ y : ℝ, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ ∀ x, p.eval x = f (x, y))
    (S : Set (ℝ × ℝ)) (hSmeas : MeasurableSet S) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ z ∈ S, |f z| ≤ E) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      |f z| ≤ (16 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  classical
  let I : Set ℝ := Set.Icc 0 1
  let μ : Measure ℝ := volume.restrict I
  have hI : MeasurableSet I := measurableSet_Icc
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ, I]⟩
  have hμS : (μ.prod μ) S = volume S := by
    dsimp only [μ]
    rw [Measure.prod_restrict, Measure.restrict_apply hSmeas]
    rw [Set.inter_eq_left.mpr hS]
    rfl
  have hlarge := probability_large_fibers μ μ S hSmeas hη.le (hmass.trans_eq hμS.symm)
  let H : Set ℝ := {x | ENNReal.ofReal (η / 2) ≤ μ (Prod.mk x ⁻¹' S)}
  have hH : MeasurableSet H := measurableSet_le measurable_const
    (measurable_measure_prodMk_left hSmeas)
  have hHmass : ENNReal.ofReal (η / 2) ≤ volume (H ∩ I) := by
    change ENNReal.ofReal (η / 2) ≤ μ H at hlarge
    simpa only [μ, Measure.restrict_apply hH] using hlarge
  let A : ℝ := 16 * ((D : ℝ) + 1) / η
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hfactor : 8 * ((D : ℝ) + 1) / (η / 2) = A := by dsimp [A]; ring
  have hvertical : ∀ x ∈ H ∩ I, ∀ y ∈ I, |f (x, y)| ≤ A ^ D * E := by
    intro x hx y hy
    have hslice : Prod.mk x ⁻¹' S ⊆ I := by
      intro t ht
      exact (hS ht).2
    have hsliceMeas : MeasurableSet (Prod.mk x ⁻¹' S) :=
      hSmeas.preimage (measurable_const.prodMk measurable_id)
    have hsliceMass : ENNReal.ofReal (η / 2) ≤ volume (Prod.mk x ⁻¹' S) := by
      have h := hx.1
      change ENNReal.ofReal (η / 2) ≤ μ (Prod.mk x ⁻¹' S) at h
      simpa only [μ, Measure.restrict_apply hsliceMeas, Set.inter_eq_left.mpr hslice] using h
    obtain ⟨p, hp, heval⟩ := hrow x
    have h := polynomial_remez_unit p D hp (Prod.mk x ⁻¹' S)
      (by positivity : 0 < η / 2) (by linarith : η / 2 ≤ 1) hE hslice hsliceMass
      (by intro t ht; simpa only [heval] using hbound (x, t) ht) y hy
    simpa only [heval, hfactor] using h
  intro z hz
  obtain ⟨p, hp, heval⟩ := hcol z.2
  have h := polynomial_remez_unit p D hp (H ∩ I)
    (by positivity : 0 < η / 2) (by linarith : η / 2 ≤ 1)
    (mul_nonneg (pow_nonneg hA0 D) hE) Set.inter_subset_right hHmass
    (by intro x hx; simpa only [heval] using hvertical x hx z.2 hz.2) z.1 hz.1
  have heq : A ^ D * (A ^ D * E) = A ^ (2 * D) * E := by rw [two_mul, pow_add]; ring
  simpa only [heval, hfactor, heq, A] using h

/-- For a continuous separately polynomial function, an arbitrary witness set
can be replaced by its measurable closed sublevel superset. -/
theorem separately_polynomial_remez_square_of_outer_measure (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (D : ℕ)
    (hrow : ∀ x : ℝ, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ ∀ y, p.eval y = f (x, y))
    (hcol : ∀ y : ℝ, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ ∀ x, p.eval x = f (x, y))
    (S : Set (ℝ × ℝ)) {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |f z| ≤ E) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      |f z| ≤ (16 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  let B : Set (ℝ × ℝ) := (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩ {z | |f z| ≤ E}
  have hB : MeasurableSet B := (measurableSet_Icc.prod measurableSet_Icc).inter
    (isClosed_le hf.abs continuous_const).measurableSet
  have hSB : S ⊆ B := fun z hz => ⟨hS hz, hbound z hz⟩
  exact separately_polynomial_remez_square f D hrow hcol B hB hη hη1 hE
    Set.inter_subset_left (hmass.trans (measure_mono hSB)) (fun _ hz => hz.2)

/-- The same outer-measure comparison in the `Fin 2 → ℝ` coordinates used for
scalar fields and their potentials. -/
theorem separately_polynomial_remez_box (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) (D : ℕ)
    (hrow : ∀ x : ℝ, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ ∀ y, p.eval y = f ![x, y])
    (hcol : ∀ y : ℝ, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ ∀ x, p.eval x = f ![x, y])
    (S : Set (Fin 2 → ℝ)) {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : Fin 2 → ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |f z| ≤ E) :
    ∀ z ∈ Set.Icc (0 : Fin 2 → ℝ) 1,
      |f z| ≤ (16 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  let e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.finTwoArrow
  let g : ℝ × ℝ → ℝ := fun z => f ![z.1, z.2]
  have hg : Continuous g := hf.comp (by apply continuous_pi; intro i; fin_cases i <;> fun_prop)
  have hvec (x : Fin 2 → ℝ) : (![x 0, x 1] : Fin 2 → ℝ) = x := by
    ext i
    fin_cases i <;> rfl
  have hpre : e ⁻¹' (e '' S) = S := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, e.injective.eq_iff]
    simp
  have himage : volume (e '' S) = volume S := by
    have h := (volume_preserving_finTwoArrow ℝ).measure_preimage_emb e.measurableEmbedding (e '' S)
    rw [show (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ) = e by rfl, hpre] at h
    exact h.symm
  have hsubset : e '' S ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨(hS hx).1 0, (hS hx).2 0⟩, ⟨(hS hx).1 1, (hS hx).2 1⟩⟩
  have hbounds : ∀ z ∈ e '' S, |g z| ≤ E := by
    rintro z ⟨x, hx, rfl⟩
    simpa only [g, e, MeasurableEquiv.finTwoArrow_apply, hvec] using hbound x hx
  have h := separately_polynomial_remez_square_of_outer_measure g hg D hrow hcol (e '' S)
    hη hη1 hE hsubset (hmass.trans_eq himage.symm) hbounds
  intro z hz
  have hz' : (z 0, z 1) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨hz.1 0, hz.2 0⟩, ⟨hz.1 1, hz.2 1⟩⟩
  simpa only [g, hvec] using h (z 0, z 1) hz'

end Submission.Lib.K4PolynomialRemez
