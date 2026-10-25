import Mathlib

/-!
# From fine scalar bins to coarse scalar bins

The residual-slope concentration of the first jet gives a short list of slope values for
every FINE scalar bin `Y` (width `H`), while the bootstrap needs short lists for every COARSE
scalar bin `Z` (width `w ≫ H`). The paper passes between them with the common-information
inequality and the near independence of the coefficient bin `X` and the fine bin given the
coarse bin. This file proves the counting form of that transfer.

`transfer_core`: if the value `J` is listed by the fine bin `Y` and (together with the coarse
bin) by the coefficient bin `X`, every coarse bin contains only the fine bins of its list
`Yset`, and inside every set of coefficient bins each fine bin has relative mass at most
`c₀ / M`, then the values `j` of a coarse bin `z` that are listed by at most `θ M` of its fine
bins ("light" values) carry mass at most `θ c₀ K₀ ν(L)`; `card_heavyVals_le` bounds the number
of the other ("heavy") values of a coarse bin by `K² / θ` when lists have size `≤ K` and every
coarse bin has at most `K M` fine bins.

`success_restriction`: the relative fine-bin bound inside coefficient bins follows from an
absolute one (relative to the full prior mass of each coefficient bin) after deleting the
coefficient bins of low success fraction `< s₀`, at mass cost `s₀ ν(univ)`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

/-- Double counting in a finite incidence relation. -/
theorem sum_card_filter_mem {S T : Finset ℤ} {f : ℤ → Finset ℤ} :
    ∑ j ∈ S, ((T.filter (fun c => j ∈ f c)).card : ℝ) =
      ∑ c ∈ T, ((S.filter (fun j => j ∈ f c)).card : ℝ) := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

/-- The heavy values of a coarse bin: those listed by more than `θ M` of its fine bins. -/
def heavyVals (Yset : ℤ → Finset ℤ) (listY : ℤ → Finset ℤ) (θ M : ℝ) (z : ℤ) : Finset ℤ :=
  ((Yset z).biUnion listY).filter
    (fun j => θ * M < (((Yset z).filter (fun c => j ∈ listY c)).card : ℝ))

theorem card_heavyVals_le {Yset listY : ℤ → Finset ℤ} {θ M K : ℝ} (hθ : 0 < θ) (hM : 0 < M)
    (hK : 0 ≤ K) (h1c : ∀ c, ((listY c).card : ℝ) ≤ K) (z : ℤ)
    (h4c : ((Yset z).card : ℝ) ≤ K * M) :
    ((heavyVals Yset listY θ M z).card : ℝ) ≤ K * K / θ := by
  classical
  set S := (Yset z).biUnion listY with hS
  set Hv := heavyVals Yset listY θ M z with hHv
  have hsub : Hv ⊆ S := Finset.filter_subset _ _
  have hlow : (Hv.card : ℝ) * (θ * M) ≤
      ∑ j ∈ Hv, (((Yset z).filter (fun c => j ∈ listY c)).card : ℝ) := by
    have : ∑ _j ∈ Hv, θ * M ≤ ∑ j ∈ Hv, (((Yset z).filter (fun c => j ∈ listY c)).card : ℝ) :=
      Finset.sum_le_sum (fun j hj => le_of_lt (Finset.mem_filter.mp hj).2)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hmono : ∑ j ∈ Hv, (((Yset z).filter (fun c => j ∈ listY c)).card : ℝ) ≤
      ∑ j ∈ S, (((Yset z).filter (fun c => j ∈ listY c)).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  have hdc := sum_card_filter_mem (S := S) (T := Yset z) (f := listY)
  have hcol : ∑ c ∈ Yset z, ((S.filter (fun j => j ∈ listY c)).card : ℝ) ≤
      (Yset z).card * K := by
    have : ∑ c ∈ Yset z, ((S.filter (fun j => j ∈ listY c)).card : ℝ) ≤ ∑ _c ∈ Yset z, K := by
      apply Finset.sum_le_sum
      intro c _
      have : (S.filter (fun j => j ∈ listY c)).card ≤ (listY c).card := by
        apply Finset.card_le_card
        intro j hj
        exact (Finset.mem_filter.mp hj).2
      exact (Nat.cast_le.mpr this).trans (h1c c)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have htot : (Hv.card : ℝ) * (θ * M) ≤ K * M * K := by
    calc (Hv.card : ℝ) * (θ * M) ≤ _ := hlow
      _ ≤ _ := hmono
      _ = _ := hdc
      _ ≤ (Yset z).card * K := hcol
      _ ≤ K * M * K := mul_le_mul_of_nonneg_right h4c hK
  rw [le_div_iff₀ hθ]
  have hθM : 0 < θ * M := mul_pos hθ hM
  have h' : (Hv.card : ℝ) * θ * M ≤ K * K * M := by nlinarith
  have hM' : 0 < M := hM
  by_contra hcon
  push_neg at hcon
  have : K * K * M < (Hv.card : ℝ) * θ * M := by nlinarith
  linarith

/-- Sum of measures of finitely many sets of bounded multiplicity inside `L`. -/
theorem sum_measure_le_of_multiplicity {Ω κ : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (s : Finset κ) (A : κ → Set Ω) (hA : ∀ i, MeasurableSet (A i)) {L : Set Ω}
    (hL : MeasurableSet L) (hAL : ∀ i, A i ⊆ L) (m : ℕ)
    (hm : ∀ l ∈ L, ∃ t : Finset κ, t.card ≤ m ∧ ∀ i ∈ s, l ∈ A i → i ∈ t) :
    ∑ i ∈ s, ν (A i) ≤ m * ν L := by
  classical
  have h1 : ∀ i, ν (A i) = ∫⁻ l, (A i).indicator 1 l ∂ν := fun i =>
    (lintegral_indicator_one (hA i)).symm
  simp_rw [h1]
  rw [← lintegral_finset_sum _ (fun i _ => measurable_one.indicator (hA i))]
  have h2 : m * ν L = ∫⁻ l, L.indicator (fun _ => (m : ENNReal)) l ∂ν := by
    rw [lintegral_indicator_const hL]
  rw [h2]
  refine lintegral_mono (fun l => ?_)
  simp only [Finset.sum_apply]
  by_cases hl : l ∈ L
  · rw [indicator_of_mem hl]
    obtain ⟨t, ht, hst⟩ := hm l hl
    have : ∑ i ∈ s, (A i).indicator (1 : Ω → ENNReal) l =
        ((s.filter (fun i => l ∈ A i)).card : ENNReal) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : l ∈ A i
      · simp [hi]
      · simp [hi]
    rw [this]
    have hsub : s.filter (fun i => l ∈ A i) ⊆ t := by
      intro i hi
      obtain ⟨his, hli⟩ := Finset.mem_filter.mp hi
      exact hst i his hli
    exact_mod_cast (Finset.card_le_card hsub).trans ht
  · rw [indicator_of_notMem hl]
    have : ∀ i ∈ s, (A i).indicator (1 : Ω → ENNReal) l = 0 := fun i _ =>
      indicator_of_notMem (fun h => hl (hAL i h)) _
    rw [Finset.sum_eq_zero this]

/-- The counting form of the fine-to-coarse transfer. -/
theorem transfer_core {Ω ι : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {L : Set Ω} (hL : MeasurableSet L) {X : Ω → ι} {Y Z J : Ω → ℤ}
    (hX : ∀ s : Set ι, MeasurableSet (X ⁻¹' s))
    {listY : ℤ → Finset ℤ} {listX zlist : ι → Finset ℤ} {Yset : ℤ → Finset ℤ} {Zs : Finset ℤ}
    {M θ c₀ : ℝ} {K₀ : ℕ} (hM : 0 < M) (hc₀ : 0 ≤ c₀)
    (hZs : ∀ l ∈ L, Z l ∈ Zs)
    (h1 : ∀ l ∈ L, J l ∈ listY (Y l))
    (h2 : ∀ l ∈ L, J l ∈ listX (X l) ∧ Z l ∈ zlist (X l))
    (h2c : ∀ x, (listX x).card * (zlist x).card ≤ K₀)
    (h4 : ∀ l ∈ L, Y l ∈ Yset (Z l))
    (h5 : ∀ (s : Set ι) (c : ℤ),
      ν (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' s) ≤ ENNReal.ofReal (c₀ / M) * ν (L ∩ X ⁻¹' s)) :
    ν (L ∩ {l | J l ∉ heavyVals Yset listY θ M (Z l)}) ≤
      ENNReal.ofReal (θ * c₀) * (K₀ * ν L) := by
  classical
  -- coefficient bins compatible with a value `j` in the coarse bin `z`
  let Xs : ℤ → ℤ → Set ι := fun z j => {x | j ∈ listX x ∧ z ∈ zlist x}
  let C : ℤ → ℤ → Finset ℤ := fun z j => (Yset z).filter (fun c => j ∈ listY c)
  let light : ℤ → Finset ℤ := fun z => ((Yset z).biUnion listY) \ heavyVals Yset listY θ M z
  let P : Finset (Σ _ : ℤ, ℤ) := Zs.sigma light
  have hcover : L ∩ {l | J l ∉ heavyVals Yset listY θ M (Z l)} ⊆
      ⋃ i ∈ P, ⋃ c ∈ C i.1 i.2, (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' (Xs i.1 i.2)) := by
    intro l ⟨hl, hlight⟩
    have hz := hZs l hl
    have hy := h4 l hl
    have hj := h1 l hl
    obtain ⟨hjx, hzx⟩ := h2 l hl
    refine mem_iUnion₂.mpr ⟨⟨Z l, J l⟩, Finset.mem_sigma.mpr ⟨hz, ?_⟩,
      mem_iUnion₂.mpr ⟨Y l, ?_, ?_⟩⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨Y l, hy, hj⟩, hlight⟩
    · exact Finset.mem_filter.mpr ⟨hy, hj⟩
    · exact ⟨⟨hl, rfl⟩, hjx, hzx⟩
  have hpiece : ∀ i ∈ P,
      ν (⋃ c ∈ C i.1 i.2, (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' (Xs i.1 i.2))) ≤
        ENNReal.ofReal (θ * c₀) * ν (L ∩ X ⁻¹' (Xs i.1 i.2)) := by
    intro i hi
    have hj := (Finset.mem_sigma.mp hi).2
    have hlight : ¬ θ * M < ((C i.1 i.2).card : ℝ) := by
      intro hh
      exact (Finset.mem_sdiff.mp hj).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, hh⟩)
    have hcard : ((C i.1 i.2).card : ℝ) ≤ θ * M := le_of_not_gt hlight
    calc ν (⋃ c ∈ C i.1 i.2, (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' (Xs i.1 i.2)))
        ≤ ∑ c ∈ C i.1 i.2, ν (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' (Xs i.1 i.2)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _c ∈ C i.1 i.2, ENNReal.ofReal (c₀ / M) * ν (L ∩ X ⁻¹' (Xs i.1 i.2)) :=
          Finset.sum_le_sum (fun c _ => h5 _ c)
      _ = ENNReal.ofReal ((C i.1 i.2).card * (c₀ / M)) * ν (L ∩ X ⁻¹' (Xs i.1 i.2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (θ * c₀) * ν (L ∩ X ⁻¹' (Xs i.1 i.2)) := by
          apply mul_le_mul_left
          apply ENNReal.ofReal_le_ofReal
          calc ((C i.1 i.2).card : ℝ) * (c₀ / M) ≤ θ * M * (c₀ / M) :=
                mul_le_mul_of_nonneg_right hcard (div_nonneg hc₀ hM.le)
            _ = θ * c₀ := by field_simp
  have hsum : ∑ i ∈ P, ν (L ∩ X ⁻¹' (Xs i.1 i.2)) ≤ K₀ * ν L := by
    apply sum_measure_le_of_multiplicity ν P (fun i => L ∩ X ⁻¹' (Xs i.1 i.2))
      (fun i => hL.inter (hX _)) hL (fun i => inter_subset_left) K₀
    intro l hl
    refine ⟨((zlist (X l)).sigma (fun _ => listX (X l))), ?_, ?_⟩
    · calc ((zlist (X l)).sigma (fun _ => listX (X l))).card
          = (zlist (X l)).card * (listX (X l)).card := by
            rw [Finset.card_sigma, Finset.sum_const, smul_eq_mul]
        _ ≤ K₀ := by rw [mul_comm]; exact h2c (X l)
    · intro i _ hi
      obtain ⟨-, hjx, hzx⟩ := hi
      exact Finset.mem_sigma.mpr ⟨hzx, hjx⟩
  calc ν (L ∩ {l | J l ∉ heavyVals Yset listY θ M (Z l)})
      ≤ ν (⋃ i ∈ P, ⋃ c ∈ C i.1 i.2, (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' (Xs i.1 i.2))) :=
        measure_mono hcover
    _ ≤ ∑ i ∈ P, ν (⋃ c ∈ C i.1 i.2, (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' (Xs i.1 i.2))) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ P, ENNReal.ofReal (θ * c₀) * ν (L ∩ X ⁻¹' (Xs i.1 i.2)) :=
        Finset.sum_le_sum hpiece
    _ = ENNReal.ofReal (θ * c₀) * ∑ i ∈ P, ν (L ∩ X ⁻¹' (Xs i.1 i.2)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (θ * c₀) * (K₀ * ν L) := by gcongr

/-- Deleting coefficient bins of low success fraction turns an absolute fine-bin bound
(relative to the full prior mass of each coefficient bin) into a relative one. -/
theorem success_restriction {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {ν : Measure Ω} {L : Set Ω} (hL : MeasurableSet L) {X : Ω → ι} {Y : Ω → ℤ}
    (hX : ∀ s : Set ι, MeasurableSet (X ⁻¹' s)) (hY : Measurable Y)
    {a s₀ : ℝ} (ha : 0 ≤ a) (hs₀ : 0 < s₀)
    (h5 : ∀ (x : ι) (c : ℤ), ν (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' {x}) ≤ ENNReal.ofReal a * ν (X ⁻¹' {x})) :
    let good : Set ι := {x | ENNReal.ofReal s₀ * ν (X ⁻¹' {x}) ≤ ν (L ∩ X ⁻¹' {x})}
    ν (L \ (L ∩ X ⁻¹' good)) ≤ ENNReal.ofReal s₀ * ν univ ∧
      ∀ (S : Set ι) (c : ℤ), ν ((L ∩ X ⁻¹' good) ∩ Y ⁻¹' {c} ∩ X ⁻¹' S) ≤
        ENNReal.ofReal (a / s₀) * ν ((L ∩ X ⁻¹' good) ∩ X ⁻¹' S) := by
  classical
  intro good
  have hsing : ∀ x : ι, MeasurableSet (X ⁻¹' {x}) := fun x => hX {x}
  -- measure of a preimage as a sum over the countable index type
  have hdecomp : ∀ (A : Set Ω), MeasurableSet A → ∀ S : Set ι,
      ν (A ∩ X ⁻¹' S) = ∑' x : S, ν (A ∩ X ⁻¹' {(x : ι)}) := by
    intro A hA S
    have : A ∩ X ⁻¹' S = ⋃ x : S, A ∩ X ⁻¹' {(x : ι)} := by
      ext l
      simp only [mem_inter_iff, mem_preimage, mem_iUnion, mem_singleton_iff, Subtype.exists,
        exists_prop]
      constructor
      · rintro ⟨hl, hs⟩; exact ⟨X l, hs, hl, rfl⟩
      · rintro ⟨x, hx, hl, rfl⟩; exact ⟨hl, hx⟩
    rw [this, measure_iUnion]
    · intro x y hxy
      refine Set.disjoint_left.mpr ?_
      rintro l ⟨-, hlx⟩ ⟨-, hly⟩
      exact hxy (Subtype.ext ((hlx.symm.trans hly)))
    · intro x; exact hA.inter (hsing x)
  constructor
  · -- the deleted part lies in the bad coefficient bins
    have hdiff : L \ (L ∩ X ⁻¹' good) = L ∩ X ⁻¹' goodᶜ := by
      ext l; simp [mem_inter_iff, mem_preimage]
    rw [hdiff, hdecomp L hL goodᶜ]
    calc ∑' x : (goodᶜ : Set ι), ν (L ∩ X ⁻¹' {(x : ι)})
        ≤ ∑' x : (goodᶜ : Set ι), ENNReal.ofReal s₀ * ν (X ⁻¹' {(x : ι)}) := by
          apply ENNReal.tsum_le_tsum
          intro x
          exact le_of_lt (not_le.mp x.2)
      _ = ENNReal.ofReal s₀ * ∑' x : (goodᶜ : Set ι), ν (X ⁻¹' {(x : ι)}) := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal s₀ * ν (X ⁻¹' goodᶜ) := by
          congr 1
          have := hdecomp univ MeasurableSet.univ goodᶜ
          simpa only [univ_inter] using this.symm
      _ ≤ ENNReal.ofReal s₀ * ν univ := by gcongr; exact subset_univ _
  · intro S c
    have hLg : MeasurableSet (L ∩ X ⁻¹' good) := hL.inter (hX good)
    have hYc : MeasurableSet (Y ⁻¹' {c}) := hY (measurableSet_singleton c)
    rw [hdecomp _ (hLg.inter hYc) S, hdecomp _ hLg S, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro x
    by_cases hx : (x : ι) ∈ good
    · have hgx : ENNReal.ofReal s₀ * ν (X ⁻¹' {(x : ι)}) ≤ ν (L ∩ X ⁻¹' {(x : ι)}) := hx
      have heq1 : (L ∩ X ⁻¹' good) ∩ Y ⁻¹' {c} ∩ X ⁻¹' {(x : ι)} =
          L ∩ Y ⁻¹' {c} ∩ X ⁻¹' {(x : ι)} := by
        ext l
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨⟨hl, -⟩, hc⟩, hxl⟩; exact ⟨⟨hl, hc⟩, hxl⟩
        · rintro ⟨⟨hl, hc⟩, hxl⟩; exact ⟨⟨⟨hl, by rw [hxl]; exact hx⟩, hc⟩, hxl⟩
      have heq2 : (L ∩ X ⁻¹' good) ∩ X ⁻¹' {(x : ι)} = L ∩ X ⁻¹' {(x : ι)} := by
        ext l
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨hl, -⟩, hxl⟩; exact ⟨hl, hxl⟩
        · rintro ⟨hl, hxl⟩; exact ⟨⟨hl, by rw [hxl]; exact hx⟩, hxl⟩
      rw [heq1, heq2]
      calc ν (L ∩ Y ⁻¹' {c} ∩ X ⁻¹' {(x : ι)}) ≤ ENNReal.ofReal a * ν (X ⁻¹' {(x : ι)}) :=
            h5 x c
        _ = ENNReal.ofReal (a / s₀) * (ENNReal.ofReal s₀ * ν (X ⁻¹' {(x : ι)})) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg ha hs₀.le)]
            congr 2
            field_simp
        _ ≤ ENNReal.ofReal (a / s₀) * ν (L ∩ X ⁻¹' {(x : ι)}) := by gcongr
    · have hempty : (L ∩ X ⁻¹' good) ∩ Y ⁻¹' {c} ∩ X ⁻¹' {(x : ι)} = ∅ := by
        refine Set.eq_empty_of_forall_notMem ?_
        intro l hl
        have hg : X l ∈ good := hl.1.1.2
        have hxl : X l = (x : ι) := hl.2
        rw [hxl] at hg
        exact hx hg
      rw [hempty, measure_empty]
      exact bot_le

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
