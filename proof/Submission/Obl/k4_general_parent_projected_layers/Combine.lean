import Submission.Obl.k4_general_parent_projected_layers.Layers
import Submission.Obl.k4_general_parent_projected_layers.WidthBins

/-!
# Merging group layers into one layer of common width

Scalar returns one width per group. Groups whose normalized widths lie in one
power-grid class (`widthBin`, ratio `N^τ`) are merged into a single layer whose
common width is the lower end of the class: fits lose at most `N^τ`, the moving
norms only shrink and the floors are unchanged. The class carrying the most
covered mass keeps at least a `1 / #classes` share.
-/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial

noncomputable section

namespace ProjLayer

variable {α : Type} [MeasurableSpace α]

theorem covered_eq (L : ProjLayer α) : L.covered = ⋃ i, L.C i ×ˢ (univ : Set ℝ) := by
  ext z
  simp [covered]

theorem measurableSet_covered {L : ProjLayer α} (h : ∀ i, MeasurableSet (L.C i)) :
    MeasurableSet L.covered := by
  rw [covered_eq]
  exact MeasurableSet.iUnion fun i => (h i).prod MeasurableSet.univ

/-- The layer made of all pieces of the layers `L u`, `u ∈ Q`, with one common width. -/
def merge {ι : Type*} (Q : Finset ι) (L : ι → ProjLayer α) (β : ℝ) : ProjLayer α :=
  let e := Fintype.equivFin (Σ u : Q, Fin (L u).n)
  { n := Fintype.card (Σ u : Q, Fin (L u).n)
    β := β
    C := fun i => (L (e.symm i).1).C (e.symm i).2
    tag := fun i => (L (e.symm i).1).tag (e.symm i).2
    u := fun i => (L (e.symm i).1).u (e.symm i).2
    v := fun i => (L (e.symm i).1).v (e.symm i).2
    G := fun i => (L (e.symm i).1).G (e.symm i).2 }

theorem merge_covered {ι : Type*} (Q : Finset ι) (L : ι → ProjLayer α) (β : ℝ) :
    (merge Q L β).covered = ⋃ u ∈ Q, (L u).covered := by
  ext z
  simp only [covered, merge, Set.mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, ((Fintype.equivFin _).symm i).1.2, _, hi⟩
  · rintro ⟨u, hu, i, hi⟩
    refine ⟨Fintype.equivFin (Σ u : Q, Fin (L u).n) ⟨⟨u, hu⟩, i⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hi

/-- Merging layers of comparable widths at the lower end of their common class. -/
theorem merge_good {ι : Type*} (Q : Finset ι) (L : ι → ProjLayer α)
    {N E d ell La s χ τ β : ℝ} {b : α → Fin 6 → ℝ} {P : MvPolynomial (Fin 4) ℝ}
    {π : Measure ℝ} {ρ : Measure (α × ℝ)}
    (hN : 1 ≤ N) (hτ : 0 ≤ τ) (hE : 0 < E) (hχ : 0 ≤ χ) (hβ : 0 < β)
    (hβlo : N ^ (-ell * s) * N ^ (-La) / (E * N ^ τ) ≤ β)
    (hβhi : β ≤ E * N ^ τ * N ^ (-ell * s))
    (hdisj : ∀ u ∈ Q, ∀ u' ∈ Q, u ≠ u' → ∀ i i', Disjoint ((L u).C i) ((L u').C i'))
    (hgood : ∀ u ∈ Q, (L u).Good N E d ell La s χ b P π ρ)
    (hlo : ∀ u ∈ Q, β ≤ (L u).β) (hhi : ∀ u ∈ Q, (L u).β ≤ N ^ τ * β) :
    (merge Q L β).Good N (E * N ^ τ) d ell La s χ b P π ρ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : 1 ≤ N ^ τ := Real.one_le_rpow hN hτ
  have hEE : E ≤ E * N ^ τ := le_mul_of_one_le_right hE.le hpow
  have hNs : 0 ≤ N ^ (-s) := Real.rpow_nonneg hN0.le _
  set e := Fintype.equivFin (Σ u : Q, Fin (L u).n) with he
  refine ⟨hβ, hβlo, hβhi, ?_, ?_, ?_⟩
  · intro i
    dsimp only [merge]
    rw [← he]
    generalize e.symm i = x
    obtain ⟨⟨u, hu⟩, j⟩ := x
    exact (hgood u hu).2.2.2.1 j
  · intro i i' hii'
    dsimp only [merge]
    rw [← he]
    have hne : e.symm i ≠ e.symm i' := fun h => hii' (e.symm.injective h)
    generalize e.symm i = x at hne ⊢
    generalize e.symm i' = x' at hne ⊢
    obtain ⟨⟨u, hu⟩, j⟩ := x
    obtain ⟨⟨u', hu'⟩, j'⟩ := x'
    by_cases huu : u = u'
    · subst huu
      have hjj : j ≠ j' := by
        intro hjj
        subst hjj
        exact hne rfl
      exact (hgood u hu).2.2.2.2.1 j j' hjj
    · exact hdisj u hu u' hu' huu j j'
  · intro i
    dsimp only [merge]
    rw [← he]
    generalize e.symm i = x
    obtain ⟨⟨u, hu⟩, j⟩ := x
    obtain ⟨huv, hdeg, hnorm, hfit, hfloor⟩ := (hgood u hu).2.2.2.2.2 j
    have hβu : β ≤ (L u).β := hlo u hu
    have hβu' : (L u).β ≤ N ^ τ * β := hhi u hu
    refine ⟨huv.trans hEE, hdeg, ?_, ?_, ?_⟩
    · intro t ht w hw
      -- a smaller width stays inside the group's moving band
      have hr₀ : 0 ≤ β / (L u).β := div_nonneg hβ.le (hβ.le.trans hβu)
      have hr₁ : β / (L u).β ≤ 1 := (div_le_one (hβ.trans_le hβu)).mpr hβu
      have hww : |w| ≤ 1 := abs_le.mpr hw
      have hscaled : β / (L u).β * w ∈ Icc (-1 : ℝ) 1 := by
        apply abs_le.mp
        rw [abs_mul, abs_of_nonneg hr₀]
        simpa only [one_mul] using mul_le_mul hr₁ hww (abs_nonneg _) zero_le_one
      have H := hnorm t ht _ hscaled
      have heq : (L u).β * (β / (L u).β * w) = β * w := by
        field_simp [(hβ.trans_le hβu).ne']
      rw [heq] at H
      exact H.trans hEE
    · intro l hl
      obtain ⟨h0, h1, ht⟩ := hfit l hl
      refine ⟨h0, h1, fun t htI => ⟨?_, (ht t htI).2.trans
        (mul_le_mul_of_nonneg_right hEE hNs)⟩⟩
      calc _ ≤ E * (L u).β := (ht t htI).1
        _ ≤ E * (N ^ τ * β) := mul_le_mul_of_nonneg_left hβu' hE.le
        _ = E * N ^ τ * β := by ring
    · refine le_trans ?_ hfloor
      gcongr ENNReal.ofReal ?_ * _
      have hc : 0 ≤ χ * (N ^ (-s)) ^ d := mul_nonneg hχ (Real.rpow_nonneg hNs _)
      calc χ * (N ^ (-s)) ^ d * β / (E * N ^ τ) ≤ χ * (N ^ (-s)) ^ d * β / E :=
            div_le_div_of_nonneg_left (mul_nonneg hc hβ.le) hE hEE
        _ ≤ χ * (N ^ (-s)) ^ d * (L u).β / E := by gcongr

/-- Covered mass of disjoint group layers adds up. -/
theorem measure_merge_covered {ι : Type*} (Q : Finset ι) (L : ι → ProjLayer α) (β : ℝ)
    (ζ : Measure (α × ℝ))
    (hmeas : ∀ u ∈ Q, ∀ i, MeasurableSet ((L u).C i))
    (hdisj : ∀ u ∈ Q, ∀ u' ∈ Q, u ≠ u' → ∀ i i', Disjoint ((L u).C i) ((L u').C i')) :
    ζ (merge Q L β).covered = ∑ u ∈ Q, ζ (L u).covered := by
  rw [merge_covered]
  apply measure_biUnion_finset
  · intro u hu u' hu' huu
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨i, hi⟩ ⟨i', hi'⟩
    exact Set.disjoint_left.mp (hdisj u hu u' hu' huu i i') hi hi'
  · intro u hu
    exact measurableSet_covered (hmeas u hu)

/-- Among finitely many group layers with pairwise disjoint pieces and normalized
widths in `[N^(-A), N^B]`, the groups of one power-grid width class merge into a single
layer of common width carrying at least a `1 / #classes` share of the covered mass. -/
theorem exists_merged_layer {ι : Type*} [DecidableEq ι] (Q : Finset ι) (L : ι → ProjLayer α)
    {N E d ell La s χ τ A B : ℝ} {b : α → Fin 6 → ℝ} {P : MvPolynomial (Fin 4) ℝ}
    {π : Measure ℝ} {ρ : Measure (α × ℝ)} (ζ : Measure (α × ℝ))
    (hN : 1 < N) (hτ : 0 < τ) (hE : 1 ≤ E) (hχ : 0 ≤ χ) (hLa : 0 ≤ La)
    (hdisj : ∀ u ∈ Q, ∀ u' ∈ Q, u ≠ u' → ∀ i i', Disjoint ((L u).C i) ((L u').C i'))
    (hgood : ∀ u ∈ Q, (L u).Good N E d ell La s χ b P π ρ)
    (hwidth : ∀ u ∈ Q, N ^ (-A) ≤ (L u).β / N ^ (-ell * s) ∧
      (L u).β / N ^ (-ell * s) ≤ N ^ B) :
    ∃ L' : ProjLayer α, L'.Good N (E * N ^ τ) d ell La s χ b P π ρ ∧
      (∑ u ∈ Q, ζ (L u).covered) ≤ ((widthIndices A B τ).card : ENNReal) * ζ L'.covered := by
  classical
  have hN1 : 1 ≤ N := hN.le
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  set g := N ^ (-ell * s) with hgdef
  have hg : 0 < g := Real.rpow_pos_of_pos hN0 _
  have hpowτ : 1 ≤ N ^ τ := Real.one_le_rpow hN1 hτ.le
  have hpowτ0 : 0 < N ^ τ := Real.rpow_pos_of_pos hN0 τ
  have hmeas : ∀ u ∈ Q, ∀ i, MeasurableSet ((L u).C i) := fun u hu => (hgood u hu).2.2.2.1
  rcases Q.eq_empty_or_nonempty with hQ | hQ
  · -- no groups: an empty layer of width `g`
    subst hQ
    refine ⟨merge ∅ L g, ?_, by simp⟩
    apply merge_good ∅ L hN1 hτ.le hE0 hχ hg
    · have h1 : N ^ (-La) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      have h2 : 1 ≤ E * N ^ τ := one_le_mul_of_one_le_of_one_le hE hpowτ
      rw [div_le_iff₀ (by positivity)]
      calc g * N ^ (-La) ≤ g * 1 := mul_le_mul_of_nonneg_left h1 hg.le
        _ ≤ g * (E * N ^ τ) := mul_le_mul_of_nonneg_left h2 hg.le
    · have h2 : 1 ≤ E * N ^ τ := one_le_mul_of_one_le_of_one_le hE hpowτ
      nlinarith
    all_goals simp
  · let bin : ι → ℤ := fun u => widthBin N τ ((L u).β / g)
    let J := Q.image bin
    let F : ℤ → ENNReal := fun j => ∑ u ∈ Q with bin u = j, ζ (L u).covered
    have hJ : J.Nonempty := hQ.image bin
    obtain ⟨j₀, hj₀J, hj₀max⟩ := J.exists_max_image F hJ
    obtain ⟨u₀, hu₀, hu₀j⟩ := Finset.mem_image.mp hj₀J
    set Q' := Q.filter (fun u => bin u = j₀) with hQ'
    set β := g * N ^ (τ * (j₀ : ℝ)) with hβdef
    have hβ : 0 < β := mul_pos hg (Real.rpow_pos_of_pos hN0 _)
    have hβu : ∀ u ∈ Q', β ≤ (L u).β ∧ (L u).β ≤ N ^ τ * β := by
      intro u hu
      obtain ⟨hu, hbin⟩ := Finset.mem_filter.mp hu
      have hpos : 0 < (L u).β / g := div_pos (hgood u hu).1 hg
      obtain ⟨h1, h2⟩ := widthBin_bounds hN hτ hpos
      change widthBin N τ ((L u).β / g) = j₀ at hbin
      rw [hbin] at h1 h2
      constructor
      · rw [hβdef, mul_comm]
        exact (le_div_iff₀ hg).mp h1
      · have h3 : N ^ (τ * ((j₀ : ℝ) + 1)) = N ^ τ * N ^ (τ * (j₀ : ℝ)) := by
          rw [← Real.rpow_add hN0]; ring_nf
        rw [h3] at h2
        calc (L u).β = (L u).β / g * g := by field_simp
          _ ≤ N ^ τ * N ^ (τ * (j₀ : ℝ)) * g := mul_le_mul_of_nonneg_right h2 hg.le
          _ = N ^ τ * β := by rw [hβdef]; ring
    have hu₀' : u₀ ∈ Q' := Finset.mem_filter.mpr ⟨hu₀, hu₀j⟩
    have hgood' : ∀ u ∈ Q', (L u).Good N E d ell La s χ b P π ρ :=
      fun u hu => hgood u (Finset.mem_filter.mp hu).1
    have hdisj' : ∀ u ∈ Q', ∀ u' ∈ Q', u ≠ u' → ∀ i i', Disjoint ((L u).C i) ((L u').C i') :=
      fun u hu u' hu' => hdisj u (Finset.mem_filter.mp hu).1 u' (Finset.mem_filter.mp hu').1
    refine ⟨merge Q' L β, ?_, ?_⟩
    · apply merge_good Q' L hN1 hτ.le hE0 hχ hβ _ _ hdisj' hgood'
        (fun u hu => (hβu u hu).1) (fun u hu => (hβu u hu).2)
      · -- the lower width bound from the group `u₀`
        have hlo := (hgood u₀ hu₀).2.1
        have hhi := (hβu u₀ hu₀').2
        rw [div_le_iff₀ (mul_pos hE0 hpowτ0)]
        rw [div_le_iff₀ hE0] at hlo
        calc g * N ^ (-La) ≤ (L u₀).β * E := hlo
          _ ≤ N ^ τ * β * E := mul_le_mul_of_nonneg_right hhi hE0.le
          _ = β * (E * N ^ τ) := by ring
      · have h1 := (hβu u₀ hu₀').1
        have h2 := (hgood u₀ hu₀).2.2.1
        calc β ≤ (L u₀).β := h1
          _ ≤ E * g := h2
          _ ≤ E * N ^ τ * g := by
            apply mul_le_mul_of_nonneg_right _ hg.le
            exact le_mul_of_one_le_right hE0.le hpowτ
    · rw [measure_merge_covered Q' L β ζ (fun u hu => hmeas u (Finset.mem_filter.mp hu).1) hdisj']
      have hsub : J ⊆ widthIndices A B τ := by
        intro j hj
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
        exact widthBin_mem hN hτ (div_pos (hgood u hu).1 hg) (hwidth u hu).1 (hwidth u hu).2
      calc (∑ u ∈ Q, ζ (L u).covered) = ∑ j ∈ J, F j :=
            (Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image_of_mem bin hu) _).symm
        _ ≤ ∑ j ∈ J, F j₀ := Finset.sum_le_sum fun j hj => hj₀max j hj
        _ = (J.card : ENNReal) * F j₀ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((widthIndices A B τ).card : ENNReal) * F j₀ := by
            gcongr

end ProjLayer

end

end Submission.Obl.k4_general_parent_projected_layers
