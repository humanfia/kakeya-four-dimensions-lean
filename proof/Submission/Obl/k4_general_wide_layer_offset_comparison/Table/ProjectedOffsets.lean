import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.GoodDataOfAE
import Submission.Obl.k4_general_wide_layer_offset_comparison.ActualProjectedComparison
import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparedProjectedOffsets

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

private theorem long_fiber_bounds (hp : p.Valid) {k : ℕ} {r u s m H Hf : ℝ}
    {A F : ProjectedLayer α} (hA : A.Valid p k r m H) (hF : F.Valid p k s m H)
    (hH : 0 < H) (hHH : H ≤ Hf) (hu : 0 ≤ u) (hrs : r ≤ s) (hsu : s ≤ r + u) :
    longTime A.β F.β * longSlope A.β F.β = longWidth A.β F.β ∧
    p.N k ^ (-p.ℓ * (r + u)) / Hf ≤ longWidth A.β F.β ∧
    longSlope A.β F.β ≤ Hf * p.N k ^ (-p.ℓ * r) := by
  have hN : 1 ≤ p.N k := by linarith [hp.scale k]
  have hN0 : 0 < p.N k := zero_lt_one.trans_le hN
  have hHf : 0 < Hf := hH.trans_le hHH
  have hpow (a b : ℝ) (hab : a ≤ b) : p.N k ^ (-p.ℓ * b) ≤ p.N k ^ (-p.ℓ * a) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith [hp.transverse_pos])
  have hmin (a : ℝ) (ha : a ≤ r + u) {β : ℝ}
      (hβ : p.N k ^ (-p.ℓ * a) / H ≤ β) :
      p.N k ^ (-p.ℓ * (r + u)) / Hf ≤ β := by
    exact ((div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) hH hHH).trans
      (div_le_div_of_nonneg_right (hpow _ _ ha) hH.le)).trans hβ
  refine ⟨div_mul_cancel₀ _ (ne_of_gt (hA.1.trans_le (le_max_left _ _))),
    le_min (hmin r (by linarith) hA.2.1) (hmin s hsu hF.2.1), ?_⟩
  apply max_le
  · exact hA.2.2.1.trans (mul_le_mul_of_nonneg_right hHH (by positivity))
  · exact hF.2.2.1.trans ((mul_le_mul_of_nonneg_left (hpow _ _ hrs) hH.le).trans
      (mul_le_mul_of_nonneg_right hHH (by positivity)))

/-- Both projected comparisons use one original exceptional event. On its
complement their canonical offsets hold for every literal occurring label
on the whole fiber with the already chosen final height. -/
theorem eventually_projected_table_offsets (hp : p.Valid)
    (hMatch : Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Matching)
    {r u v m : ℝ} (hr : 0 < r) (hu : 0 < u) (hv : 0 ≤ v) (hvu : v ≤ u)
    (hU : r + u ≤ p.U) (hm0 : 0 < m) (hm : (p.κ + p.ℓ) * r < m)
    (hgap : (10 / (1 - p.d) + 1 + p.ℓ) * u < p.κ * r)
    (H Hf : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k) (hKH : ∀ k, p.K k ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    (hHf : ∀ k, 2 ≤ Hf k) (hKHf : ∀ k, p.K k ≤ Hf k)
    (hHH : ∀ k, H k ≤ Hf k)
    (hHfs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Hf k ≤ p.N k ^ ε)
    (σ : ℕ → Measure (α × ℝ)) (hσ : ∀ k, σ k ≤ p.ρ k)
    (L : ℕ → Fin 3 → ProjectedLayer α)
    (hL : ∀ k a, (L k a).Valid p k (![r, r + u, r + v] a) m (H k))
    (hcover : ∀ k a, (L k a).Covers (σ k)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∃ E : Set (α × ℝ), MeasurableSet E ∧ σ k E ≤ ENNReal.ofReal (2 * p.N k ^ (-c)) ∧
        ∀ᵐ ω ∂(σ k).restrict Eᶜ, ∀ R : ℝ, p.AtDepth k r R →
          p.LayerOffsetsAt k r u v m (Hf k) (L k) ω := by
  let gain : Fin 2 → ℝ := ![u, v]
  have hgain (c : Fin 2) : 0 ≤ gain c ∧ gain c ≤ u := by
    fin_cases c
    · exact ⟨hu.le, le_rfl⟩
    · exact ⟨hv, hvu⟩
  have hdepth (c : Fin 2) : (![r, r + u, r + v] c.succ) = r + gain c := by
    fin_cases c <;> rfl
  have hpair (c : Fin 2) : ∃ e : ℝ, 0 < e ∧ ∀ᶠ k in atTop,
      ∃ f : ProjectedComparisonFrame p k r (r + gain c) m (H k)
        (longTime (L k 0).β (L k c.succ).β) (longSlope (L k 0).β (L k c.succ).β)
        (longWidth (L k 0).β (L k c.succ).β) (σ k),
        f.coarse = L k 0 ∧ f.fine = L k c.succ ∧
        σ k (f.bad (4 * H k * p.N k ^ (-r) * p.N k ^ (10 / (1 - p.d) * u))) ≤
          ENNReal.ofReal (p.N k ^ (-e)) := by
    have hvalid : ∀ k, (L k c.succ).Valid p k (r + gain c) m (H k) := by
      intro k
      rw [← hdepth c]
      exact hL k c.succ
    obtain ⟨e, he, C, hC, hf⟩ := p.actual_projected_comparison hp hMatch hr
      (by linarith [(hgain c).1]) (by linarith [(hgain c).2]) hm0 hu
      (by linarith [(hgain c).2]) H σ (fun k => L k 0) (fun k => L k c.succ)
      hH hKH hHs hσ (fun k => hL k 0) hvalid (fun k => hcover k 0) (fun k => hcover k c.succ)
    refine ⟨e, he, ?_⟩
    filter_upwards [hf] with k hk
    obtain ⟨f, hco, hfi, -, hbad⟩ := hk
    exact ⟨f, hco, hfi, hbad⟩
  choose e he hf using hpair
  let c := min (e 0) (e 1)
  have hc : 0 < c := lt_min (he 0) (he 1)
  have hce (a : Fin 2) : c ≤ e a := by
    fin_cases a
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hframes : ∀ᶠ k in atTop, ∀ a : Fin 2,
      ∃ f : ProjectedComparisonFrame p k r (r + gain a) m (H k)
        (longTime (L k 0).β (L k a.succ).β) (longSlope (L k 0).β (L k a.succ).β)
        (longWidth (L k 0).β (L k a.succ).β) (σ k),
        f.coarse = L k 0 ∧ f.fine = L k a.succ ∧
        σ k (f.bad (4 * H k * p.N k ^ (-r) * p.N k ^ (10 / (1 - p.d) * u))) ≤
          ENNReal.ofReal (p.N k ^ (-e a)) := Filter.eventually_all.mpr hf
  have hC : 0 ≤ 10 / (1 - p.d) := by have := hp.dimension_lt_one; positivity
  have hwhole := p.eventually_projected_fiber_offsets hp hr hu hC hm hgap
    Hf hHf hKHf hHfs
  refine ⟨c, hc, ?_⟩
  filter_upwards [hframes, hwhole] with k hfk hwk
  choose f hco hfi hbad using hfk
  let threshold := 4 * H k * p.N k ^ (-r) * p.N k ^ (10 / (1 - p.d) * u)
  let E : Set (α × ℝ) := ⋃ a : Fin 2, (f a).bad threshold
  have hE : MeasurableSet E := MeasurableSet.iUnion fun a => (f a).bad_measurable threshold
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.scale k]
  have hbad' (a : Fin 2) : σ k ((f a).bad threshold) ≤ ENNReal.ofReal (p.N k ^ (-c)) :=
    (hbad a).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (hce a))))
  have hmass : σ k E ≤ ENNReal.ofReal (2 * p.N k ^ (-c)) := by
    calc
      _ ≤ ∑ a : Fin 2, σ k ((f a).bad threshold) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _a : Fin 2, ENNReal.ofReal (p.N k ^ (-c)) := Finset.sum_le_sum fun a _ => hbad' a
      _ = _ := by
        rw [Fin.sum_univ_two, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  refine ⟨E, hE, hmass, ?_⟩
  have hone (a : Fin 2) : ∀ᵐ ω ∂(σ k).restrict Eᶜ, ∀ R : ℝ, p.AtDepth k r R →
      ∀ (Q : Fin (p.n k r)) (i : Fin (L k 0).count) (j : Fin (L k a.succ).count),
      ω.1 ∈ p.B k r Q → ω.2 ∈ block (p.T k r) (p.j k r Q) →
      ω.1 ∈ (L k 0).C i → ω.1 ∈ (L k a.succ).C j →
      ∀ z ∈ p.trueFiberBox k r m (Hf k) Q ((L k 0).tag i),
        |eval ![z 0, z 2] ((L k a.succ).G j) - eval ![z 0, z 2] ((L k 0).G i) -
          p.canonicalOffset k r m (L k 0) (L k a.succ) Q i j| ≤ p.N k ^ (-r - u) := by
    have hvalid : (L k a.succ).Valid p k (r + gain a) m (H k) := by
      rw [← hdepth a]
      exact hL k a.succ
    have hvalid₀ : (L k 0).Valid p k r m (H k) := hL k 0
    have hb := long_fiber_bounds p hp hvalid₀ hvalid (zero_lt_one.trans_le (hH k))
      (hHH k) hu.le (by linarith [(hgain a).1]) (by linarith [(hgain a).2])
    have ho := hwk (r + gain a) _ _ _ (H k) (σ k) (f a) (hHH k) hb.1 hb.2.1 hb.2.2
    have hle : (σ k).restrict Eᶜ ≤ (f a).goodLaw threshold := by
      apply Measure.restrict_mono_set
      intro ω hω hbadω
      exact hω (mem_iUnion.mpr ⟨a, hbadω⟩)
    have ho' := ho.filter_mono (ae_mono hle)
    rw [hco a, hfi a] at ho'
    filter_upwards [ho'] with ω hω
    obtain ⟨i₀, j₀, -, hi₀, hj₀, -, hfit⟩ := hω
    intro R hat Q i j hQ hQt hi hj z hz
    have hii : i = i₀ := by
      by_contra hne
      exact Set.disjoint_left.mp ((hL k 0).2.2.2.2.1 i i₀ hne) hi hi₀
    have hjj : j = j₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hvalid.2.2.2.2.1 j j₀ hne) hj hj₀
    subst i j
    have ht₀ : (((p.j k r Q : ℕ) : ℝ) / (2 : ℝ) ^ p.T k r) ∈
        block (p.T k r) (p.j k r Q) := by
      constructor
      · exact le_rfl
      · apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
    exact hfit R hat Q hQ hQt _ ht₀ z hz
  have hall := ae_all_iff.mpr hone
  filter_upwards [hall] with ω hω
  intro R hat a Q i j hQ hQt hi hj z hz
  exact (hω a R hat Q i j hQ hQt hi hj z hz).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [(hgain a).2]))

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
