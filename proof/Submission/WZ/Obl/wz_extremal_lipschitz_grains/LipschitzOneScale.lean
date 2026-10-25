-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.LipschitzOneScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzTools

/-!
# Lipschitz plane map at one scale (sticky Lemma 4.5)

On each grid cube of side `s`, pick the coarse label pair carried by the most mass (every point has
at least `A² / (2 B²)` transverse coarse pairs by robust transversality and the fibre bound), then
the cell of side `r` of plane-map values carried by the most mass.  On the pair set the plane map is
within `R` of the normal of the two coarse directions (`cap_of_pair`), so few cells are needed.
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

theorem measurableSet_coarsePair {n k : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    (v : Fin n → Space) (β : ℝ) (a : Fin n → Fin k) (π : Fin k × Fin k) :
    MeasurableSet {p | π ∈ coarsePairs Y v β a p} := by
  classical
  have : {p | π ∈ coarsePairs Y v β a p} = ⋃ i ∈ (Finset.univ.filter fun ii : Fin n × Fin n =>
      (a ii.1, a ii.2) = π ∧ β < min ‖v ii.1 - v ii.2‖ ‖v ii.1 + v ii.2‖), Y i.1 ∩ Y i.2 := by
    ext p
    simp only [coarsePairs, transPairs, mem_ofPred_eq, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product, mem_through, mem_iUnion, Finset.mem_univ, true_and, exists_prop,
      mem_inter_iff]
    constructor
    · rintro ⟨ii, ⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨ii, ⟨h4, h3⟩, h1, h2⟩
    · rintro ⟨ii, ⟨h4, h3⟩, h1, h2⟩; exact ⟨ii, ⟨⟨h1, h2⟩, h3⟩, h4⟩
  rw [this]
  exact Finset.measurableSet_biUnion _ fun ii _ => (hY ii.1).inter (hY ii.2)

theorem measurableSet_iUnion_fin {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i)) :
    MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hY

/-- Variant of `measure_iUnion_select` with the constants kept apart. -/
theorem measure_iUnion_select' (ν : Measure Space) {s : ℝ} (hs : 0 < s) (E : Set Space)
    (hE : MeasurableSet E) (K : (Fin 3 → ℤ) → Set Space) (hKm : ∀ m, MeasurableSet (K m))
    (hKsub : ∀ m, K m ⊆ gridCube s m) (L D : ℝ≥0∞)
    (hK : ∀ m, L * ν (E ∩ gridCube s m) ≤ D * ν (K m)) :
    L * ν E ≤ D * ν (⋃ m, K m) := by
  have hdisjQ : Pairwise (Function.onFun Disjoint (gridCube s)) :=
    fun m m' h => gridCube_disjoint hs h
  have hdisjK : Pairwise (Function.onFun Disjoint K) :=
    fun m m' h => (hdisjQ h).mono (hKsub m) (hKsub m')
  have hE' : ν E = ∑' m, ν (E ∩ gridCube s m) := by
    rw [← measure_iUnion (fun m m' h => (hdisjQ h).mono inter_subset_right inter_subset_right)
      (fun m => hE.inter (measurableSet_gridCube s m)), ← inter_iUnion,
      iUnion_gridCube_eq_univ hs, inter_univ]
  rw [hE', measure_iUnion hdisjK hKm, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hK


/-- **Lipschitz plane map at one scale** (sticky Lemma 4.5).  Under robust transversality at
angle `β`, fibre bounds `B`, at most `Cact` active coarse labels per grid cube of side `s`, and a
fine plane map of precision `e₀` with coarse directions within `d₀`, there is a measurable part
`E'` of the shaded set carrying a fixed fraction of any measure `ν` on which the plane map varies
by less than `2 r` inside each grid cube. -/
theorem lipschitz_one_scale {n k : ℕ} (ν : Measure Space) {v : Fin n → Space}
    {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i)) (hv : ∀ i, ‖v i‖ = 1)
    {w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {a : Fin n → Fin k} {V : Space → Space}
    (hVm : Measurable V) (hVu : ∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1)
    {e₀ d₀ β s r A : ℝ} {B Cact : ℕ} (hs : 0 < s) (hr : 0 < r) (hβ : 2 * d₀ < β) (hA : 0 < A)
    (he₀ : 0 ≤ e₀) (hd₀ : 0 ≤ d₀)
    (hVp : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ e₀)
    (hdir : ∀ i, (Y i).Nonempty → min ‖w (a i) - v i‖ ‖w (a i) + v i‖ ≤ d₀)
    (hmult : ∀ p ∈ ⋃ i, Y i, A ≤ ((through Y p).card : ℝ))
    (hcone : ∀ p, ∀ i ∈ through Y p, (((through Y p).filter fun l =>
      min ‖v l - v i‖ ‖v l + v i‖ ≤ β).card : ℝ) ≤ (through Y p).card / 2)
    (hB : ∀ j p, ((through Y p).filter fun i => a i = j).card ≤ B) (hB1 : 1 ≤ B)
    (Act : (Fin 3 → ℤ) → Finset (Fin k))
    (hAct : ∀ m p, p ∈ gridCube s m → ∀ i ∈ through Y p, a i ∈ Act m)
    (hActc : ∀ m, (Act m).card ≤ Cact) :
    ∃ E' : Set Space, MeasurableSet E' ∧ E' ⊆ ⋃ i, Y i ∧
      ENNReal.ofReal (A ^ 2 / (2 * B ^ 2)) * ν (⋃ i, Y i) ≤
        ((Cact ^ 2 * (2 * (⌊2 * (4 * (e₀ + d₀) / ((β - 2 * d₀) / 2)) / r⌋₊ + 3) ^ 3) : ℕ) :
          ℝ≥0∞) * ν E' ∧
      ∀ p ∈ E', ∀ q ∈ E', cubeIndex s p = cubeIndex s q → dist (V p) (V q) < 2 * r := by
  classical
  set E := ⋃ i, Y i with hEdef
  have hE : MeasurableSet E := MeasurableSet.iUnion hY
  set R := 4 * (e₀ + d₀) / ((β - 2 * d₀) / 2) with hRdef
  have hR : 0 ≤ R := div_nonneg (by linarith) (by linarith)
  set Nc := (⌊2 * R / r⌋₊ + 3) ^ 3 with hNc
  set L : ℝ≥0∞ := ENNReal.ofReal (A ^ 2 / (2 * B ^ 2)) with hL
  set D : ℕ := Cact ^ 2 * (2 * Nc) with hD
  -- the per-cube construction
  have hper : ∀ m : Fin 3 → ℤ, ∃ K : Set Space, MeasurableSet K ∧ K ⊆ E ∩ gridCube s m ∧
      L * ν (E ∩ gridCube s m) ≤ (D : ℝ≥0∞) * ν K ∧
      ∃ c : Fin 3 → ℤ, K ⊆ V ⁻¹' gridCube r c := by
    intro m
    by_cases hQ : (E ∩ gridCube s m).Nonempty
    swap
    · refine ⟨∅, MeasurableSet.empty, empty_subset _, ?_, 0, empty_subset _⟩
      rw [Set.not_nonempty_iff_eq_empty.1 hQ, measure_empty, mul_zero]
      exact zero_le
    obtain ⟨p₀, hp₀E, hp₀Q⟩ := hQ
    obtain ⟨i₀, hi₀⟩ := mem_iUnion.1 hp₀E
    set P := Act m ×ˢ Act m with hP
    have hPne : P.Nonempty := by
      have := hAct m p₀ hp₀Q i₀ (mem_through.2 hi₀)
      exact ⟨(a i₀, a i₀), Finset.mem_product.2 ⟨this, this⟩⟩
    set S : Fin k × Fin k → Set Space := fun π => {p | π ∈ coarsePairs Y v β a p} with hS
    have hSm : ∀ π, MeasurableSet (S π) := fun π => measurableSet_coarsePair hY v β a π
    have hQm : MeasurableSet (E ∩ gridCube s m) := hE.inter (measurableSet_gridCube s m)
    -- many coarse pairs at every point of the cube
    have hLp : ∀ p ∈ E ∩ gridCube s m, L ≤ ∑ π ∈ P, (S π).indicator 1 p := by
      intro p hp
      have hsub : coarsePairs Y v β a p ⊆ P := by
        intro π hπ
        simp only [coarsePairs, Finset.mem_image, transPairs, Finset.mem_filter,
          Finset.mem_product] at hπ
        obtain ⟨ii, ⟨⟨h1, h2⟩, _⟩, rfl⟩ := hπ
        exact Finset.mem_product.2 ⟨hAct m p hp.2 _ h1, hAct m p hp.2 _ h2⟩
      have hsum : ∑ π ∈ P, (S π).indicator (1 : Space → ℝ≥0∞) p =
          ((coarsePairs Y v β a p).card : ℝ≥0∞) := by
        rw [← Finset.sum_subset hsub]
        · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          refine Finset.sum_congr rfl fun π hπ => ?_
          rw [indicator_of_mem (show p ∈ S π from hπ)]; simp
        · intro π _ hπ
          exact indicator_of_notMem (show p ∉ S π from hπ) _
      rw [hsum]
      have hc1 := card_transPairs_ge Y v β p (hcone p)
      have hc2 := card_transPairs_le Y v β a p B (hB · p)
      have hm := hmult p hp.1
      have hreal : A ^ 2 / (2 * B ^ 2) ≤ ((coarsePairs Y v β a p).card : ℝ) := by
        have hB0 : (0 : ℝ) < B := by exact_mod_cast hB1
        have h3 : ((through Y p).card : ℝ) ^ 2 / 2 ≤ (B : ℝ) * B * (coarsePairs Y v β a p).card := by
          have : ((transPairs Y v β p).card : ℝ) ≤ (B : ℝ) * B * (coarsePairs Y v β a p).card := by
            exact_mod_cast hc2
          linarith
        have h4 : A ^ 2 ≤ ((through Y p).card : ℝ) ^ 2 := pow_le_pow_left₀ hA.le hm 2
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      rw [hL]
      calc ENNReal.ofReal (A ^ 2 / (2 * B ^ 2)) ≤ ENNReal.ofReal ((coarsePairs Y v β a p).card) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = _ := ENNReal.ofReal_natCast _
    obtain ⟨π, hπP, hπ⟩ := exists_heavy_member ν (E ∩ gridCube s m) P hPne S hSm L hLp hQm
    set F := E ∩ gridCube s m ∩ S π with hF
    have hFm : MeasurableSet F := hQm.inter (hSm π)
    set Nv := ‖cross (w π.1) (w π.2)‖⁻¹ • cross (w π.1) (w π.2) with hNv
    -- the plane map is in one of two caps on `F`
    have hcap : ∀ p ∈ F, dist (V p) Nv ≤ R ∨ dist (V p) (-Nv) ≤ R := by
      intro p hp
      have hp3 : π ∈ coarsePairs Y v β a p := hp.2
      simp only [coarsePairs, Finset.mem_image, transPairs, Finset.mem_filter,
        Finset.mem_product, mem_through] at hp3
      obtain ⟨⟨i, i'⟩, ⟨⟨h1, h2⟩, h3⟩, hii⟩ := hp3
      have hVp1 : ‖V p‖ = 1 := hVu p (mem_iUnion.2 ⟨i, h1⟩)
      have := cap_of_pair hVp1 (hv i) (hv i') (hw (a i)) (hw (a i')) hβ (hVp i p h1)
        (hVp i' p h2) (hdir i ⟨p, h1⟩) (hdir i' ⟨p, h2⟩) h3
      rw [← hii] at hNv
      simp only at hNv
      rw [dist_eq_norm, dist_eq_norm, sub_neg_eq_add, hNv]
      rcases le_total ‖V p - ‖cross (w (a i)) (w (a i'))‖⁻¹ • cross (w (a i)) (w (a i'))‖
        ‖V p + ‖cross (w (a i)) (w (a i'))‖⁻¹ • cross (w (a i)) (w (a i'))‖ with h | h
      · left; rw [min_eq_left h] at this; exact this
      · right; rw [min_eq_right h] at this; exact this
    obtain ⟨S₁, hS₁c, hS₁⟩ := exists_cells_cover Nv hR hr
    obtain ⟨S₂, hS₂c, hS₂⟩ := exists_cells_cover (-Nv) hR hr
    have hcov : ∀ p ∈ F, cubeIndex r (V p) ∈ S₁ ∪ S₂ := by
      intro p hp
      rcases hcap p hp with h | h
      · exact Finset.mem_union_left _ (hS₁ _ h)
      · exact Finset.mem_union_right _ (hS₂ _ h)
    have hSne : (S₁ ∪ S₂).Nonempty := ⟨_, Finset.mem_union_left _ (hS₁ Nv (by simp [hR]))⟩
    obtain ⟨cc, _, hcc⟩ := exists_heavy_cell ν V hVm hFm hr (S₁ ∪ S₂) hcov hSne
    refine ⟨F ∩ V ⁻¹' gridCube r cc, hFm.inter (hVm (measurableSet_gridCube r cc)),
      fun p hp => hp.1.1, ?_, cc, fun p hp => hp.2⟩
    have hPc : P.card ≤ Cact ^ 2 := by
      rw [hP, Finset.card_product, sq]; exact Nat.mul_le_mul (hActc m) (hActc m)
    have hSc : (S₁ ∪ S₂).card ≤ 2 * Nc := by
      calc (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
        _ ≤ Nc + Nc := Nat.add_le_add hS₁c hS₂c
        _ = 2 * Nc := by ring
    calc L * ν (E ∩ gridCube s m) ≤ P.card * ν (E ∩ gridCube s m ∩ S π) := hπ
      _ ≤ P.card * ((S₁ ∪ S₂).card * ν (F ∩ V ⁻¹' gridCube r cc)) := by
          gcongr
      _ ≤ (D : ℝ≥0∞) * ν (F ∩ V ⁻¹' gridCube r cc) := by
          rw [← mul_assoc]
          gcongr
          rw [hD]
          push_cast
          gcongr
          · exact_mod_cast hPc
          · exact_mod_cast hSc
  choose K hKm hKsub hKmass c hKc using hper
  refine ⟨⋃ m, K m, MeasurableSet.iUnion hKm, iUnion_subset fun m => (hKsub m).trans
    inter_subset_left, ?_, ?_⟩
  · have := measure_iUnion_select' ν hs E hE K hKm (fun m => (hKsub m).trans inter_subset_right)
      L D hKmass
    simpa [hD, hNc] using this
  · intro p hp q hq hpq
    obtain ⟨m, hpm⟩ := mem_iUnion.1 hp
    obtain ⟨m', hqm⟩ := mem_iUnion.1 hq
    have hm1 : cubeIndex s p = m := cubeIndex_eq_of_mem hs ((hKsub m hpm).2)
    have hm2 : cubeIndex s q = m' := cubeIndex_eq_of_mem hs ((hKsub m' hqm).2)
    have hmm : m = m' := hm1.symm.trans (hpq.trans hm2)
    subst hmm
    have h1 := hKc m hpm
    have h2 := hKc m hqm
    exact dist_lt_of_cubeIndex_eq hr ((cubeIndex_eq_of_mem hr h1).trans
      (cubeIndex_eq_of_mem hr h2).symm)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
