import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawDecomp

/-!
# Cell ceilings of the marked law

`MarkedLaw_cell_le`: the marked law puts mass at most `(1/σ) κ W |A|` on the incidences whose
exact base point `(t, y)` lies in `A`, whose hidden trace lies in the `ρ`-bin `i` and whose
noisy slope lies in `Ksl`, when the noisy slope of every tag falls into `Ksl` with probability
at most `κ`, and the weights of the tags whose window contains a base point sum to at most
`W`.

The organisation (slice in time, slice the noise, then sum the tag weights pointwise) follows
`markLaw_ceiling` of x0215's `Submission/Lib/K4ScalarMeshSmoothing.lean` (o062, branch x0215),
adapted to the product noise and to the marked time cells used here.
-/

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw

open MeasureTheory Set
open scoped ENNReal

/-- The window of tag `j` for the hidden `ρ`-bin `i` and the noisy slope set `Ksl`: the base
points `(t, y)` that tag `j` can reach with a hidden trace in bin `i` and a noisy slope in
`Ksl`. -/
def tagWindow (σ ρ : ℝ) {H J : ℕ} (b₀ : Fin H → Coeff) (mark : Fin H → Fin J → Bool)
    (j : Fin H) (i : ℤ) (Ksl : Set ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ∈ markTimes mark j ∧ (i : ℝ) * ρ ≤ curveX b₀ j q.1 + 3 * σ ∧
    curveX b₀ j q.1 < ((i : ℝ) + 1) * ρ ∧ curveY b₀ j q.1 ≤ q.2 ∧
    q.2 ≤ curveY b₀ j q.1 + 2 * σ ∧ ∃ v ∈ Icc 0 σ, b₀ j 1 + v ∈ Ksl}

theorem measurable_curveX_tag {H : ℕ} (b₀ : Fin H → Coeff) (j : Fin H) :
    Measurable (fun t : ℝ => curveX b₀ j t) := by
  unfold curveX; fun_prop

theorem measurable_curveY_tag {H : ℕ} (b₀ : Fin H → Coeff) (j : Fin H) :
    Measurable (fun t : ℝ => curveY b₀ j t) := by
  unfold curveY; fun_prop

theorem measurableSet_tagWindow (σ ρ : ℝ) {H J : ℕ} (b₀ : Fin H → Coeff)
    (mark : Fin H → Fin J → Bool) (j : Fin H) (i : ℤ) (Ksl : Set ℝ) :
    MeasurableSet (tagWindow σ ρ b₀ mark j i Ksl) := by
  have hX := (measurable_curveX_tag b₀ j).comp (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ))
  have hY := (measurable_curveY_tag b₀ j).comp (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ))
  refine ((measurableSet_markTimes mark j).preimage measurable_fst).inter
    ((measurableSet_le measurable_const (hX.add measurable_const)).inter
    ((measurableSet_lt hX measurable_const).inter
    ((measurableSet_le hY measurable_snd).inter
    ((measurableSet_le measurable_snd (hY.add measurable_const)).inter
    (MeasurableSet.const _)))))

/-- The noisy traces of tag `j`. -/
theorem curveY_noisy {H : ℕ} (b₀ : Fin H → Coeff) (j : Fin H) (u : Coeff) (t : ℝ) :
    curveY Prod.snd (((j : ℕ), b₀ j + u) : Traj) t = u 0 + (b₀ j 0 + t * (b₀ j 1 + u 1)) := by
  simp only [curveY, Pi.add_apply]; ring

theorem curveX_noisy {H : ℕ} (b₀ : Fin H → Coeff) (j : Fin H) (u : Coeff) (t : ℝ) :
    curveX Prod.snd (((j : ℕ), b₀ j + u) : Traj) t =
      curveX b₀ j t + (u 2 + t * u 3 + t ^ 2 * u 4) := by
  simp only [curveX, Pi.add_apply]; ring

/-- One tag at one time: the noise slice. -/
theorem tag_slice_le {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) {H J : ℕ} (b₀ : Fin H → Coeff)
    (mark : Fin H → Fin J → Bool) (j : Fin H) (i : ℤ) {Ksl : Set ℝ} (hK : MeasurableSet Ksl)
    {κ : ℝ≥0∞} (hκ : noise1 σ {v | b₀ j 1 + v ∈ Ksl} ≤ κ)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (t : ℝ) :
    (markTimes mark j).indicator (fun t => Noise σ {u | ((((j : ℕ), b₀ j + u), t) : Traj × ℝ) ∈
        {p : Traj × ℝ | (p.2, curveY Prod.snd p.1 p.2) ∈ A ∧
          ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl}}) t ≤
      ENNReal.ofReal (σ⁻¹) * κ * volume (Prod.mk t ⁻¹' (A ∩ tagWindow σ ρ b₀ mark j i Ksl)) := by
  by_cases ht : t ∈ markTimes mark j
  swap
  · rw [indicator_of_notMem ht]; exact zero_le
  rw [indicator_of_mem ht]
  have ht01 := markTimes_subset mark j ht
  have ht0 : 0 ≤ t := ht01.1
  have ht1 : t ≤ 1 := ht01.2.le
  have hbox := Noise_ae_mem hσ
  -- the noisy traces on the box
  have htr : ∀ u : Coeff, (∀ e, u e ∈ Icc 0 σ) →
      curveY b₀ j t ≤ curveY Prod.snd (((j : ℕ), b₀ j + u) : Traj) t ∧
      curveY Prod.snd (((j : ℕ), b₀ j + u) : Traj) t ≤ curveY b₀ j t + 2 * σ ∧
      curveX b₀ j t ≤ curveX Prod.snd (((j : ℕ), b₀ j + u) : Traj) t ∧
      curveX Prod.snd (((j : ℕ), b₀ j + u) : Traj) t ≤ curveX b₀ j t + 3 * σ := by
    intro u hu
    have h0 := hu 0; have h1 := hu 1; have h2 := hu 2; have h3 := hu 3; have h4 := hu 4
    simp only [mem_Icc] at h0 h1 h2 h3 h4
    rw [curveY_noisy, curveX_noisy]
    simp only [curveY]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have ht2' : 0 ≤ t ^ 2 := by positivity
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  by_cases hc : (i : ℝ) * ρ ≤ curveX b₀ j t + 3 * σ ∧ curveX b₀ j t < ((i : ℝ) + 1) * ρ ∧
      ∃ v ∈ Icc 0 σ, b₀ j 1 + v ∈ Ksl
  · -- the slice estimate
    set Y' : (Fin 4 → ℝ) → ℝ := fun u' => b₀ j 0 + t * (b₀ j 1 + u' 0) with hY'
    set A' : Set ℝ := {y | (t, y) ∈ A ∧ curveY b₀ j t ≤ y ∧ y ≤ curveY b₀ j t + 2 * σ}
      with hA'
    set Q : Set (Fin 4 → ℝ) := {u' | ⌊(curveX b₀ j t + (u' 1 + t * u' 2 + t ^ 2 * u' 3)) / ρ⌋ = i ∧
      b₀ j 1 + u' 0 ∈ Ksl} with hQ
    have hY'm : Measurable Y' := by rw [hY']; fun_prop
    have hA'm : MeasurableSet A' :=
      (measurable_prodMk_left hA).inter
        ((measurableSet_le measurable_const measurable_id).inter
          (measurableSet_le measurable_id measurable_const))
    have hQm : MeasurableSet Q := by
      refine MeasurableSet.inter ?_ ?_
      · exact (measurableSet_singleton i).preimage (Int.measurable_floor.comp (by fun_prop))
      · exact hK.preimage (by fun_prop)
    have hsub : {u : Coeff | ((((j : ℕ), b₀ j + u), t) : Traj × ℝ) ∈
        {p : Traj × ℝ | (p.2, curveY Prod.snd p.1 p.2) ∈ A ∧
          ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl}} ≤ᵐ[Noise σ]
        {u : Coeff | u 0 + Y' (Fin.tail u) ∈ A' ∧ Fin.tail u ∈ Q} := by
      filter_upwards [hbox] with u hu hmem
      obtain ⟨h1, h2, h3⟩ := hmem
      obtain ⟨hy1, hy2, -, -⟩ := htr u hu
      have hYeq : u 0 + Y' (Fin.tail u) = curveY Prod.snd (((j : ℕ), b₀ j + u) : Traj) t := by
        rw [curveY_noisy]; rfl
      have hXeq : curveX b₀ j t + (Fin.tail u 1 + t * Fin.tail u 2 + t ^ 2 * Fin.tail u 3) =
          curveX Prod.snd (((j : ℕ), b₀ j + u) : Traj) t := by
        rw [curveX_noisy]; rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hYeq]; exact ⟨h1, hy1, hy2⟩
      · show ⌊(curveX b₀ j t + (Fin.tail u 1 + t * Fin.tail u 2 + t ^ 2 * Fin.tail u 3)) / ρ⌋ = i
        rw [hXeq]; exact h2
      · exact h3
    calc Noise σ {u : Coeff | ((((j : ℕ), b₀ j + u), t) : Traj × ℝ) ∈
          {p : Traj × ℝ | (p.2, curveY Prod.snd p.1 p.2) ∈ A ∧
            ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl}}
        ≤ Noise σ {u : Coeff | u 0 + Y' (Fin.tail u) ∈ A' ∧ Fin.tail u ∈ Q} :=
          measure_mono_ae hsub
      _ ≤ ENNReal.ofReal (σ⁻¹) * noise4 σ Q * volume A' := Noise_slice_le hσ hY'm hA'm hQm
      _ ≤ ENNReal.ofReal (σ⁻¹) * κ *
            volume (Prod.mk t ⁻¹' (A ∩ tagWindow σ ρ b₀ mark j i Ksl)) := by
          gcongr
          · calc noise4 σ Q ≤ noise4 σ {u' | b₀ j 1 + u' 0 ∈ Ksl} :=
                  measure_mono fun u' hu' => hu'.2
              _ = noise1 σ {v | b₀ j 1 + v ∈ Ksl} := noise4_slope σ hσ _ hK
              _ ≤ κ := hκ
          · intro y hy
            obtain ⟨hyA, hy1, hy2⟩ := hy
            exact ⟨hyA, ht, hc.1, hc.2.1, hy1, hy2, hc.2.2⟩
  · -- the slice is null
    have hnull : Noise σ {u : Coeff | ((((j : ℕ), b₀ j + u), t) : Traj × ℝ) ∈
        {p : Traj × ℝ | (p.2, curveY Prod.snd p.1 p.2) ∈ A ∧
          ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl}} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hbox] with u hu hmem
      obtain ⟨-, h2, h3⟩ := hmem
      obtain ⟨-, -, hx1, hx2⟩ := htr u hu
      apply hc
      have hf1 := Int.floor_le (curveX Prod.snd (((j : ℕ), b₀ j + u) : Traj) t / ρ)
      have hf2 := Int.lt_floor_add_one (curveX Prod.snd (((j : ℕ), b₀ j + u) : Traj) t / ρ)
      rw [h2, le_div_iff₀ hρ] at hf1
      rw [h2, div_lt_iff₀ hρ] at hf2
      refine ⟨by linarith, by linarith, u 1, hu 1, ?_⟩
      simpa using h3
    rw [hnull]
    exact zero_le

/-- **Cell ceiling of the marked law.** -/
theorem MarkedLaw_cell_le {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) {H J : ℕ} (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) (i : ℤ) {Ksl : Set ℝ}
    (hK : MeasurableSet Ksl) {κ W : ℝ≥0∞} (hκ : ∀ j, noise1 σ {v | b₀ j 1 + v ∈ Ksl} ≤ κ)
    (hW : ∀ q : ℝ × ℝ,
      ∑ j, (tagWindow σ ρ b₀ mark j i Ksl).indicator (fun _ => ENNReal.ofReal (w j)) q ≤ W)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    MarkedLaw σ H J b₀ w mark {p : Traj × ℝ | (p.2, curveY Prod.snd p.1 p.2) ∈ A ∧
        ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl} ≤
      ENNReal.ofReal (σ⁻¹) * κ * W * volume A := by
  have hYm : Measurable (fun p : Traj × ℝ => curveY Prod.snd p.1 p.2) := by
    unfold curveY; fun_prop
  have hXm : Measurable (fun p : Traj × ℝ => curveX Prod.snd p.1 p.2) := by
    unfold curveX; fun_prop
  have hP : MeasurableSet {p : Traj × ℝ | (p.2, curveY Prod.snd p.1 p.2) ∈ A ∧
      ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl} := by
    refine (hA.preimage (measurable_snd.prodMk hYm)).inter
      (((measurableSet_singleton i).preimage
        (Int.measurable_floor.comp (hXm.div_const ρ))).inter (hK.preimage (by fun_prop)))
  rw [MarkedLaw_apply hσ b₀ w mark hP]
  have hTm : ∀ j, MeasurableSet (tagWindow σ ρ b₀ mark j i Ksl) := fun j =>
    measurableSet_tagWindow σ ρ b₀ mark j i Ksl
  calc ∑ j, ENNReal.ofReal (w j) * ∫⁻ t, (markTimes mark j).indicator
        (fun t => Noise σ {u | ((((j : ℕ), b₀ j + u), t) : Traj × ℝ) ∈
          {p : Traj × ℝ | (p.2, curveY Prod.snd p.1 p.2) ∈ A ∧
            ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl}}) t
      ≤ ∑ j, ENNReal.ofReal (w j) * ∫⁻ t, ENNReal.ofReal (σ⁻¹) * κ *
          volume (Prod.mk t ⁻¹' (A ∩ tagWindow σ ρ b₀ mark j i Ksl)) := by
        gcongr with j
        exact tag_slice_le hσ hρ b₀ mark j i hK (hκ j) hA _
    _ = ∑ j, ENNReal.ofReal (w j) * (ENNReal.ofReal (σ⁻¹) * κ *
          volume (A ∩ tagWindow σ ρ b₀ mark j i Ksl)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul _ (measurable_measure_prodMk_left (hA.inter (hTm j))),
          Measure.volume_eq_prod, Measure.prod_apply (hA.inter (hTm j))]
    _ = ENNReal.ofReal (σ⁻¹) * κ * ∫⁻ q in A,
          ∑ j, (tagWindow σ ρ b₀ mark j i Ksl).indicator (fun _ => ENNReal.ofReal (w j)) q := by
        rw [lintegral_finsetSum _ (fun j _ => measurable_const.indicator (hTm j)), Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_indicator_const (hTm j), Measure.restrict_apply (hTm j), inter_comm]
        ring
    _ ≤ ENNReal.ofReal (σ⁻¹) * κ * ∫⁻ _ in A, W := by
        gcongr with q
        exact hW q
    _ = ENNReal.ofReal (σ⁻¹) * κ * W * volume A := by
        rw [setLIntegral_const]; ring

/-! ### From cell ceilings to densities -/

/-- A measure on `X × ℤ` bounded on every product cell `A ×ˢ {i}` by `C ν A` is bounded by
`C • (ν ⊗ count)`. -/
theorem le_smul_prod_count {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {lam : Measure (X × ℤ)} {C : ℝ≥0∞}
    (h : ∀ (i : ℤ) (A : Set X), MeasurableSet A → lam (A ×ˢ {i}) ≤ C * ν A) :
    lam ≤ C • ν.prod Measure.count := by
  refine Measure.le_iff.mpr fun B hB => ?_
  have hBi : ∀ i : ℤ, MeasurableSet ((fun x => (x, i)) ⁻¹' B) := fun i =>
    measurable_prodMk_right hB
  have hunion : B = ⋃ i : ℤ, ((fun x => (x, i)) ⁻¹' B) ×ˢ {i} := by
    ext ⟨x, i⟩
    simp only [mem_iUnion, mem_prod, mem_preimage, mem_singleton_iff]
    constructor
    · intro hx; exact ⟨i, hx, rfl⟩
    · rintro ⟨i', hx, rfl⟩; exact hx
  have hdisj : Pairwise (Function.onFun Disjoint
      fun i : ℤ => ((fun x => (x, i)) ⁻¹' B) ×ˢ ({i} : Set ℤ)) := by
    intro i i' hii'
    refine Set.disjoint_left.mpr ?_
    rintro ⟨x, k⟩ h1 h2
    exact hii' ((mem_singleton_iff.mp h1.2).symm.trans (mem_singleton_iff.mp h2.2))
  rw [Measure.smul_apply, smul_eq_mul, Measure.prod_apply_symm hB, lintegral_count]
  conv_lhs => rw [hunion]
  rw [measure_iUnion hdisj (fun i => (hBi i).prod (measurableSet_singleton i)),
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun i => h i _ (hBi i)

/-- The Radon-Nikodym derivative of a measure dominated by `C • ν` is at most `C`. -/
theorem rnDeriv_le_of_le_smul {X : Type*} [MeasurableSpace X] {ν : Measure X} [SigmaFinite ν]
    {lam : Measure X} {C : ℝ≥0∞} (h : lam ≤ C • ν) : ∀ᵐ x ∂ν, lam.rnDeriv ν x ≤ C := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
    fun s hs _ => ?_
  calc ∫⁻ x in s, lam.rnDeriv ν x ∂ν ≤ lam s := Measure.setLIntegral_rnDeriv_le s
    _ ≤ (C • ν) s := h s
    _ = ∫⁻ _ in s, C ∂ν := by rw [Measure.smul_apply, smul_eq_mul, setLIntegral_const]

/-- A measure dominated by `C • ν` has a density bounded by `C`. -/
theorem exists_density_le {X : Type*} [MeasurableSpace X] {ν : Measure X} [SigmaFinite ν]
    {lam : Measure X} {C : ℝ≥0∞} (hC : C ≠ ⊤) (h : lam ≤ C • ν) :
    Measurable (lam.rnDeriv ν) ∧ lam = ν.withDensity (lam.rnDeriv ν) ∧
      ∀ᵐ x ∂ν, lam.rnDeriv ν x ≤ C := by
  have hac : lam ≪ ν := Measure.absolutelyContinuous_of_le_smul h
  have : SigmaFinite (C • ν) := by
    have h1 : (C.toNNReal • ν : Measure X) = C • ν := by
      ext s _
      simp [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_toNNReal hC]
    rw [← h1]
    infer_instance
  have : SigmaFinite lam := Measure.sigmaFinite_of_le (C • ν) h
  refine ⟨Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq lam ν hac).symm, ?_⟩
  exact rnDeriv_le_of_le_smul h

end Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw
