-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreWitness.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreVelocity
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreGoodLines
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreLists

/-!
# States with witnesses in two separated narrow velocity bins

Inside the qualified packet set `S₀`, drop the null code classes and the bad
lines (no mass), fix two separated narrow velocity bins `b₁, b₂` charged by
states of mass `≥ ρ S₀ / (4 Λ²)`, and choose in every such state one witness
incidence in each bin.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set
open scoped ENNReal

/-- The narrow velocity bin of an incidence. -/
noncomputable def velBin (δ : ℝ) (p : Incidence) : ℤ := ⌊p.1.2 1 / δ⌋

theorem measurable_velBin (δ : ℝ) : Measurable (velBin δ) := by
  have h : Measurable fun p : Incidence => p.1.2 1 :=
    (measurable_pi_apply (1 : Fin 5)).comp (measurable_snd.comp measurable_fst)
  exact Int.measurable_floor.comp (h.div_const δ)

/-- The close narrow bins lie in five consecutive separation bins. -/
theorem velBin_geom {δv δs : ℝ} (hδv : 0 < δv) (hδs : 0 < δs) (hvs : 2 * δv ≤ δs) (b₁ : ℤ) :
    ∃ s₀ : ℤ, ∀ p : Incidence, |velBin δv p - b₁| < ⌈δs / δv⌉ + 1 →
      s₀ ≤ velBin δs p ∧ velBin δs p ≤ s₀ + 4 := by
  set m₀ : ℤ := ⌈δs / δv⌉ + 1 with hm₀
  refine ⟨⌊((b₁ - m₀ + 1 : ℤ) : ℝ) * δv / δs⌋, ?_⟩
  intro p hp
  have hlt := abs_lt.mp hp
  set V := p.1.2 1 with hV
  have hk1 : ((velBin δv p : ℤ) : ℝ) ≤ V / δv := Int.floor_le _
  have hk2 : V / δv < (velBin δv p : ℝ) + 1 := Int.lt_floor_add_one _
  have hlo : ((b₁ - m₀ + 1 : ℤ) : ℝ) * δv ≤ V := by
    have : ((b₁ - m₀ + 1 : ℤ) : ℝ) ≤ (velBin δv p : ℝ) := by exact_mod_cast (by omega)
    have h3 := (le_div_iff₀ hδv).mp (this.trans hk1)
    linarith
  have hhi : V < ((b₁ + m₀ : ℤ) : ℝ) * δv := by
    have : (velBin δv p : ℝ) + 1 ≤ ((b₁ + m₀ : ℤ) : ℝ) := by exact_mod_cast (by omega)
    have h3 := (div_lt_iff₀ hδv).mp (hk2.trans_le this)
    linarith
  constructor
  · apply Int.floor_mono
    exact div_le_div_of_nonneg_right hlo hδs.le
  · -- the window has width at most `3.5 δs`
    have hceil : ((⌈δs / δv⌉ : ℤ) : ℝ) < δs / δv + 1 := Int.ceil_lt_add_one _
    have hwidth : ((b₁ + m₀ : ℤ) : ℝ) * δv - ((b₁ - m₀ + 1 : ℤ) : ℝ) * δv ≤ 4 * δs := by
      have heq : ((b₁ + m₀ : ℤ) : ℝ) * δv - ((b₁ - m₀ + 1 : ℤ) : ℝ) * δv =
          (2 * (⌈δs / δv⌉ : ℝ) + 1) * δv := by
        rw [hm₀]; push_cast; ring
      rw [heq]
      have h1 : (2 * (⌈δs / δv⌉ : ℝ) + 1) * δv ≤ (2 * (δs / δv + 1) + 1) * δv :=
        mul_le_mul_of_nonneg_right (by linarith) hδv.le
      have h2 : (2 * (δs / δv + 1) + 1) * δv = 2 * δs + 3 * δv := by field_simp; ring
      linarith
    have hfl : velBin δs p ≤ ⌊((b₁ - m₀ + 1 : ℤ) : ℝ) * δv / δs + 4⌋ := by
      apply Int.floor_mono
      rw [div_add' _ _ _ hδs.ne', div_le_div_iff_of_pos_right hδs]
      linarith
    rw [Int.floor_add_ofNat] at hfl
    · exact_mod_cast hfl


/-- Witnesses in two separated narrow velocity bins for many states. -/
theorem exists_core_witnesses (ρ : Measure Incidence) [IsFiniteMeasure ρ]
    (θ : Measure Trajectory) [IsFiniteMeasure θ] (π : Measure ℝ) [IsProbabilityMeasure π]
    (E S₀ : Set Incidence) (hE : MeasurableSet E) (hS₀ : MeasurableSet S₀) (hS₀E : S₀ ⊆ E)
    (N B rT δv δs Λ : ℝ) (hΛ : 1 ≤ Λ) (hδv : 0 < δv) (hδs : 0 < δs) (hvs : 2 * δv ≤ δs)
    (hθρ : (θ.prod volume).restrict E ≤ ENNReal.ofReal Λ • ρ.restrict E)
    (hρθ : ρ.restrict E ≤ ENNReal.ofReal Λ • (θ.prod volume).restrict E)
    (hbreadth : ∀ (q : Fin 3 → ℤ) (c : ℤ),
      16 * ρ.restrict S₀ {p | physCube N B p = q ∧ ⌊p.1.2 1 / δs⌋ = c} ≤
        ρ.restrict S₀ {p | physCube N B p = q})
    (hpal : ∀ (q : Fin 3 → ℤ) (c : ℤ),
      ρ.restrict S₀ {p | physCube N B p = q ∧ ⌊p.1.2 1 / δv⌋ = c} ≤
        ENNReal.ofReal Λ * ρ.restrict S₀ {p | physCube N B p = q} * π {w | ⌊w / δv⌋ = c})
    (hpos : ρ S₀ ≠ 0) :
    ∃ (b : Fin 2 → ℤ) (A₁ : Set Incidence) (wit : Fin 2 → (Fin 3 → ℤ) → Incidence),
      ⌈δs / δv⌉ + 1 ≤ |b 0 - b 1| ∧
      MeasurableSet A₁ ∧ A₁ ⊆ S₀ ∧
      ENNReal.ofReal (1 / (4 * Λ ^ 2)) * ρ S₀ ≤ ρ A₁ ∧
      (∀ ω ∈ A₁, ω ∉ nullCodeSet ρ E (coreCode N B rT)) ∧
      (∀ ω ∈ A₁, ∀ i, wit i (physCube N B ω) ∈ S₀ ∧
        physCube N B (wit i (physCube N B ω)) = physCube N B ω ∧
        velBin δv (wit i (physCube N B ω)) = b i ∧
        (wit i (physCube N B ω)).1 ∉ badLines ρ E (coreCode N B rT)) := by
  classical
  set code := coreCode N B rT with hcode_def
  have hcode : Measurable code := measurable_coreCode N B rT
  set Z := nullCodeSet ρ E code with hZ
  have hZm : MeasurableSet Z := measurableSet_nullCodeSet ρ E code hcode
  set Bd : Set Incidence := badLines ρ E code ×ˢ univ with hBd
  have hBdm : MeasurableSet Bd :=
    (measurableSet_badLines ρ E hE code hcode).prod MeasurableSet.univ
  have hZnull : ρ (S₀ ∩ Z) = 0 := by
    have h := nullCodeSet_null ρ E code
    rw [Measure.restrict_apply hZm] at h
    exact measure_mono_null (fun x (hx : x ∈ S₀ ∩ Z) => (⟨hx.2, hS₀E hx.1⟩ : x ∈ Z ∩ E)) h
  have hBdnull : ρ (S₀ ∩ Bd) = 0 := by
    have h := badLines_null ρ θ E hE code hcode Λ hθρ hρθ
    rw [Measure.restrict_apply hBdm] at h
    exact measure_mono_null (fun x (hx : x ∈ S₀ ∩ Bd) => (⟨hx.2, hS₀E hx.1⟩ : x ∈ Bd ∩ E)) h
  set S₀' := S₀ \ (Z ∪ Bd) with hS₀'
  have hS₀'m : MeasurableSet S₀' := hS₀.diff (hZm.union hBdm)
  have hae : S₀' =ᵐ[ρ] S₀ := by
    apply diff_ae_eq_self.mpr
    rw [Set.inter_union_distrib_left]
    exact measure_union_null hZnull hBdnull
  have hres : ρ.restrict S₀' = ρ.restrict S₀ := Measure.restrict_congr_set hae
  set μ := ρ.restrict S₀' with hμ
  have hμuniv : μ univ = ρ S₀ := by
    rw [hμ, Measure.restrict_apply_univ]
    exact measure_congr hae
  -- the palette as a function of the narrow bin
  set π' : ℤ → ℝ≥0∞ := fun c => π {w | ⌊w / δv⌋ = c} with hπ'
  have hπsum : ∑' c, π' c ≤ 1 := by
    have hf : Measurable fun w : ℝ => ⌊w / δv⌋ := Int.measurable_floor.comp (measurable_id.div_const δv)
    have h := tsum_measure_inter_label (Ω := ℝ) π (fun w : ℝ => ⌊w / δv⌋) hf univ MeasurableSet.univ
    simp only [univ_inter] at h
    rw [hπ']
    simp only
    rw [h, measure_univ]
  obtain ⟨b₁, b₂, hsep, hmass⟩ := exists_separated_bin_pair μ (physCube N B)
    (measurable_physCube N B) (velBin δv) (velBin δs) (measurable_velBin δv)
    (measurable_velBin δs) (⌈δs / δv⌉ + 1) (velBin_geom hδv hδs hvs)
    (fun q c => by rw [hres]; exact hbreadth q c) π' hπsum Λ hΛ
    (fun q b => by rw [hres]; exact hpal q b) (by rw [hμuniv]; exact hpos)
  set good : Set Incidence := {ω | μ {ω' | physCube N B ω' = physCube N B ω ∧
      velBin δv ω' = b₁} ≠ 0 ∧ μ {ω' | physCube N B ω' = physCube N B ω ∧
      velBin δv ω' = b₂} ≠ 0} with hgood
  have hgoodm : MeasurableSet good := by
    have : good = physCube N B ⁻¹' {q | μ {ω' | physCube N B ω' = q ∧ velBin δv ω' = b₁} ≠ 0 ∧
        μ {ω' | physCube N B ω' = q ∧ velBin δv ω' = b₂} ≠ 0} := rfl
    rw [this]
    exact measurable_physCube N B (Set.to_countable _).measurableSet
  set b : Fin 2 → ℤ := ![b₁, b₂] with hb
  -- witnesses
  set wit : Fin 2 → (Fin 3 → ℤ) → Incidence := fun i q =>
    if h : (S₀' ∩ {ω | physCube N B ω = q ∧ velBin δv ω = b i}).Nonempty then h.some
    else default with hwit
  have hwitspec : ∀ (i : Fin 2) (q : Fin 3 → ℤ),
      μ {ω' | physCube N B ω' = q ∧ velBin δv ω' = b i} ≠ 0 →
      wit i q ∈ S₀' ∧ physCube N B (wit i q) = q ∧ velBin δv (wit i q) = b i := by
    intro i q hq
    have hne : (S₀' ∩ {ω | physCube N B ω = q ∧ velBin δv ω = b i}).Nonempty := by
      rw [hμ, Measure.restrict_apply' hS₀'m] at hq
      obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hq
      exact ⟨ω, hω.2, hω.1⟩
    have hsome := hne.some_mem
    simp only [hwit, dif_pos hne]
    exact ⟨hsome.1, hsome.2.1, hsome.2.2⟩
  refine ⟨b, S₀' ∩ good, wit, ?_, hS₀'m.inter hgoodm, fun x hx => hx.1.1, ?_, ?_, ?_⟩
  · simpa [hb] using hsep
  · calc ENNReal.ofReal (1 / (4 * Λ ^ 2)) * ρ S₀ = ENNReal.ofReal (1 / (4 * Λ ^ 2)) * μ univ := by
          rw [hμuniv]
      _ ≤ μ good := hmass
      _ = ρ (S₀' ∩ good) := by rw [hμ, Measure.restrict_apply hgoodm, inter_comm]
  · intro ω hω hZω
    exact hω.1.2 (Or.inl hZω)
  · intro ω hω i
    have hq : μ {ω' | physCube N B ω' = physCube N B ω ∧ velBin δv ω' = b i} ≠ 0 := by
      fin_cases i
      · exact hω.2.1
      · exact hω.2.2
    obtain ⟨h1, h2, h3⟩ := hwitspec i (physCube N B ω) hq
    refine ⟨h1.1, h2, h3, ?_⟩
    intro hbad
    exact h1.2 (Or.inr ⟨hbad, trivial⟩)

end Submission.Obl.k4_scalar_grid_cartesian_field
