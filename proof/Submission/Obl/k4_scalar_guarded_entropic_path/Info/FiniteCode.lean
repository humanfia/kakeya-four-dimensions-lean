/-
Adapted from this LOT tree, obligation o168, session x0569, branch x0569 (commit 58cd9e8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/FiniteCode.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Interface

/-!
# Finite observation codes of a bounded reference law

A reference law `σ` carried by incidences with time in `[0, 1]` and coefficients bounded by
`K` sees only finitely many grid states: base and hidden bins at the tangent resolutions
`j / m` (`j ≤ m²`) and the finest velocity bin at resolution `m`. `exists_finite_code`
builds the measurable finite code `X`, the state code `Y` (base/hidden part), the velocity
code `Z`, and the decoders `q`, `c` used by `ReferenceLaws`, correct `σ`-almost
everywhere. `velocityPalette` is the normalized velocity marginal of `σ` (or a fixed
probability when `σ = 0`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The full grid state of an incidence. -/
abbrev GridTuple (m : ℕ) : Type :=
  (Fin (m ^ 2 + 1) → Fin 2 → ℤ) × (Fin (m ^ 2 + 1) → ℤ) × ℤ

/-- The grid state: all base and hidden bins at `j / m`, and the velocity bin at `m`. -/
def gridTuple (N : ℝ) (m : ℕ) (z : Incidence) : GridTuple m :=
  (fun j => baseBin N ((j : ℝ) / (m : ℝ)) z, fun j => hiddenBin N ((j : ℝ) / (m : ℝ)) z,
    velocityBin N (m : ℝ) (z.1.2 1))

theorem measurable_baseBin (N r : ℝ) (e : Fin 2) :
    Measurable (fun z : Incidence => baseBin N r z e) := by
  unfold baseBin
  apply Int.measurable_floor.comp
  apply Measurable.div_const
  fin_cases e
  · exact measurable_snd
  · show Measurable (fun z : Incidence => Split.y z.1 z.2)
    unfold Split.y; fun_prop

theorem measurable_hiddenBin (N s : ℝ) : Measurable (fun z : Incidence => hiddenBin N s z) := by
  unfold hiddenBin
  apply Int.measurable_floor.comp
  apply Measurable.div_const
  unfold Split.x; fun_prop

theorem measurable_velocityBin_coord (N b : ℝ) :
    Measurable (fun z : Incidence => velocityBin N b (z.1.2 1)) := by
  unfold velocityBin
  apply Int.measurable_floor.comp
  apply Measurable.div_const
  fun_prop

theorem measurable_gridTuple (N : ℝ) (m : ℕ) : Measurable (gridTuple N m) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ (measurable_velocityBin_coord N _))
  · exact measurable_pi_iff.mpr fun j =>
      measurable_pi_iff.mpr fun e => measurable_baseBin N _ e
  · exact measurable_pi_iff.mpr fun j => measurable_hiddenBin N _

/-- The bounded box of grid states. -/
def gridBox (m : ℕ) (M : ℤ) : Set (GridTuple m) :=
  (Set.pi univ fun _ => Set.pi univ fun _ => Icc (-M) M) ×ˢ
    ((Set.pi univ fun _ => Icc (-M) M) ×ˢ Icc (-M) M)

theorem gridBox_finite (m : ℕ) (M : ℤ) : (gridBox m M).Finite := by
  refine Set.Finite.prod ?_ (Set.Finite.prod ?_ (Set.finite_Icc _ _))
  · exact Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _
  · exact Set.Finite.pi fun _ => Set.finite_Icc _ _

theorem zero_mem_gridBox (m : ℕ) {M : ℤ} (hM : 0 ≤ M) : (0 : GridTuple m) ∈ gridBox m M := by
  refine ⟨fun j _ e _ => ?_, fun j _ => ?_, ?_⟩ <;> simp [hM]

theorem abs_floor_div_le {x w B : ℝ} (hw : 0 < w) (hx : |x| ≤ B) (hB : B / w ≤ ((⌈B / w⌉ : ℤ) : ℝ)) :
    |(⌊x / w⌋ : ℤ)| ≤ ⌈B / w⌉ + 1 := by
  have h1 : x / w ≤ B / w := div_le_div_of_nonneg_right (le_of_abs_le hx) hw.le
  have h2 : -(B / w) ≤ x / w := by
    rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_le_of_abs_le hx) hw.le
  have hf1 := Int.floor_le (x / w)
  have hf2 := Int.lt_floor_add_one (x / w)
  rw [abs_le]
  constructor
  · have : (-(⌈B / w⌉ + 1) : ℝ) ≤ (⌊x / w⌋ : ℝ) := by linarith
    exact_mod_cast this
  · have : ((⌊x / w⌋ : ℤ) : ℝ) ≤ ((⌈B / w⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- The grid state of a bounded incidence lies in the bounded box. -/
theorem gridTuple_mem_gridBox {N K : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    {z : Incidence} (ht : z.2 ∈ Icc (0 : ℝ) 1) (hl : ∀ e, |z.1.2 e| ≤ K) :
    gridTuple N m z ∈ gridBox m (⌈3 * K * N ^ (m : ℝ)⌉ + 1) := by
  have hNpos : 0 < N := by linarith
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨ht0, ht1⟩ := ht
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- widths at tangent resolutions at most m are at least N^(-m)
  have hw : ∀ r : ℝ, r ≤ m → 1 / N ^ (-r) ≤ N ^ (m : ℝ) := by
    intro r hr
    rw [Real.rpow_neg hNpos.le, one_div, inv_inv]
    exact Real.rpow_le_rpow_of_exponent_le hN hr
  have hbound : ∀ (x r : ℝ), |x| ≤ 3 * K → r ≤ m →
      |(⌊x / N ^ (-r)⌋ : ℤ)| ≤ ⌈3 * K * N ^ (m : ℝ)⌉ + 1 := by
    intro x r hx hr
    have hwpos : 0 < N ^ (-r) := Real.rpow_pos_of_pos hNpos _
    have h1 := abs_floor_div_le hwpos hx (Int.le_ceil _)
    refine h1.trans ?_
    gcongr
    calc 3 * K / N ^ (-r) = 3 * K * (1 / N ^ (-r)) := by ring
      _ ≤ 3 * K * N ^ (m : ℝ) := by gcongr; exact hw r hr
  have hjr : ∀ j : Fin (m ^ 2 + 1), ((j : ℕ) : ℝ) / (m : ℝ) ≤ m := by
    intro j
    rw [div_le_iff₀ (by linarith)]
    have : (j : ℕ) ≤ m ^ 2 := Nat.lt_succ_iff.mp j.isLt
    calc ((j : ℕ) : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
      _ = m * m := by push_cast; ring
  have hy : |Split.y z.1 z.2| ≤ 3 * K := by
    have : |z.2 * z.1.2 1| ≤ K := by
      rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg (z.1.2 1), hl 1]
    calc |Split.y z.1 z.2| = |z.1.2 0 + z.2 * z.1.2 1| := rfl
      _ ≤ |z.1.2 0| + |z.2 * z.1.2 1| := abs_add_le _ _
      _ ≤ 3 * K := by linarith [hl 0]
  have hx : |Split.x z.1 z.2| ≤ 3 * K := by
    have hA : |z.2 * z.1.2 3| ≤ K := by
      rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg (z.1.2 3), hl 3]
    have hB : |z.2 ^ 2 * z.1.2 4| ≤ K := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have : z.2 ^ 2 ≤ 1 := by nlinarith
      nlinarith [abs_nonneg (z.1.2 4), hl 4]
    calc |Split.x z.1 z.2| = |z.1.2 2 + z.2 * z.1.2 3 + z.2 ^ 2 * z.1.2 4| := rfl
      _ ≤ |z.1.2 2 + z.2 * z.1.2 3| + |z.2 ^ 2 * z.1.2 4| := abs_add_le _ _
      _ ≤ |z.1.2 2| + |z.2 * z.1.2 3| + |z.2 ^ 2 * z.1.2 4| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 3 * K := by linarith [hl 2]
  have ht' : |z.2| ≤ 3 * K := by rw [abs_of_nonneg ht0]; linarith
  have hv : |z.1.2 1| ≤ 3 * K := by linarith [hl 1]
  refine ⟨fun j _ e _ => ?_, fun j _ => ?_, ?_⟩
  · simp only [gridTuple, baseBin, mem_Icc]
    fin_cases e
    · exact abs_le.mp (hbound _ _ (by simpa using ht') (hjr j))
    · exact abs_le.mp (hbound _ _ (by simpa using hy) (hjr j))
  · simp only [gridTuple, hiddenBin, mem_Icc]
    exact abs_le.mp (hbound _ _ hx (hjr j))
  · simp only [gridTuple, velocityBin, mem_Icc]
    exact abs_le.mp (hbound _ _ hv le_rfl)

/-- **Finite codes.** -/
theorem exists_finite_code {N K : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    (σ : Measure Incidence)
    (hsupp : ∀ᵐ z ∂σ, z.2 ∈ Icc (0 : ℝ) 1 ∧ ∀ e, |z.1.2 e| ≤ K) :
    ∃ (n : ℕ) (X : Incidence → Fin n) (Y : Fin n → ℕ) (Z : Fin n → ℤ)
      (q : Fin (m ^ 2 + 1) → ℕ → Fin 2 → ℤ) (c : Fin (m ^ 2 + 1) → ℕ → ℤ),
      Measurable X ∧
      ∀ᵐ z ∂σ, Z (X z) = velocityBin N (m : ℝ) (z.1.2 1) ∧
        ∀ j : Fin (m ^ 2 + 1),
          baseBin N ((j : ℝ) / (m : ℝ)) z = q j (Y (X z)) ∧
          hiddenBin N ((j : ℝ) / (m : ℝ)) z = c j (Y (X z)) := by
  classical
  set M : ℤ := ⌈3 * K * N ^ (m : ℝ)⌉ + 1 with hMdef
  have hM : 0 ≤ M := by
    have : (0 : ℝ) ≤ 3 * K * N ^ (m : ℝ) := by positivity
    have := Int.ceil_nonneg this
    omega
  set S : Finset (GridTuple m) := (gridBox_finite m M).toFinset with hS
  have h0S : (0 : GridTuple m) ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact zero_mem_gridBox m hM
  set n := S.card with hn
  let e : S ≃ Fin n := S.equivFin
  let X : Incidence → Fin n := fun z =>
    if h : gridTuple N m z ∈ S then e ⟨gridTuple N m z, h⟩ else e ⟨0, h0S⟩
  -- an injective code of the base/hidden part
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat
    ((Fin (m ^ 2 + 1) → Fin 2 → ℤ) × (Fin (m ^ 2 + 1) → ℤ))
  let dec : ℕ → (Fin (m ^ 2 + 1) → Fin 2 → ℤ) × (Fin (m ^ 2 + 1) → ℤ) := fun y =>
    if h : ∃ u, f u = y then Classical.choose h else 0
  have hdec : ∀ u, dec (f u) = u := by
    intro u
    have h : ∃ u', f u' = f u := ⟨u, rfl⟩
    simp only [dec, h, dif_pos]
    exact hf (Classical.choose_spec h)
  let Y : Fin n → ℕ := fun i => f ((e.symm i).1.1, (e.symm i).1.2.1)
  let Z : Fin n → ℤ := fun i => (e.symm i).1.2.2
  let q : Fin (m ^ 2 + 1) → ℕ → Fin 2 → ℤ := fun j y => (dec y).1 j
  let c : Fin (m ^ 2 + 1) → ℕ → ℤ := fun j y => (dec y).2 j
  refine ⟨n, X, Y, Z, q, c, ?_, ?_⟩
  · -- measurability through the fibres of a map into a finite type
    apply measurable_to_countable'
    intro i
    have hfib : X ⁻¹' {i} = gridTuple N m ⁻¹' {u | ∃ h : u ∈ S, e ⟨u, h⟩ = i} ∪
        (gridTuple N m ⁻¹' (↑S)ᶜ ∩ {_z | e ⟨0, h0S⟩ = i}) := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_setOf_eq, mem_inter_iff,
        mem_compl_iff, Finset.mem_coe, X]
      by_cases h : gridTuple N m z ∈ S
      · simp [h]
      · simp [h]
    rw [hfib]
    refine MeasurableSet.union ?_ ?_
    · exact (measurable_gridTuple N m)
        ((S.finite_toSet.subset (fun u hu => hu.fst)).measurableSet)
    · refine MeasurableSet.inter ?_ ?_
      · exact (measurable_gridTuple N m) (S.finite_toSet.measurableSet.compl)
      · by_cases h : e ⟨0, h0S⟩ = i
        · simp [h]
        · simp [h]
  · filter_upwards [hsupp] with z hz
    have hmem : gridTuple N m z ∈ S := by
      rw [hS, Set.Finite.mem_toFinset]
      exact gridTuple_mem_gridBox hN hK hm hz.1 hz.2
    have hX : X z = e ⟨gridTuple N m z, hmem⟩ := by simp only [X, dif_pos hmem]
    have hsymm : (e.symm (X z)).1 = gridTuple N m z := by rw [hX, Equiv.symm_apply_apply]
    refine ⟨?_, fun j => ⟨?_, ?_⟩⟩
    · show (e.symm (X z)).1.2.2 = _
      rw [hsymm]; rfl
    · show _ = (dec (f ((e.symm (X z)).1.1, (e.symm (X z)).1.2.1))).1 j
      rw [hdec, hsymm]; rfl
    · show _ = (dec (f ((e.symm (X z)).1.1, (e.symm (X z)).1.2.1))).2 j
      rw [hdec, hsymm]; rfl

/-- The normalized velocity marginal of a finite law (a fixed probability for the zero law). -/
def velocityPalette (σ : Measure Incidence) : Measure ℝ :=
  if σ Set.univ = 0 then (volume.restrict (Ico (0 : ℝ) 1))
  else (σ Set.univ)⁻¹ • σ.map (fun z : Incidence => z.1.2 1)

theorem velocityPalette_spec (σ : Measure Incidence) [IsFiniteMeasure σ] :
    IsProbabilityMeasure (velocityPalette σ) ∧
      σ.map (fun z : Incidence => z.1.2 1) = (σ Set.univ) • velocityPalette σ := by
  have hmeas : Measurable (fun z : Incidence => z.1.2 1) := by fun_prop
  by_cases h0 : σ Set.univ = 0
  · have hσ : σ = 0 := Measure.measure_univ_eq_zero.mp h0
    refine ⟨?_, ?_⟩
    · rw [velocityPalette, if_pos h0]
      constructor
      rw [Measure.restrict_apply_univ, Real.volume_Ico]; simp
    · simp [hσ]
  · have htop : σ Set.univ ≠ ⊤ := measure_ne_top σ _
    refine ⟨?_, ?_⟩
    · rw [velocityPalette, if_neg h0]
      constructor
      rw [Measure.smul_apply, Measure.map_apply hmeas MeasurableSet.univ, preimage_univ,
        smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]
    · rw [velocityPalette, if_neg h0, smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
