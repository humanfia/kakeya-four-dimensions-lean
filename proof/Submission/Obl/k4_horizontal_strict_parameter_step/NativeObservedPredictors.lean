/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeObservedPredictors.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonFrames
import Submission.Obl.k4_horizontal_strict_parameter_step.NativePairSupport
import Submission.Obl.k4_horizontal_strict_parameter_step.JitterGeometry

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

namespace ObservedPairs

variable {Ω Γ J : Type*} [MeasurableSpace Ω] [DecidableEq Γ] [DecidableEq J]
  {m n : ℕ} {S : Set Ω} {A : Fin m → Set Ω} {B : Fin n → Set Ω}
  (T : ObservedPairs S A B) (group : Fin m → Γ) (block : Fin n → J)
  (frame : Γ × J → ComparisonFrame)

/-- The physical sheet menu before the common colour chart is applied. -/
def physicalPredictors (old : Fin m → Fin 6 → ℝ) (native : Fin n → Fin 4 → ℝ) :
    T.Index group block → Fin 6 → ℝ
  | Sum.inl i => old i.val.1
  | Sum.inr i => affinePredictor (native i.val.1) (frame (i.val.2, block i.val.1)).velocity

theorem comparisonPredictors_eq_rechart (old : Fin m → Fin 6 → ℝ)
    (native : Fin n → Fin 4 → ℝ) (i : T.Index group block) :
    T.comparisonPredictors group block frame old native i =
      (frame (T.colour group block i)).rechart
        (T.physicalPredictors group block frame old native i) := by
  cases i <;> rfl

theorem physical_source (old : Fin m → Fin 6 → ℝ) (native : Fin n → Fin 4 → ℝ)
    (i : Fin T.count) :
    T.physicalPredictors group block frame old native (T.source group block i) =
      old (T.old i) := rfl

theorem physical_witness (old : Fin m → Fin 6 → ℝ) (native : Fin n → Fin 4 → ℝ)
    (i : Fin T.count) :
    T.physicalPredictors group block frame old native (T.witness group block i) =
      affinePredictor (native (T.native i)) (T.markedFrame group block frame i).velocity := rfl

/-- Every matching index comes from an actual observed mark. This retains
representative bounds without charging any unused Cartesian-product entries. -/
theorem index_observed (i : T.Index group block) :
    ∃ r : Fin T.count, i = T.source group block r ∨ i = T.witness group block r := by
  cases i with
  | inl i =>
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp i.property
    refine ⟨r, Or.inl ?_⟩
    apply congrArg Sum.inl
    exact Subtype.ext hr.symm
  | inr i =>
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp i.property
    refine ⟨r, Or.inr ?_⟩
    apply congrArg Sum.inr
    exact Subtype.ext hr.symm

end ObservedPairs

namespace NativeModel

open Submission.Obl.k4_critical_derivative_evaluation_lists

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The actual observed source retains its whole old full-time fit. -/
theorem observed_source_fit {k : ℕ} {s ε D a : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (frame : (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s) → ComparisonFrame)
    (L : Fin (cfg.n k s) → Fin 4 → ℝ)
    (htime : ∀ p ∈ G, p.2 ∈ Icc (0 : ℝ) 1) (p : α × ℝ) (hp : p ∈ G) :
    |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
      predictor (T.physicalPredictors group (cfg.j k s) frame hH L
        (T.source group (cfg.j k s) (T.mark p))) p.2
          (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ cfg.N k ^ ε * a := by
  rw [T.physical_source]
  exact (H.2.2.1 (T.old (T.mark p))).2.2.1 p.1 (T.decode_old p hp).1 p.2 (htime p hp)

/-- The actual observed witness is the true affine fit pulled back with the
SAME velocity colour as its source. Only the original contact and velocity
bin errors are paid; no current pair-floor assumption enters. -/
theorem observed_witness_fit {k : ℕ} {s ε D a χ M : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (frame : (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s) → ComparisonFrame)
    (hframe : ∀ g j, (frame (g, j)).velocity = χ * (g 0 : ℝ))
    (hχ : 0 < χ) (hχeq : χ = cfg.N k ^ (-cfg.e₀))
    (L : Fin (cfg.n k s) → Fin 4 → ℝ)
    (hL : ∀ i (e : Fin 3), |L i e.succ| ≤ M)
    (hfit : ∀ i l, l ∈ cfg.B k s i → ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
      |cfg.b k l 2 + t * cfg.b k l 5 -
        (L i 0 + L i 1 * t + L i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
          L i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * a)
    (htime : ∀ p ∈ G, p.2 ∈ Icc (0 : ℝ) 1)
    (hcontact : ∀ p ∈ G, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ)
    (p : α × ℝ) (hp : p ∈ G) :
    |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
      predictor (T.physicalPredictors group (cfg.j k s) frame hH L
        (T.witness group (cfg.j k s) (T.mark p))) p.2
          (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ cfg.K k * a + 2 * M * χ := by
  rw [T.physical_witness]
  have hvframe : (T.markedFrame group (cfg.j k s) frame (T.mark p)).velocity =
      χ * (group (T.old (T.mark p)) 0 : ℝ) := hframe _ _
  have hgrid := (H.2.2.1 (T.old (T.mark p))).1 p.1 (T.decode_old p hp).1
  have hvel : |cfg.b k p.1 3 -
      (T.markedFrame group (cfg.j k s) frame (T.mark p)).velocity| ≤ χ := by
    rw [hvframe]
    have hcode : ⌊cfg.b k p.1 3 / χ⌋ = group (T.old (T.mark p)) 0 := by
      simpa only [hχeq] using hgrid.1
    simpa only [floorPoint, hcode] using floorPoint_error hχ (cfg.b k p.1 3)
  obtain ⟨hpB, hpI⟩ := T.decode_native p hp
  exact affinePredictor_fit _ _ (htime p hp) hvel (hcontact p hp)
    (hL _ (1 : Fin 3)) (hL _ (2 : Fin 3)) (hfit _ p.1 hpB p.2 hpI)

/-- Actual observed contacts bound all reference grid representatives. No
absolute coefficient bound is assumed for unused reference colours. -/
theorem observed_reference_bounds {k : ℕ} {s ε D a χ : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (hK : 1 ≤ cfg.K k) (hD : 0 < D) (hD1 : D ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hχeq : χ = cfg.N k ^ (-cfg.e₀))
    (hcoeff : ∀ p ∈ G, ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k) :
    ∀ i : T.Index group (cfg.j k s),
      |χ * ((T.colour group (cfg.j k s) i).1 0 : ℝ)| ≤ 3 * cfg.K k ∧
      |D * ((T.colour group (cfg.j k s) i).1 1 : ℝ)| ≤ 3 * cfg.K k ∧
      |D * ((T.colour group (cfg.j k s) i).1 2 : ℝ)| ≤ 3 * cfg.K k := by
  have hbound {x y R : ℝ} (hxy : |x - y| ≤ R) (hx : |x| ≤ 2 * cfg.K k)
      (hR : R ≤ 1) : |y| ≤ 3 * cfg.K k := by
    have ht := abs_sub_le y x 0
    simp only [sub_zero, abs_sub_comm y x] at ht
    linarith
  have hmark (r : Fin T.count) :
      |χ * (group (T.old r) 0 : ℝ)| ≤ 3 * cfg.K k ∧
      |D * (group (T.old r) 1 : ℝ)| ≤ 3 * cfg.K k ∧
      |D * (group (T.old r) 2 : ℝ)| ≤ 3 * cfg.K k := by
    let p := T.representative r
    have hp := T.representative_support r
    have hg := (H.2.2.1 (T.old r)).1 p.1 (T.representative_old r).1
    have hg0 : ⌊cfg.b k p.1 3 / χ⌋ = group (T.old r) 0 := by
      simpa only [hχeq] using hg.1
    have h0 : |cfg.b k p.1 3 - χ * (group (T.old r) 0 : ℝ)| ≤ χ := by
      simpa only [floorPoint, hg0] using floorPoint_error hχ (cfg.b k p.1 3)
    have h1 : |cfg.b k p.1 0 - D * (group (T.old r) 1 : ℝ)| ≤ D := by
      simpa only [floorPoint, hg.2.1] using floorPoint_error hD (cfg.b k p.1 0)
    have h2 : |cfg.b k p.1 1 - D * (group (T.old r) 2 : ℝ)| ≤ D := by
      simpa only [floorPoint, hg.2.2] using floorPoint_error hD (cfg.b k p.1 1)
    exact ⟨hbound h0 (hcoeff p hp 3) hχ1, hbound h1 (hcoeff p hp 0) hD1,
      hbound h2 (hcoeff p hp 1) hD1⟩
  intro i
  obtain ⟨r, hi | hi⟩ := T.index_observed group (cfg.j k s) i
  · subst i
    exact hmark r
  · subst i
    exact hmark r

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
