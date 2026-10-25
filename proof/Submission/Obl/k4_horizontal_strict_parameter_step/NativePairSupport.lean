/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativePairSupport.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeWitnesses
import Submission.Obl.k4_horizontal_strict_parameter_step.ObservedPairs
import Submission.Obl.k4_horizontal_coefficient_count.Bounded

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Native and old assignments give a finite marked comparison on a measurable
conull original support, with bounded coefficients and the original contact defect. -/
theorem observed_pair_support {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hbasic : cfg.Basic) (hK : 0 ≤ cfg.K k)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ cfg.μ k) (hσ0 : σ univ ≠ 0)
    {ε D a₀ : ℝ} {m : ℕ} {AH : Fin m → Set α} {qH : Fin m → Fin 3 → ℤ}
    {hH : Fin m → Fin 6 → ℝ}
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a₀ m AH qH hH) :
    ∃ G : Set (α × ℝ), MeasurableSet G ∧ (∀ᵐ p ∂σ, p ∈ G) ∧
      (∀ p ∈ G, p.2 ∈ Icc (0 : ℝ) 1 ∧ (∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k) ∧
        |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) ∧
      Nonempty (ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
        (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i))) := by
  classical
  obtain ⟨hb, hν, -, hdom, -, hμtime, -, -, hbase, hpoly⟩ := hbasic k
  letI := hν
  have hμ0 : cfg.μ k univ ≠ 0 := fun h => hσ0
    (le_antisymm ((hσ univ).trans_eq h) bot_le)
  obtain ⟨hP, hcontact⟩ := cfg.native_equation a hμ0
  have hscalar : ∀ᵐ p ∂cfg.μ k, ∀ t ∈ Icc (0 : ℝ) 1,
      |cfg.b k p.1 2 + t * cfg.b k p.1 5| ≤ cfg.K k := by
    filter_upwards [hpoly] with p hp t ht
    have hh := (hp.1 t ht).1
    simpa only [hP, MvPolynomial.eval_X, Data.x, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] using hh
  have hcoeff := Submission.Obl.k4_horizontal_coefficient_count.current_ae_coefficient_bound
    (cfg.ν k) (cfg.μ k) (cfg.b k) hb hK hdom hbase hscalar
  let old : Fin m → Set (α × ℝ) := fun i => AH i ×ˢ univ
  let native : Fin (cfg.n k s) → Set (α × ℝ) :=
    fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)
  have hold : ∀ i, MeasurableSet (old i) :=
    fun i => (H.1 i).prod MeasurableSet.univ
  have hnative : ∀ i, MeasurableSet (native i) :=
    fun i => (a.fitted_measurable i).prod measurableSet_Icc
  have hcoeffm : MeasurableSet {p : α × ℝ | ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k} := by
    have he : {p : α × ℝ | ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k} =
        ⋂ e, {p : α × ℝ | |cfg.b k p.1 e| ≤ 2 * cfg.K k} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter fun e => measurableSet_le (by fun_prop) measurable_const
  have hcontactm : MeasurableSet {p : α × ℝ |
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)} :=
    measurableSet_le (by fun_prop) measurable_const
  let G := (((univ ×ˢ Icc (0 : ℝ) 1) ∩
    {p : α × ℝ | ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k}) ∩
    {p | |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)}) ∩
      (⋃ i, old i) ∩ (⋃ i, native i)
  have hG : MeasurableSet G :=
    ((((MeasurableSet.univ.prod measurableSet_Icc).inter hcoeffm).inter hcontactm).inter
      (MeasurableSet.iUnion hold)).inter (MeasurableSet.iUnion hnative)
  have htime : ∀ᵐ p ∂cfg.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
    apply ae_iff.mpr
    have he : {p : α × ℝ | p.2 ∉ Icc (0 : ℝ) 1} = (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
      ext p
      simp
    rw [he]
    exact hμtime
  have holdAE : ∀ᵐ p ∂σ, ∃ i, p.1 ∈ AH i := by
    apply ae_iff.mpr
    exact H.2.2.2
  have hGAE : ∀ᵐ p ∂σ, p ∈ G := by
    filter_upwards [ae_mono hσ htime, ae_mono hσ hcoeff,
      ae_mono hσ hcontact, holdAE, ae_mono hσ a.covers] with p ht hc hd ho hn
    refine ⟨⟨⟨⟨⟨mem_univ _, ht⟩, hc⟩, hd⟩, ?_⟩, ?_⟩
    · obtain ⟨i, hi⟩ := ho
      exact mem_iUnion.mpr ⟨i, hi, mem_univ _⟩
    · obtain ⟨i, hi, hit⟩ := hn
      exact mem_iUnion.mpr ⟨i, hi, hit⟩
  have hSne : G.Nonempty := by
    by_contra hn
    have he : G = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hσ0
    have hh := ae_iff.mp hGAE
    simpa only [he, mem_empty_iff_false, not_false_eq_true, Set.ofPred_true] using hh
  refine ⟨G, hG, hGAE, ?_, exists_observed_pairs G hG hSne old native hold hnative ?_ ?_⟩
  · intro p hp
    exact ⟨hp.1.1.1.1.2, hp.1.1.1.2, hp.1.1.2⟩
  · intro p hp
    exact mem_iUnion.mp hp.1.2
  · intro p hp
    exact mem_iUnion.mp hp.2

end NativeModel

end Submission.Obl.k4_horizontal_strict_parameter_step
