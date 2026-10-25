/- Adapted from same-tree o168/x0569, SubLayer.lean. Chart restriction and
list recovery use the ACCEPTED o166 AtlasPruning API without re-proving it. -/
import Submission.Obl.k4_scalar_guarded_entropic_path.Interface
import Submission.Obl.k4_scalar_normalized_exact_refinement.AtlasPruning

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

noncomputable section

namespace Layer

variable {w : ℕ}

/-- The kept pieces of a layer, as a finset. -/
def keptSet (f : Layer w) (keep : Fin f.n → Prop) [DecidablePred keep] : Finset (Fin f.n) :=
  Finset.univ.filter keep

/-- The order embedding enumerating the kept pieces. -/
def keptEmb (f : Layer w) (keep : Fin f.n → Prop) [DecidablePred keep] :
    Fin (f.keptSet keep).card ↪o Fin f.n :=
  (f.keptSet keep).orderEmbOfFin rfl

theorem keptEmb_keep (f : Layer w) (keep : Fin f.n → Prop) [DecidablePred keep]
    (i : Fin (f.keptSet keep).card) : keep (f.keptEmb keep i) := by
  have := (f.keptSet keep).orderEmbOfFin_mem rfl i
  simp only [keptSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

theorem exists_keptEmb (f : Layer w) (keep : Fin f.n → Prop) [DecidablePred keep]
    {i : Fin f.n} (hi : keep i) : ∃ i', f.keptEmb keep i' = i := by
  have hmem : i ∈ f.keptSet keep := by simp [keptSet, hi]
  have hrange := (f.keptSet keep).range_orderEmbOfFin rfl
  have : i ∈ Set.range ((f.keptSet keep).orderEmbOfFin rfl) := by
    rw [hrange]; exact hmem
  obtain ⟨i', hi'⟩ := this
  exact ⟨i', hi'⟩

theorem keptEmb_injective (f : Layer w) (keep : Fin f.n → Prop) [DecidablePred keep] :
    Function.Injective (f.keptEmb keep) :=
  (f.keptEmb keep).injective

/-- The layer made of the kept pieces, in their original order. -/
def prune (f : Layer w) (keep : Fin f.n → Prop) [DecidablePred keep] : Layer w :=
  ⟨f.T, (f.keptSet keep).card, f.world ∘ f.keptEmb keep, f.block ∘ f.keptEmb keep,
    f.assignment ∘ f.keptEmb keep, f.witness ∘ f.keptEmb keep, f.u ∘ f.keptEmb keep,
    f.v ∘ f.keptEmb keep, f.width ∘ f.keptEmb keep, f.graph ∘ f.keptEmb keep,
    Submission.Obl.k4_scalar_normalized_exact_refinement.restrictedChartList
      ⟨f.keptEmb keep, f.keptEmb_injective keep⟩ f.list⟩

end Layer

namespace Layer

open MeasureTheory
open Submission.Obl.k4_scalar_linear_critical_extremizers

variable {w : ℕ}

/-- Reindexing retained labels leaves their full original witnesses intact. -/
theorem prune_witness_union (f : Layer w) (keep : Fin f.n → Prop) [DecidablePred keep]
    (g : Fin w) :
    {z | ∃ i, (f.prune keep).world i = g ∧ z ∈ (f.prune keep).witness i} =
      {z | ∃ i, keep i ∧ f.world i = g ∧ z ∈ f.witness i} := by
  ext z
  constructor
  · rintro ⟨i, hi, hz⟩
    exact ⟨f.keptEmb keep i, f.keptEmb_keep keep i, hi, hz⟩
  · rintro ⟨i, hi, hworld, hz⟩
    obtain ⟨i', rfl⟩ := f.exists_keptEmb keep hi
    exact ⟨i', hworld, hz⟩

/-- The accepted injective-restriction theorem preserves both truth flags. -/
theorem chartData_prune {p : Code} {B k : ℕ} {r b h ε : ℝ} {flag : Bool}
    {f : Layer (p.1 k)}
    (hc : Split.ChartData p B r b h ε flag k f.T f.n f.world f.block
      f.assignment f.witness f.u f.v f.width f.graph f.list)
    (keep : Fin f.n → Prop) [DecidablePred keep]
    (hcov : ENNReal.ofReal (p.N k ^ (-ε)) ≤ ∑ g,
      ENNReal.ofReal (p.weight k g) * Split.mu p k g
        {z | ∃ i, keep i ∧ f.world i = g ∧ z ∈ f.witness i}) :
    let F := f.prune keep
    Split.ChartData p B r b h ε flag k F.T F.n F.world F.block
      F.assignment F.witness F.u F.v F.width F.graph F.list := by
  apply Submission.Obl.k4_scalar_normalized_exact_refinement.chartData_restrict hc
    ⟨f.keptEmb keep, f.keptEmb_injective keep⟩
  change ENNReal.ofReal (p.N k ^ (-ε)) ≤ ∑ g,
    ENNReal.ofReal (p.weight k g) * Split.mu p k g
      {z | ∃ i, (f.prune keep).world i = g ∧ z ∈ (f.prune keep).witness i}
  simp_rw [f.prune_witness_union keep]
  exact hcov

/-- A current original-law submeasure supplies the retained union-mass
clause, without changing any earlier TRUE witness. -/
theorem chartData_prune_of_submeasure {p : Code} {B k : ℕ} {r b h ε : ℝ} {flag : Bool}
    {f : Layer (p.1 k)}
    (hc : Split.ChartData p B r b h ε flag k f.T f.n f.world f.block
      f.assignment f.witness f.u f.v f.width f.graph f.list)
    (keep : Fin f.n → Prop) [DecidablePred keep]
    (σ : Fin (p.1 k) → Measure Incidence) (hσ : ∀ g, σ g ≤ Split.mu p k g)
    (hcover : ∀ g, σ g {z | ∃ i, keep i ∧ f.world i = g ∧ z ∈ f.witness i}ᶜ = 0)
    (hmass : ENNReal.ofReal (p.N k ^ (-ε)) ≤
      ∑ g, ENNReal.ofReal (p.weight k g) * σ g Set.univ) :
    let F := f.prune keep
    Split.ChartData p B r b h ε flag k F.T F.n F.world F.block
      F.assignment F.witness F.u F.v F.width F.graph F.list := by
  apply chartData_prune hc keep
  apply hmass.trans
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul' le_rfl
  let E : Set Incidence := {z | ∃ i, keep i ∧ f.world i = g ∧ z ∈ f.witness i}
  calc
    σ g Set.univ = σ g (E ∪ Eᶜ) := by rw [Set.union_compl_self]
    _ ≤ σ g E + σ g Eᶜ := measure_union_le _ _
    _ = σ g E := by rw [hcover g, add_zero]
    _ ≤ Split.mu p k g E := hσ g E

end Layer


end

end Submission.Obl.k4_scalar_guarded_entropic_path
