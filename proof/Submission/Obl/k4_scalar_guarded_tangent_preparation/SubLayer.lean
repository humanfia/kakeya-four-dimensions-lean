/-
Sub-families of chart layers.

`pullLists`, `card_pullLists_le` and the structure of `chartData_subfamily` are adapted
from this LOT tree (g-oai-074), obligation o131 `k4_scalar_chart_normalization`, branch
x0445 (session x0445, own code of this tree), file
`Submission/Obl/k4_scalar_chart_normalization/NormChart.lean` (`chartData_sub`), renamed
into this namespace. Here the selected incidences are kept unchanged, so the true floor
of every surviving piece survives.
-/
import Submission.Obl.k4_scalar_guarded_tangent_preparation.Interface

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Lists pulled back along an injection of pieces. -/
def pullLists {m n : ℕ} {α β : Type*} (e : Fin m → Fin n) (he : Function.Injective e)
    (Λ : α → β → Finset (Fin n)) : α → β → Finset (Fin m) :=
  fun a z => (Λ a z).preimage e he.injOn

theorem mem_pullLists {m n : ℕ} {α β : Type*} (e : Fin m → Fin n) (he : Function.Injective e)
    (Λ : α → β → Finset (Fin n)) (a : α) (z : β) (i : Fin m) :
    i ∈ pullLists e he Λ a z ↔ e i ∈ Λ a z := by
  simp [pullLists]

theorem card_pullLists_le {m n : ℕ} {α β : Type*} (e : Fin m → Fin n)
    (he : Function.Injective e) (Λ : α → β → Finset (Fin n)) (a : α) (z : β) :
    (pullLists e he Λ a z).card ≤ (Λ a z).card :=
  Finset.card_le_card_of_injOn e (fun i hi => by simpa [pullLists] using hi) he.injOn

/-- Dropping pieces keeps (true or false) chart data, as soon as the coverage of the
surviving pieces is checked. -/
theorem chartData_subfamily {p : Code} {B : ℕ} {r b h ε : ℝ} {truth : Bool} {k T n m : ℕ}
    {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set Coeff}
    {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ} {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hcd : Split.ChartData p B r b h ε truth k T n γ j A C u v J P Λ)
    (e : Fin m → Fin n) (he : Function.Injective e)
    (hcov : ENNReal.ofReal (p.N k ^ (-ε)) ≤
      ∑ a : Fin (p.1 k), ENNReal.ofReal (p.weight k a) *
        Split.mu p k a {q | ∃ i, γ (e i) = a ∧ q ∈ C (e i)}) :
    Split.ChartData p B r b h ε truth k T m (γ ∘ e) (j ∘ e) (A ∘ e) (C ∘ e) (u ∘ e) (v ∘ e)
      (J ∘ e) (P ∘ e) (pullLists e he Λ) := by
  obtain ⟨hT, hn, hmeas, hdisj, hsub, hpiece, hcard, hΛm, hΛ, _⟩ := hcd
  refine ⟨hT, ?_, fun i => hmeas (e i), ?_, fun i => hsub (e i), fun i => hpiece (e i),
    fun a z => ?_, fun a i => ?_, fun i => ?_, hcov⟩
  · have hmn : m ≤ n := by
      simpa using Fintype.card_le_of_injective e he
    exact le_trans (by exact_mod_cast hmn) hn
  · intro i i' hii' hγ hj
    exact hdisj (e i) (e i') (he.ne hii') hγ hj
  · exact le_trans (by exact_mod_cast card_pullLists_le e he Λ a z) (hcard a z)
  · have h := hΛm a (e i)
    convert h using 1
    ext z
    exact mem_pullLists e he Λ a z i
  · refine le_antisymm ?_ zero_le
    rw [← hΛ (e i)]
    apply measure_mono
    intro q hq
    exact ⟨hq.1, fun h => hq.2 ((mem_pullLists e he Λ _ _ i).mpr h)⟩

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
    pullLists (f.keptEmb keep) (f.keptEmb_injective keep) f.list⟩

end Layer

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
