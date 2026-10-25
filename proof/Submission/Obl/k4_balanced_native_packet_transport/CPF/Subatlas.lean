/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/Subatlas.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/Subatlas.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions

/-! Restrict a chart collection to a finite set of labels, with an explicit new
`Fin` indexing.  This removes whole charts without leaving empty labels whose
genuine mass floors could fail. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory
open scoped ENNReal

noncomputable section

def Atlas.labelEquiv {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C)) :
    Fin s.card ≃ s :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card s = s.card)).symm

def Atlas.labelEmbedding {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C)) :
    Fin s.card ↪ Fin a.C :=
  (a.labelEquiv s).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩

theorem Atlas.labelEmbedding_mem {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) (i : Fin s.card) : a.labelEmbedding s i ∈ s :=
  (a.labelEquiv s i).property

def Atlas.subatlas {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C)) : Atlas p k where
  κ := a.κ
  T := a.T
  C := s.card
  γ := a.γ ∘ a.labelEmbedding s
  j := a.j ∘ a.labelEmbedding s
  c := a.c ∘ a.labelEmbedding s
  u := a.u ∘ a.labelEmbedding s
  Q := a.Q ∘ a.labelEmbedding s
  R := a.R ∘ a.labelEmbedding s
  A := a.A ∘ a.labelEmbedding s
  F := a.F ∘ a.labelEmbedding s

theorem Atlas.subatlas_card_le {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) : (a.subatlas s).C ≤ a.C :=
  (Finset.card_le_card (Finset.subset_univ s)).trans_eq (Finset.card_fin a.C)

theorem Atlas.subatlas_separated {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) (ha : a.Separated) : (a.subatlas s).Separated := by
  intro b b' hne hγ hj
  exact ha _ _ (fun h => hne ((a.labelEmbedding s).injective h)) hγ hj

theorem Atlas.sum_labels {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C))
    {β : Type*} [AddCommMonoid β] (f : Fin a.C → β) :
    (∑ i : Fin s.card, f (a.labelEmbedding s i)) = ∑ b ∈ s, f b := by
  change (∑ i : Fin s.card, f (a.labelEquiv s i).val) = _
  rw [Equiv.sum_comp (a.labelEquiv s) (fun i : s => f i.val)]
  exact Finset.sum_coe_sort s f

theorem Atlas.subatlas_mass {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) :
    (a.subatlas s).mass = ∑ b ∈ s, ENNReal.ofReal (p.ω k (a.γ b)) *
      ((p.ν k (a.γ b)).prod volume) (a.F b) := by
  exact a.sum_labels s (fun b => ENNReal.ofReal (p.ω k (a.γ b)) *
    ((p.ν k (a.γ b)).prod volume) (a.F b))

def Atlas.restrictList {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C))
    (lst : Finset (Fin a.C)) : Finset (Fin s.card) :=
  Finset.univ.filter (fun i => a.labelEmbedding s i ∈ lst)

theorem Atlas.mem_restrictList {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) (lst : Finset (Fin a.C)) (i : Fin s.card) :
    i ∈ a.restrictList s lst ↔ a.labelEmbedding s i ∈ lst := by
  classical
  simp [restrictList]

theorem Atlas.restrictList_card_le {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) (lst : Finset (Fin a.C)) :
    (a.restrictList s lst).card ≤ lst.card := by
  classical
  exact Finset.card_le_card_of_injOn (a.labelEmbedding s)
    (fun i hi => (a.mem_restrictList s lst i).mp hi)
    (a.labelEmbedding s).injective.injOn

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
