import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WorldRestriction

/-! Restrict an atlas to an injectively indexed set of charts. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable def subatlas {p : Data} {k n : ℕ} (a : Atlas p k)
    (f : Fin n → Fin a.C) : Atlas p k := by
  classical
  exact {
    T := a.T
    C := n
    γ := a.γ ∘ f
    j := a.j ∘ f
    c := a.c ∘ f
    u := a.u ∘ f
    Q := a.Q ∘ f
    R := a.R ∘ f
    A := a.A ∘ f
    F := a.F ∘ f
    lst := fun γ o => Finset.univ.filter (fun b => f b ∈ a.lst γ o) }

theorem subatlas_mem_list {p : Data} {k n : ℕ} (a : Atlas p k)
    (f : Fin n → Fin a.C) (γ : Fin (p.W k)) (o : Observation) (b : Fin n) :
    b ∈ (subatlas a f).lst γ o ↔ f b ∈ a.lst γ o := by
  classical
  change b ∈ Finset.univ.filter (fun b' => f b' ∈ a.lst γ o) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem subatlas_list_card_le {p : Data} {k n : ℕ} (a : Atlas p k)
    (f : Fin n → Fin a.C) (hf : Function.Injective f) (γ : Fin (p.W k)) (o : Observation) :
    ((subatlas a f).lst γ o).card ≤ (a.lst γ o).card := by
  classical
  let L := (subatlas a f).lst γ o
  calc
    _ = (L.image f).card := (Finset.card_image_of_injective L hf).symm
    _ ≤ (a.lst γ o).card := by
      apply Finset.card_le_card
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
      change b' ∈ Finset.univ.filter (fun b => f b ∈ a.lst γ o) at hb'
      exact (Finset.mem_filter.mp hb').2

theorem keptWorldIndex_injective {W : ℕ} (S : Finset (Fin W)) :
    Function.Injective (keptWorldIndex S) := by
  intro b b' h
  apply S.equivFin.symm.injective
  exact Subtype.ext h

theorem sum_keptWorldIndex {W : ℕ} {α : Type*} [AddCommMonoid α]
    (S : Finset (Fin W)) (f : Fin W → α) :
    (∑ b : Fin S.card, f (keptWorldIndex S b)) = ∑ b ∈ S, f b :=
  Submission.Obl.k4_dyadic_crop_worlds.sum_equivFin S f

noncomputable def RemainderGeometry.retainedIndex {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (S : (k : ℕ) → Finset (Fin (q.W k))) (k : ℕ) :
    Fin (S k).card → Fin (a.parent k).C :=
  fun b => a.worlds k (keptWorldIndex (S k) b)

theorem RemainderGeometry.retainedIndex_injective {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (S : (k : ℕ) → Finset (Fin (q.W k))) (k : ℕ) :
    Function.Injective (a.retainedIndex S k) :=
  (a.worlds k).injective.comp (keptWorldIndex_injective (S k))

noncomputable def RemainderGeometry.retainedAtlas {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (S : (k : ℕ) → Finset (Fin (q.W k))) (k : ℕ) :
    Atlas p (a.φ k) := subatlas (a.parent k) (a.retainedIndex S k)

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
