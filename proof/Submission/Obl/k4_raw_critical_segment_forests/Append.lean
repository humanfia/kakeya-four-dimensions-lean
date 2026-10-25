import Submission.Obl.k4_raw_critical_segment_forests.AtlasDepth

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Append one terminal atlas to a prefix forest. The parent map points back
to actual prefix labels; no parent is duplicated. -/
abbrev Forest.append {p : Data} {k : ℕ} (a : Forest p k) (b : Atlas p k)
    (m : ℕ) (parent : Fin b.C → Fin a.C) : Forest p k where
  κ := a.κ
  T i := if i = m then b.T else a.T i
  C := a.C + b.C
  lev := Fin.addCases a.lev (fun _ => m)
  par := Fin.addCases (fun i => Fin.castAdd b.C (a.par i))
    (fun j => Fin.castAdd b.C (parent j))
  γ := Fin.addCases a.γ b.γ
  j := Fin.addCases a.j (fun j => (b.j j : ℕ))
  c := Fin.addCases a.c b.c
  u := Fin.addCases a.u b.u
  Q := Fin.addCases a.Q b.Q
  R := Fin.addCases a.R b.R
  A := Fin.addCases a.A b.A
  F := Fin.addCases a.F b.F

lemma append_layer_mass {p : Data} {k : ℕ} (a : Forest p k) (b : Atlas p k)
    (m i : ℕ) (parent : Fin b.C → Fin a.C) :
    (∑ z, if (a.append b m parent).lev z = i then
      ENNReal.ofReal (p.ω k ((a.append b m parent).γ z)) *
        priorMass p k ((a.append b m parent).γ z) ((a.append b m parent).F z) else 0) =
      (∑ z, if a.lev z = i then
        ENNReal.ofReal (p.ω k (a.γ z)) * priorMass p k (a.γ z) (a.F z) else 0) +
      (if m = i then ∑ z,
        ENNReal.ofReal (p.ω k (b.γ z)) * priorMass p k (b.γ z) (b.F z) else 0) := by
  classical
  dsimp only [Forest.append]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  by_cases h : m = i <;> simp [h]

/-- The finite geometric append step. The genuine floor of the new layer is
that of a terminal atlas at the newly coarsened endpoint. -/
theorem append_core {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    {a : Forest p k} {b : Atlas p k} (parent : Fin b.C → Fin a.C)
    (hm : 0 < m) (ha : a.Core M D m r)
    (hb : TrueDepth b M D a.κ (r m))
    (hC : ((a.C + b.C : ℕ) : ℝ) ≤ p.N k ^ M)
    (hlev : ∀ z, a.lev (parent z) + 1 = m)
    (hγ : ∀ z, a.γ (parent z) = b.γ z)
    (hA : ∀ z, b.A z ⊆ a.A (parent z))
    (hF : ∀ z, b.F z ⊆ a.F (parent z))
    (hlo : ∀ z, (a.j (parent z) : ℝ) / (2 : ℝ) ^ a.T (a.lev (parent z)) ≤
      (b.j z : ℝ) / (2 : ℝ) ^ b.T)
    (hhi : ∀ z, ((b.j z : ℝ) + 1) / (2 : ℝ) ^ b.T ≤
      ((a.j (parent z) : ℝ) + 1) / (2 : ℝ) ^ a.T (a.lev (parent z))) :
    (a.append b m parent).Core M D (m + 1) r := by
  classical
  obtain ⟨hκ, hKκ, hCa, hmass, hsep, hchart⟩ := ha
  obtain ⟨hCb, hsepb, hchartb, hmassb⟩ := hb
  have hlt (z : Fin a.C) : a.lev z < m := (hchart z).1
  have hne (z : Fin a.C) : a.lev z ≠ m := (hlt z).ne
  refine ⟨hκ, hKκ, hC, ?_, ?_, ?_⟩
  · intro i hi
    rw [append_layer_mass]
    by_cases him : i < m
    · exact (hmass i him).trans le_self_add
    · have him' : i = m := by omega
      subst i
      simpa only [Forest.append, hne, ↓reduceIte, Finset.sum_const_zero, zero_add] using hmassb
  · intro x
    refine Fin.addCases ?_ ?_ x
    · intro x y
      refine Fin.addCases ?_ ?_ y
      · intro y hxy hxyLev hxyγ hxyj
        simp only [Forest.append, Fin.addCases_left, Fin.addCases_right]
          at hxyLev hxyγ hxyj ⊢
        exact hsep x y (fun he => hxy (congrArg (Fin.castAdd b.C) he)) hxyLev hxyγ hxyj
      · intro y hxy hxyLev hxyγ hxyj
        simp only [Forest.append, Fin.addCases_left, Fin.addCases_right]
          at hxyLev hxyγ hxyj ⊢
        exact False.elim ((hne x) hxyLev)
    · intro x y
      refine Fin.addCases ?_ ?_ y
      · intro y hxy hxyLev hxyγ hxyj
        simp only [Forest.append, Fin.addCases_left, Fin.addCases_right]
          at hxyLev hxyγ hxyj ⊢
        exact False.elim ((hne y) hxyLev.symm)
      · intro y hxy hxyLev hxyγ hxyj
        simp only [Forest.append, Fin.addCases_left, Fin.addCases_right]
          at hxyLev hxyγ hxyj ⊢
        apply hsepb x y (fun he => hxy (congrArg (Fin.natAdd a.C) he)) hxyγ
        exact Fin.ext hxyj
  · intro z
    refine Fin.addCases ?_ ?_ z
    · intro z
      have hz := hchart z
      have hpz := hchart (a.par z)
      simpa only [Forest.append, Fin.addCases_left, if_neg (hne z), if_neg (hne (a.par z))]
        using And.intro (show a.lev z < m + 1 by omega) hz.2
    · intro z
      have hpz := hchart (parent z)
      refine ⟨by simp only [Forest.append, Fin.addCases_right]; omega, ?_, ?_, ?_⟩
      · simpa only [Forest.append, Fin.addCases_right, if_pos rfl, ite_true] using (b.j z).isLt
      · simpa only [Forest.append, Fin.addCases_right, if_pos rfl, ite_true]
          using hchartb z
      · intro hz
        simpa only [Forest.append, Fin.addCases_right, Fin.addCases_left,
          if_pos rfl, ite_true, if_neg (hne (parent z))] using
          And.intro (hlev z) (And.intro (hγ z) (And.intro (hA z)
            (And.intro (hF z) (And.intro (hlo z) (hhi z)))))

end
end Submission.Obl.k4_raw_critical_segment_forests
