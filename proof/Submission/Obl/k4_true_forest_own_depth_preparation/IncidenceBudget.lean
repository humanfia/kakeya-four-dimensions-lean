import Submission.Obl.k4_true_forest_own_depth_preparation.Model
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set

/-- Incidences inside distinct assigned time cells spend their original
parent's mass only once. Closed endpoints are null for the time law. -/
theorem nested_incidence_budget {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) (T : ℕ) (j : ι → ℕ) (A : ι → Set α)
    (F : ι → Set (α × ℝ)) (H : Set (α × ℝ))
    (hF : ∀ b, MeasurableSet (F b))
    (hdisj : ∀ b b', b ≠ b' → j b = j b' → Disjoint (A b) (A b'))
    (hsel : ∀ b p, p ∈ F b → p.1 ∈ A b ∧
      p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T) (((j b : ℝ) + 1) / (2 : ℝ) ^ T))
    (hsub : ∀ b, F b ⊆ H) :
    (∑ b, (ν.prod volume) (F b)) ≤ (ν.prod volume) H := by
  classical
  let G : ι → Set (α × ℝ) := fun b =>
    F b ∩ {p | p.2 < ((j b : ℝ) + 1) / (2 : ℝ) ^ T}
  have hG (b) : MeasurableSet (G b) :=
    (hF b).inter (measurableSet_lt measurable_snd measurable_const)
  have hm (b) : (ν.prod volume) (G b) = (ν.prod volume) (F b) :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.measure_trim_right ν (F b) _
      (fun p hp => (hsel b p hp).2.2)
  have hpack (b) : G b ⊆ A b ×ˢ Ico ((j b : ℝ) / (2 : ℝ) ^ T)
      (((j b : ℝ) + 1) / (2 : ℝ) ^ T) := by
    intro p hp
    exact ⟨(hsel b p hp.1).1, (hsel b p hp.1).2.1, hp.2⟩
  have hd : Pairwise (fun b b' => Disjoint (G b) (G b')) := by
    intro b b' hne
    exact Disjoint.mono (hpack b) (hpack b')
      (Submission.Obl.k4_quadratic_finite_greedy_cover.halfOpen_packets_disjoint
        A j ((2 : ℝ) ^ T) (by positivity) hdisj hne)
  calc
    _ = ∑ b, (ν.prod volume) (G b) := by simp_rw [hm]
    _ = (ν.prod volume) (⋃ b, G b) := by
      rw [measure_iUnion hd hG, tsum_fintype]
    _ ≤ (ν.prod volume) H := measure_mono (iUnion_subset fun b => inter_subset_left.trans (hsub b))

/-- The original weighted masses in a genuine finite incidence forest obey
the child budget required by subsequent finite selection. -/
theorem forest_child_budget {α : Type*} [MeasurableSpace α] {C W : ℕ}
    (ν : Fin W → Measure α) (ω : Fin W → ENNReal)
    (T : ℕ → ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C)
    (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set α) (F : Fin C → Set (α × ℝ))
    (hFm : ∀ b, MeasurableSet (F b))
    (hdisj : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b'))
    (hsel : ∀ b p, p ∈ F b → p.1 ∈ A b ∧
      p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)))
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b ∧
      γ (par b) = γ b ∧ F b ⊆ F (par b)) (a : Fin C) :
    (∑ b, if 0 < lev b ∧ par b = a then
      ω (γ b) * ((ν (γ b)).prod volume) (F b) else 0) ≤
        ω (γ a) * ((ν (γ a)).prod volume) (F a) := by
  classical
  let I := {b : Fin C // 0 < lev b ∧ par b = a}
  have hγ (b : I) : γ b.val = γ a := by
    have := (hpar b.val b.property.1).2.1
    simpa only [b.property.2] using this.symm
  have hlev (b : I) : lev b.val = lev a + 1 := by
    have := (hpar b.val b.property.1).1
    simpa only [b.property.2] using this.symm
  have hb := nested_incidence_budget (ν (γ a)) (T (lev a + 1))
    (fun b : I => j b.val) (fun b => A b.val) (fun b => F b.val) (F a)
    (fun b => hFm b.val)
    (fun b b' hne hj => hdisj b.val b'.val (fun h => hne (Subtype.ext h))
      ((hlev b).trans (hlev b').symm) ((hγ b).trans (hγ b').symm) hj)
    (fun b p hp => by simpa only [hlev b] using hsel b.val p hp)
    (fun b => by
      have := (hpar b.val b.property.1).2.2
      simpa only [b.property.2] using this)
  have hs : (∑ b, if 0 < lev b ∧ par b = a then
      ω (γ b) * ((ν (γ b)).prod volume) (F b) else 0) =
      ∑ b : I, ω (γ b.val) * ((ν (γ b.val)).prod volume) (F b.val) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hs]
  simp_rw [hγ, ← Finset.mul_sum]
  exact mul_le_mul_right hb _

end Submission.Obl.k4_true_forest_own_depth_preparation
