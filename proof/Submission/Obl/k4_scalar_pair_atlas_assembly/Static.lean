import Submission.Obl.k4_scalar_pair_atlas_assembly.SourceBlocks
import Submission.Obl.k4_scalar_pair_atlas_assembly.Candidate
import Submission.Obl.k4_scalar_pair_atlas_assembly.Format
import Submission.Obl.k4_scalar_pair_atlas_assembly.Lists
set_option autoImplicit false
namespace Submission.Obl.k4_scalar_pair_atlas_assembly.Static
open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
noncomputable section

def assigned {Wc Bc Fc n m : ℕ} {α : Type}
    (g : Fin m → Fin Wc) (b : Fin m → Fin Bc) (code : Fin n → Fin m)
    (j : Fin n → Fin Fc) (A : Fin n → Set α)
    (source : Fin Wc → Fin Bc → Fin Fc) (o : Fin m) : Set α :=
  {l | ∃ i, code i = o ∧ j i = source (g o) (b o) ∧ l ∈ A i}

def selected {Wc T₀ T n m : ℕ} {α : Type}
    (g : Fin m → Fin Wc) (b : Fin m → Fin (2 ^ T)) (code : Fin n → Fin m)
    (j : Fin n → Fin (2 ^ T₀)) (A : Fin n → Set α) (C : Fin n → Set (α × ℝ))
    (R : Fin n → Finset (Fin m)) (source : Fin Wc → Fin (2 ^ T) → Fin (2 ^ T₀))
    (o : Fin m) : Set (α × ℝ) :=
  {q | q.1 ∈ assigned g b code j A source o ∧ q.2 ∈ halfI T (b o) ∧
    ∃ i, o ∈ R i ∧ q ∈ C i}

lemma measurable_assigned {Wc Bc Fc n m : ℕ} {α : Type} [MeasurableSpace α]
    (g : Fin m → Fin Wc) (b : Fin m → Fin Bc) (code : Fin n → Fin m)
    (j : Fin n → Fin Fc) (A : Fin n → Set α)
    (source : Fin Wc → Fin Bc → Fin Fc) (hA : ∀ i, MeasurableSet (A i))
    (o : Fin m) : MeasurableSet (assigned g b code j A source o) := by
  unfold assigned
  simp only [ofPred_exists, ofPred_and]
  apply MeasurableSet.iUnion fun i => ?_
  measurability

lemma measurable_selected {Wc T₀ T n m : ℕ} {α : Type} [MeasurableSpace α]
    (g : Fin m → Fin Wc) (b : Fin m → Fin (2 ^ T)) (code : Fin n → Fin m)
    (j : Fin n → Fin (2 ^ T₀)) (A : Fin n → Set α) (C : Fin n → Set (α × ℝ))
    (R : Fin n → Finset (Fin m)) (source : Fin Wc → Fin (2 ^ T) → Fin (2 ^ T₀))
    (hA : ∀ i, MeasurableSet (A i)) (hC : ∀ i, MeasurableSet (C i))
    (o : Fin m) : MeasurableSet (selected g b code j A C R source o) := by
  have ha : MeasurableSet {q : α × ℝ | q.1 ∈ assigned g b code j A source o} :=
    (measurable_assigned g b code j A source hA o).preimage measurable_fst
  have ht : MeasurableSet {q : α × ℝ | q.2 ∈ halfI T (b o)} :=
    (measurable_halfI T (b o)).preimage measurable_snd
  have hc : MeasurableSet {q | ∃ i, o ∈ R i ∧ q ∈ C i} := by
    simp only [ofPred_exists, ofPred_and]
    apply MeasurableSet.iUnion fun i => ?_
    exact (by simp : MeasurableSet {q : α × ℝ | o ∈ R i}).inter (hC i)
  exact ha.inter (ht.inter hc)

lemma assigned_disjoint {Wc Bc Fc n m : ℕ} {α : Type}
    (γ : Fin n → Fin Wc) (g : Fin m → Fin Wc) (b : Fin m → Fin Bc)
    (code : Fin n → Fin m) (j : Fin n → Fin Fc) (A : Fin n → Set α)
    (source : Fin Wc → Fin Bc → Fin Fc)
    (hcode : ∀ i, g (code i) = γ i)
    (hdis : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    (o o' : Fin m) (hne : o ≠ o') (hw : g o = g o') (hb : b o = b o') :
    Disjoint (assigned g b code j A source o) (assigned g b code j A source o') := by
  apply disjoint_left.mpr
  rintro l ⟨i, hi, hji, hAi⟩ ⟨i', hi', hji', hAi'⟩
  have hii : i ≠ i' := fun heq => hne (hi.symm.trans (heq ▸ hi'))
  exact disjoint_left.mp (hdis i i' hii (by rw [← hcode i, ← hcode i', hi, hi', hw])
    (by rw [hji, hji', hw, hb])) hAi hAi'

lemma format_assigned {Wc Bc Fc n m d : ℕ} {H : ℝ}
    (g : Fin m → Fin Wc) (b : Fin m → Fin Bc) (code : Fin n → Fin m)
    (j : Fin n → Fin Fc) (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (source : Fin Wc → Fin Bc → Fin Fc) (hH : 0 ≤ H)
    (hA : ∀ i z, Format 5 H d {a | (z, a) ∈ A i}) (o : Fin m) (z : ℕ) :
    Format 5 (n * H) d {a | (z, a) ∈ assigned g b code j A source o} := by
  have h := format_selected_union hH (fun i => {a | (z, a) ∈ A i})
    (fun i => hA i z) (fun i => code i = o ∧ j i = source (g o) (b o))
  apply k4_scalar_conditional_crop_worlds.Format.congr h
  ext a
  simp only [assigned, mem_ofPred_eq, and_assoc]

lemma format_halfI {d T : ℕ} (hd : 1 ≤ d) (b : Fin (2 ^ T)) :
    Format 6 4 d {a : Fin 6 → ℝ | a 5 ∈ halfI T b} := by
  have h := k4_scalar_conditional_crop_worlds.Format.coord_timeCell
    (5 : Fin 6) hd (Nat.two_pow_pos T) b
  apply k4_scalar_conditional_crop_worlds.Format.congr h
  ext a
  simp [halfI, width, div_eq_mul_inv]

lemma format_selected {Wc T₀ T n m d : ℕ} {H : ℝ}
    (g : Fin m → Fin Wc) (b : Fin m → Fin (2 ^ T)) (code : Fin n → Fin m)
    (j : Fin n → Fin (2 ^ T₀)) (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (R : Fin n → Finset (Fin m))
    (source : Fin Wc → Fin (2 ^ T) → Fin (2 ^ T₀)) (hH : 0 ≤ H) (hd : 1 ≤ d)
    (hA : ∀ i z, Format 5 H d {a | (z, a) ∈ A i})
    (hC : ∀ i z, Format 6 H d
      {a | ((z, fun e : Fin 5 => a e.castSucc), a 5) ∈ C i}) (o : Fin m) (z : ℕ) :
    Format 6 (2 * n * H + 5) d
      {a | ((z, fun e : Fin 5 => a e.castSucc), a 5) ∈ selected g b code j A C R source o} := by
  have hn : (0 : ℝ) ≤ n * H := mul_nonneg (Nat.cast_nonneg _) hH
  have hAs := format_assigned g b code j A source hH hA o z
  have hAs' := k4_scalar_conditional_crop_worlds.Format.mono hAs
    (show n * H ≤ n * H + 1 by linarith) le_rfl
  have hAl := format_coord_preimage (show 1 ≤ n * H + 1 by linarith) hAs'
    (fun i : Fin 5 => i.castSucc)
  have hCu := format_selected_union hH
    (fun i => {a : Fin 6 → ℝ | ((z, fun e : Fin 5 => a e.castSucc), a 5) ∈ C i})
    (fun i => hC i z) (fun i => o ∈ R i)
  have htotal := k4_scalar_conditional_crop_worlds.Format.inter hAl
    (k4_scalar_conditional_crop_worlds.Format.inter (format_halfI hd (b o)) hCu)
  have hbudget : n * H + 1 + (4 + n * H) = 2 * n * H + 5 := by ring
  rw [hbudget] at htotal
  apply k4_scalar_conditional_crop_worlds.Format.congr htotal
  ext a
  simp only [selected, mem_inter_iff, mem_ofPred_eq]

end
end Submission.Obl.k4_scalar_pair_atlas_assembly.Static
