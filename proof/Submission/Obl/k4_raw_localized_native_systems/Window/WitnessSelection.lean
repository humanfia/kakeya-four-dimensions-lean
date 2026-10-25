import Submission.Obl.k4_raw_localized_native_systems.Window.RawAssembly
import Submission.Obl.k4_raw_localized_native_systems.Window.HeavyWitnesses
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set Classical
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

def witnessIndex {J : ℕ} (S : Finset (Fin J)) (e : Fin S.card) : Fin J :=
  (S.equivFin.symm e).val

theorem witnessIndex_mem {J : ℕ} (S : Finset (Fin J)) (e : Fin S.card) : witnessIndex S e ∈ S :=
  (S.equivFin.symm e).property

theorem witnessIndex_injective {J : ℕ} (S : Finset (Fin J)) : Function.Injective (witnessIndex S) := by
  intro e e' h
  apply S.equivFin.symm.injective
  exact Subtype.ext h

/-- Relabel selected full earlier references; analytical masks are kept separate. -/
def selectWitnesses (W : Atlas p k) (S : Finset (Fin W.C)) : Atlas p k where
  T := W.T
  C := S.card
  γ := W.γ ∘ witnessIndex S
  j := W.j ∘ witnessIndex S
  c := W.c ∘ witnessIndex S
  u := W.u ∘ witnessIndex S
  Q := W.Q ∘ witnessIndex S
  R := W.R ∘ witnessIndex S
  A := W.A ∘ witnessIndex S
  F := W.F ∘ witnessIndex S
  lst := fun w o => Finset.univ.filter (fun e => witnessIndex S e ∈ W.lst w o)

def trimmedWitnesses (W : Atlas p k) (S : Finset (Fin W.C))
    (Good : Fin (p.W k) → Set Point) (e : Fin S.card) : Set Point :=
  W.F (witnessIndex S e) ∩ Good (W.γ (witnessIndex S e))

theorem selected_witness_mem_list (W : Atlas p k) (S : Finset (Fin W.C))
    (γ : Fin (p.W k)) (o : Observation) (e : Fin S.card) :
    e ∈ (selectWitnesses W S).lst γ o ↔ witnessIndex S e ∈ W.lst γ o := by
  classical
  change e ∈ Finset.univ.filter (fun e => witnessIndex S e ∈ W.lst γ o) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Retaining earlier witnesses preserves their original observation lists. -/
theorem selected_witness_known (W : Atlas p k) (S : Finset (Fin W.C))
    (hknown : ∀ e q, q ∈ W.F e →
      e ∈ W.lst (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) p.L) q)) :
    ∀ e q, q ∈ (selectWitnesses W S).F e →
      e ∈ (selectWitnesses W S).lst ((selectWitnesses W S).γ e)
        (obs (p.B k ((selectWitnesses W S).γ e)) (δ (p.N k) p.L) q) := by
  intro e q hq
  exact (selected_witness_mem_list W S _ _ e).mpr (hknown _ q hq)

theorem selected_witness_list_card (W : Atlas p k) (S : Finset (Fin W.C))
    (γ : Fin (p.W k)) (o : Observation) :
    ((selectWitnesses W S).lst γ o).card ≤ (W.lst γ o).card := by
  apply Finset.card_le_card_of_injOn (witnessIndex S)
  · intro e he
    exact (selected_witness_mem_list W S γ o e).mp he
  · exact (witnessIndex_injective S).injOn

theorem selected_witness_list_measurable (W : Atlas p k) (S : Finset (Fin W.C))
    (hm : ∀ γ e, MeasurableSet {o | e ∈ W.lst γ o}) :
    ∀ γ e, MeasurableSet {o | e ∈ (selectWitnesses W S).lst γ o} := by
  intro γ e
  have heq : {o | e ∈ (selectWitnesses W S).lst γ o} =
      {o | witnessIndex S e ∈ W.lst γ o} := by
    ext o
    exact selected_witness_mem_list W S γ o e
  rw [heq]
  exact hm γ _

theorem selected_witness_chart (hp : Valid p) {W : Atlas p k} {M D : ℕ}
    {κ κ' r : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ κ')
    (hW : ∀ e, WChart p k W M D κ r e)
    (S : Finset (Fin W.C)) (e : Fin S.card) :
    WChart p k (selectWitnesses W S) M D κ' r e := by
  obtain ⟨ex, he⟩ := hW (witnessIndex S e)
  exact ⟨ex, k4_quadratic_atlas_normalization.chart_mono (hp.scale_ge_one k)
    le_rfl le_rfl hκ hκ' (hp.B_pos k _).le he id⟩

theorem selected_witness_disjoint {W : Atlas p k}
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (S : Finset (Fin W.C)) :
    ∀ e e', e ≠ e' → (selectWitnesses W S).γ e = (selectWitnesses W S).γ e' →
      (selectWitnesses W S).j e = (selectWitnesses W S).j e' →
        Disjoint ((selectWitnesses W S).A e) ((selectWitnesses W S).A e') := by
  intro e e' hne hγ hj
  exact hdisj _ _ (fun h => hne (witnessIndex_injective S h)) hγ hj

/-- A half-heavy earlier witness keeps the true floor at a doubled slack. -/
theorem trimmed_witness_floor {p : Data} (hp : Valid p) {k M D : ℕ}
    {W : Atlas p k} {κ κ' r : ℝ} (hκ : 0 < κ) (hdouble : 2 * κ ≤ κ')
    (hW : ∀ e, WChart p k W M D κ r e)
    (hfloor : ∀ e, ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ wmass W e)
    (Good : Fin (p.W k) → Set Point) (S : Finset (Fin W.C))
    (hheavy : ∀ e ∈ S, activeWitness (selected p k) W.γ W.F Good e)
    (e : Fin S.card) :
    ENNReal.ofReal (p.N k ^ (-p.f r) * |((selectWitnesses W S).Q e).det| /
      ((2 : ℝ) ^ (selectWitnesses W S).T * κ')) ≤
        rawMass (selectWitnesses W S) (trimmedWitnesses W S Good) e := by
  let a := witnessIndex S e
  have hFsub : W.F a ⊆ p.E k (W.γ a) := fun q hq => ((hW a).sel hq).1
  have hhalf := hheavy a (witnessIndex_mem S e)
  change selected p k (W.γ a) (W.F a) ≤
    2 * selected p k (W.γ a) (W.F a ∩ Good (W.γ a)) at hhalf
  rw [selected, Measure.restrict_eq_self _ hFsub,
    Measure.restrict_eq_self _ (inter_subset_left.trans hFsub)] at hhalf
  have hN := hp.scale_pos k
  exact k4_true_forest_own_depth_preparation.restore_chart_floor hκ hdouble
    (by positivity) (by positivity) (hfloor a) hhalf

/-- An earlier label seen outside the common exceptional event is half-heavy. -/
theorem exists_heavy_witness {W : Atlas p k}
    (Good : Fin (p.W k) → Set Point) (w : Fin (p.W k)) {q : Point}
    (hq : q ∈ witnessKeep (selected p k) W.γ W.F Good w)
    (hsource : ∃ e, W.γ e = w ∧ q ∈ W.F e) :
    ∃ e, activeWitness (selected p k) W.γ W.F Good e ∧ W.γ e = w ∧
      q ∈ W.F e ∩ Good w := by
  obtain ⟨e, hew, hqe⟩ := hsource
  have hq' : q ∈ witnessKeep (selected p k) W.γ W.F Good (W.γ e) := hew ▸ hq
  obtain ⟨he, hgood⟩ := witnessKeep_active (selected p k) W.γ W.F Good hq' hqe
  exact ⟨e, he, hew, hqe, hew ▸ hgood.2⟩

end
end Submission.Obl.k4_raw_localized_native_systems.Window
