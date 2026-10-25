import Submission.Obl.k4_raw_critical_segment_forests.ParentAtlas
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.FrozenBridge
import Submission.Obl.k4_raw_localized_native_systems.Window.Witness

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests

noncomputable section

/-- Every original label in a layer has an index in the layer atlas. -/
theorem source_layer_index_surj {p : Data} {k : ℕ} (a : Forest p k)
    {i : ℕ} {b : Fin a.C} (hb : a.lev b = i) :
    ∃ e : Fin (a.layerLabels i).card, a.layerEmb i e = b := by
  classical
  have hmem : b ∈ a.layerLabels i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
  refine ⟨((a.layerLabels i).orderIsoOfFin rfl).symm ⟨b, hmem⟩, ?_⟩
  exact congrArg Subtype.val (((a.layerLabels i).orderIsoOfFin rfl).apply_symm_apply _)

/-- Adjacent actual layers preserve the original parent world, assignment
and entire selected event. No analytical mask enters the forest ancestry. -/
theorem source_layers_ancestry {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C))
    (i : ℕ) (b : Fin (a.layerLabels (i + 1)).card) :
    ∃ e : Fin (a.layerLabels i).card,
      (a.layerAtlas i (ha.j_lt · ·) lst).γ e =
        (a.layerAtlas (i + 1) (ha.j_lt · ·) lst).γ b ∧
      (a.layerAtlas (i + 1) (ha.j_lt · ·) lst).A b ⊆
        (a.layerAtlas i (ha.j_lt · ·) lst).A e ∧
      (a.layerAtlas (i + 1) (ha.j_lt · ·) lst).F b ⊆
        (a.layerAtlas i (ha.j_lt · ·) lst).F e := by
  have hlev := a.layerEmb_lev (i + 1) b
  have hpar := (ha.2.2.2.2.2 (a.layerEmb (i + 1) b)).2.2.2
    (show 0 < a.lev (a.layerEmb (i + 1) b) by omega)
  have hparent : a.lev (a.par (a.layerEmb (i + 1) b)) = i := by omega
  obtain ⟨e, he⟩ := source_layer_index_surj a hparent
  refine ⟨e, ?_, ?_, ?_⟩
  · change a.γ (a.layerEmb i e) = a.γ (a.layerEmb (i + 1) b)
    rw [he]
    exact hpar.2.1
  · change a.A (a.layerEmb (i + 1) b) ⊆ a.A (a.layerEmb i e)
    rw [he]
    exact hpar.2.2.1
  · change a.F (a.layerEmb (i + 1) b) ⊆ a.F (a.layerEmb i e)
    rw [he]
    exact hpar.2.2.2.1

/-- A current family contained in the later full source events has the exact
same-world earlier ancestry used by the analytical omission estimate. -/
theorem current_source_ancestry {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)) (i : ℕ)
    {C : ℕ} (γC : Fin C → Fin (p.W k)) (FC : Fin C → Set Point)
    (hsource : ∀ c, FC c ⊆
      ⋃ b ∈ Finset.univ.filter (fun b =>
        (a.layerAtlas (i + 1) (ha.j_lt · ·) lst).γ b = γC c),
        (a.layerAtlas (i + 1) (ha.j_lt · ·) lst).F b) :
    ∀ c z, z ∈ FC c → ∃ e : Fin (a.layerLabels i).card,
      (a.layerAtlas i (ha.j_lt · ·) lst).γ e = γC c ∧
      z ∈ (a.layerAtlas i (ha.j_lt · ·) lst).F e := by
  intro c z hz
  have hzsource := hsource c hz
  simp only [Set.mem_iUnion] at hzsource
  obtain ⟨b, hb, hzb⟩ := hzsource
  have hγ := (Finset.mem_filter.mp hb).2
  obtain ⟨e, heγ, -, heF⟩ := source_layers_ancestry a ha lst i b
  exact ⟨e, heγ.trans hγ, heF hzb⟩

/-- The true original chart of a layer is a raw witness chart with its
actual earlier depth. -/
theorem source_layer_wchart {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C))
    {i : ℕ} (hi : i < m) (e : Fin (a.layerLabels i).card) :
    Window.WChart p k (a.layerAtlas i (ha.j_lt · ·) lst) M D a.κ (r i) e := by
  exact ⟨_, (a.layer_trueDepth ha hi lst).2.2.1 e⟩

/-- The complete original layer events retain their actual saturation floor. -/
theorem source_layer_floor {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C))
    {i : ℕ} (hi : i < m) (e : Fin (a.layerLabels i).card) :
    ENNReal.ofReal (p.N k ^ (-p.f (r i)) *
      |((a.layerAtlas i (ha.j_lt · ·) lst).Q e).det| /
      ((2 : ℝ) ^ (a.layerAtlas i (ha.j_lt · ·) lst).T * a.κ)) ≤
      Window.wmass (a.layerAtlas i (ha.j_lt · ·) lst) e := by
  exact k4_native_calibrated_homogeneous_remainder.chart_extra
    ((a.layer_trueDepth ha hi lst).2.2.1 e)

end
end Submission.Obl.k4_raw_localized_native_systems
