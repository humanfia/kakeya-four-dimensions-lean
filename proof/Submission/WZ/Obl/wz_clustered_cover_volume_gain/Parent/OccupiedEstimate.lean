-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.OccupiedEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.PointwiseEstimate

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces

open Finset MeasureTheory
open scoped Classical

noncomputable section

/-- E on any nonempty uniformly dense subfamily keeps the original family count
inside the slab-normalized factor. The selected count only occurs linearly. -/
theorem selected_pointwise_dense_estimate {σ ω : ℝ} (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (P : Finset (Fin n)),
    P.Nonempty → (∀ i ∈ P, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ I ∧
      MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
    (∀ i ∈ P, o (δ ^ η * δ ^ 2) ≤ μ (Y i)) → K δ m n x v → F δ l n x v →
    o (a * δ ^ (ω + ε) * (m⁻¹) ^ 2 * (P.card * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
  classical
  intro ε hε
  obtain ⟨a, ha, η, hη, hbound⟩ := pointwise_dense_estimate hE ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n x v Y P hP hfib hdense hK hF
  have hP0 : 0 < P.card := Finset.card_pos.mpr hP
  have hk0 : (0 : ℝ) < P.card := Nat.cast_pos.mpr hP0
  have hkn : (P.card : ℝ) ≤ n := by exact_mod_cast (show P.card ≤ n by simpa using P.card_le_univ)
  let ii : Fin P.card → Fin n := fun i => (P.equivFin.symm i).1
  have hiP (i : Fin P.card) : ii i ∈ P := (P.equivFin.symm i).2
  have hinj : Function.Injective ii := Subtype.val_injective.comp P.equivFin.symm.injective
  have hl' : 1 ≤ l * n / P.card := by
    apply (le_div_iff₀ hk0).mpr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hh := hbound δ hδ hδ100 m (l * n / P.card) hm hl' P.card
    (x ∘ ii) (v ∘ ii) (Y ∘ ii) hP0 (fun i => hfib (ii i) (hiP i))
    (fun i => hdense (ii i) (hiP i))
    ((show Katz δ m x v from hK).comp_injective hinj)
    ((show Frostman δ l x v from hF).comp_injective hP0 hinj)
  have hbase : m ^ (-(3 / 2 : ℝ)) * (l * n / P.card) * (P.card * δ) =
      m ^ (-(3 / 2 : ℝ)) * l * (n * δ) := by field_simp
  rw [hbase] at hh
  refine hh.trans (measure_mono ?_)
  apply Set.iUnion_subset
  intro i
  exact Set.subset_iUnion Y (ii i)

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces
