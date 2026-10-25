-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AngularSubfamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularPrism

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

/-- The angular filling theorem applies to a selected subfamily, while its
conclusion can be measured in the original union. -/
theorem angular_global_filling_subfamily {n B : ℕ} (hB : 1 ≤ B)
    {a b h lam θ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hlam : 0 < lam) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (c : Fin n → V) (u : Fin n → Fin 3 → V) (H : Fin n → Set V)
    (c₀ : V) (u₀ : Fin 3 → V) (H₀ : Set V) (K : Finset (Fin n)) (hK : K.Nonempty)
    (hu : ∀ i ∈ K, Orthonormal ℝ (u i)) (hHm : ∀ i ∈ K, MeasurableSet (H i))
    (hHU : ∀ i ∈ K, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i ∈ K, ∀ p ∈ H i,
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hH₀m : MeasurableSet H₀) (hH₀ : H₀ ⊆ prism a b c₀ u₀)
    (hdense₀ : O lam * μ (prism a b c₀ u₀) ≤ μ H₀)
    (hcover : H₀ ⊆ ⋃ i ∈ K, H i)
    (hangle : ∀ i ∈ K, θ ≤ pd (u i 0) (u₀ 0) ∧ pd (u i 0) (u₀ 0) ≤ B * θ) :
    O ((lam / 16000) ^ 2 * h ^ 2 * θ * b ^ 2 /
      (52428800000000 * (((128 * B + 1) ^ 4 : ℕ) : ℝ) * (1 + Real.log (b / a)))) ≤
      μ ({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + (B * θ) * b} ∩
        (cTube b c₀ u₀ ∩ ⋃ i, H i)) := by
  classical
  let e := (Fintype.equivFin K).symm
  let g : Fin (Fintype.card K) → Fin n := fun j => (e j).1
  have hg : ∀ j, g j ∈ K := fun j => (e j).2
  have hn : 0 < Fintype.card K := Fintype.card_pos_iff.mpr
    (let ⟨i, hi⟩ := hK; ⟨⟨i, hi⟩⟩)
  have hcover' : H₀ ⊆ ⋃ j, H (g j) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (hcover hp)
    refine mem_iUnion.mpr ⟨e.symm ⟨i, hi⟩, ?_⟩
    simpa only [g, e.apply_symm_apply] using hpi
  have hf := angular_global_filling_of_density hn hB ha hab hb hh hlam hθ hθ1
    (c ∘ g) (u ∘ g) (H ∘ g) c₀ u₀ H₀
    (fun j => hu _ (hg j)) (fun j => hHm _ (hg j)) (fun j => hHU _ (hg j))
    (fun j => hregular _ (hg j)) hu₀ hH₀m hH₀ hdense₀ hcover' (fun j => hangle _ (hg j))
  apply hf.trans
  apply measure_mono
  intro p hp
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp.2.2
  exact ⟨hp.1, hp.2.1, mem_iUnion.mpr ⟨g j, hj⟩⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
