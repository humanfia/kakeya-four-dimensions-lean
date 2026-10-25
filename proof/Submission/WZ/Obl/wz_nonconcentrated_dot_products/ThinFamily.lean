-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.ThinFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.RadialGain
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.GoodRow

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Thin tubes yield a large projection in one fiber of any sufficiently
dense family. The exceptional-pair loss is subtracted from the density. -/
theorem thin_family_projection_gain {δ K c d γ : ℝ} (F G₁ G₂ : Finset Plane)
    (T : Plane → Plane → Finset Plane) (R : Plane → Plane → Prop)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hK : 1 ≤ K) (hdc : 0 < d - c)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hF : ClosedFiniteFrostman δ K F)
    (hFne : F.Nonempty) (hG₁ne : G₁.Nonempty) (hG₂ne : G₂.Nonempty)
    (hsep : ∀ b ∈ G₁, ∀ x ∈ G₂, 1 / 4 ≤ ‖b - x‖)
    (hfar : ∀ b ∈ G₁, ∀ x ∈ G₂, ‖b - x‖ ≤ 8)
    (hT : ∀ b ∈ G₁, ∀ x ∈ G₂, T b x ⊆ F)
    (hthin : ∀ b ∈ G₁, ∀ (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
      ((G₂.filter (fun x => R b x ∧ |inner ℝ (x - b) u| < r)).card : ℝ) ≤ K * r * (G₂.card : ℝ))
    (hbad : (((G₁ ×ˢ G₂).filter (fun p => ¬R p.1 p.2)).card : ℝ) ≤
      c * (G₁.card : ℝ) * (G₂.card : ℝ))
    (hdensity : d * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ) ≤
      ∑ b ∈ G₁, ∑ x ∈ G₂, ((T b x).card : ℝ)) :
    ∃ b ∈ G₁, ∃ x ∈ G₂, R b x ∧ ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun a => inner ℝ a (b - x)) '' (↑(T b x) : Set Plane)) cc →
        (d - c) ^ 2 ≤ (8 * (17 * K / (d - c)) ^ 2 * energyConstant γ * (4 * δ) ^ γ) * (m : ℝ) := by
  classical
  obtain ⟨b₀, hb₀⟩ := hG₁ne
  letI : Nonempty G₁ := ⟨⟨b₀, hb₀⟩⟩
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hFne
  have hG₂pos : (0 : ℝ) < G₂.card := by exact_mod_cast Finset.card_pos.mpr hG₂ne
  have hsums : (∑ b : G₁, ∑ x : G₂, ((T b x).card : ℝ)) =
      ∑ b ∈ G₁, ∑ x ∈ G₂, ((T b x).card : ℝ) := by
    rw [Finset.sum_coe_sort G₁ (fun b => ∑ x : G₂, ((T b x).card : ℝ))]
    apply Finset.sum_congr rfl
    intro b hb
    exact Finset.sum_coe_sort G₂ (fun x => ((T b x).card : ℝ))
  have hbad' : ((Finset.univ.filter (fun p : G₁ × G₂ => ¬R p.1 p.2)).card : ℝ) ≤
      c * (Fintype.card G₁ : ℝ) * (Fintype.card G₂ : ℝ) := by
    have heq : (Finset.univ.filter (fun p : G₁ × G₂ => ¬R p.1 p.2)).card =
        ((G₁ ×ˢ G₂).filter (fun p => ¬R p.1 p.2)).card := by
      convert indexed_pair_filter_card G₁ G₂ (fun p => ¬R p.1 p.2) using 1 <;>
        congr 1 <;> ext p <;> simp
    rw [heq, Fintype.card_coe, Fintype.card_coe]
    exact hbad
  have hden' : d * (Fintype.card G₁ : ℝ) * (Fintype.card G₂ : ℝ) * (F.card : ℝ) ≤
      ∑ b : G₁, ∑ x : G₂, ((T b x).card : ℝ) := by
    rw [Fintype.card_coe, Fintype.card_coe, hsums]
    exact hdensity
  obtain ⟨b, hrow⟩ := exists_good_row (fun b : G₁ => fun x : G₂ => ((T b x).card : ℝ))
    (fun b : G₁ => fun x : G₂ => R b x) (M := (F.card : ℝ)) (Nat.cast_nonneg _)
    (fun b x => ⟨Nat.cast_nonneg _, by exact_mod_cast Finset.card_le_card (hT b b.property x x.property)⟩)
    hbad' hden'
  let E : Finset Plane := G₂.filter (fun x => R b x)
  have hEsub : E ⊆ G₂ := Finset.filter_subset _ _
  have hEcap : (E.card : ℝ) ≤ (G₂.card : ℝ) := by exact_mod_cast Finset.card_le_card hEsub
  have hsumE : (∑ x : E, ((T b x).card : ℝ)) =
      ∑ x : G₂, if R b x then ((T b x).card : ℝ) else 0 := by
    rw [Finset.sum_coe_sort E (fun x => ((T b x).card : ℝ)),
      Finset.sum_coe_sort G₂ (fun x => if R b x then ((T b x).card : ℝ) else 0)]
    exact Finset.sum_filter _ _
  have hrowE : (d - c) * (G₂.card : ℝ) * (F.card : ℝ) ≤ ∑ x : E, ((T b x).card : ℝ) := by
    rw [hsumE]
    simpa only [Fintype.card_coe] using hrow
  have hmass_upper : (∑ x : E, ((T b x).card : ℝ)) ≤ (E.card : ℝ) * (F.card : ℝ) := by
    calc (∑ x : E, ((T b x).card : ℝ)) ≤ ∑ _x : E, (F.card : ℝ) := by
          apply Finset.sum_le_sum
          intro x hx
          exact_mod_cast Finset.card_le_card (hT b b.property x (hEsub x.property))
      _ = _ := by simp
  have hret : (d - c) * (G₂.card : ℝ) ≤ (E.card : ℝ) :=
    (mul_le_mul_iff_left₀ hFpos).mp (hrowE.trans hmass_upper)
  have hdc1 : d - c ≤ 1 := by
    apply (mul_le_mul_iff_left₀ hG₂pos).mp
    simpa only [one_mul] using hret.trans hEcap
  have hdenseE : (d - c) * (E.card : ℝ) * (F.card : ℝ) ≤ ∑ x : E, ((T b x).card : ℝ) := by
    calc (d - c) * (E.card : ℝ) * (F.card : ℝ) ≤
          (d - c) * (G₂.card : ℝ) * (F.card : ℝ) := by gcongr
      _ ≤ _ := hrowE
  have hneT : ∃ x : E, (T b x).Nonempty := by
    have hpos : 0 < ∑ x : E, ((T b x).card : ℝ) :=
      (by positivity : 0 < (d - c) * (G₂.card : ℝ) * (F.card : ℝ)).trans_le hrowE
    obtain ⟨x, hx, hcard⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun x (_hx : x ∈ (Finset.univ : Finset E)) => Nat.cast_nonneg (α := ℝ) (T b x).card)).mp hpos
    exact ⟨x, Finset.card_pos.mp (by exact_mod_cast hcard)⟩
  obtain ⟨x, hx⟩ := thin_radial_projection_gain F E G₂ b (fun x => T b x)
    hδ hδ1 hK hdc hdc1 hdc hγ hγ1 hF
    (fun x hx => hsep b b.property x (hEsub hx))
    (fun x hx => hfar b b.property x (hEsub hx)) hret
    (by
      intro u r hu hr
      simpa only [E, Finset.filter_filter] using hthin b b.property u r hu hr)
    (fun x => hT b b.property x (hEsub x.property)) hneT hdenseE
  exact ⟨b, b.property, x, hEsub x.property, (Finset.mem_filter.mp x.property).2, hx⟩

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
