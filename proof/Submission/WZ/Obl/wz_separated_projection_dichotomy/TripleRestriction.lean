-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TripleRestriction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleRefinement

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem card_restrict_of_uniform_fibers {X Y : Type*} (H : Finset X) (T : Finset Y)
    (f : X → Y) {t : ℝ}
    (hsupport : ∀ y ∈ T, ∃ x ∈ H, f x = y)
    (huniform : ∀ x ∈ H, t ≤ ((H.filter (fun z => f z = f x)).card : ℝ)) :
    t * (T.card : ℝ) ≤ ((H.filter (fun x => f x ∈ T)).card : ℝ) := by
  classical
  let R := H.filter (fun x => f x ∈ T)
  have hcard := Finset.card_eq_sum_card_fiberwise (s := R) (t := T) (f := f)
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have heq : ∀ y ∈ T, R.filter (fun x => f x = y) = H.filter (fun x => f x = y) := by
    intro y hy
    ext x
    simp only [R, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hy⟩, h.2⟩⟩
  have hcard' : (R.card : ℝ) = ∑ y ∈ T, ((H.filter (fun x => f x = y)).card : ℝ) := by
    rw [hcard, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [heq y hy]
  change t * (T.card : ℝ) ≤ (R.card : ℝ)
  rw [hcard']
  calc t * (T.card : ℝ) = ∑ _y ∈ T, t := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hsupport y hy
      simpa only [hxy] using huniform x hx

noncomputable def restrictSecond (H : Finset Triple) (G : Finset Plane) : Finset Triple := by
  classical
  exact H.filter (fun p => p.2.1 ∈ G)

noncomputable def restrictThird (H : Finset Triple) (U : Finset Plane) : Finset Triple := by
  classical
  exact H.filter (fun p => p.2.2 ∈ U)

theorem TripleUniform.restrict_second_density {d : ℝ} {F G U G' : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (hG' : G' ⊆ G)
    (hsupport : ∀ x ∈ G, ∃ a b, (a, x, b) ∈ H) :
    d * (F.card : ℝ) * (G'.card : ℝ) * (U.card : ℝ) ≤ ((restrictSecond H G').card : ℝ) := by
  classical
  have hc := card_restrict_of_uniform_fibers H G' (fun p : Triple => p.2.1)
    (t := d * ((F.card : ℝ) * U.card)) (by
      intro x hx
      obtain ⟨a, b, hp⟩ := hsupport x (hG' hx)
      exact ⟨(a, x, b), hp, rfl⟩) (by
      intro p hp
      convert h.row_second p hp using 1 <;> congr 2 <;> ext z <;> simp)
  have heq : ((restrictSecond H G').card : ℝ) =
      ((H.filter (fun p => p.2.1 ∈ G')).card : ℝ) := by
    congr 2
  rw [heq]
  convert hc using 1 <;> first | ring | (congr 2 <;> ext p <;> simp)

theorem TripleUniform.restrict_third_density {d : ℝ} {F G U U' : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (hU' : U' ⊆ U)
    (hsupport : ∀ b ∈ U, ∃ a x, (a, x, b) ∈ H) :
    d * (F.card : ℝ) * (G.card : ℝ) * (U'.card : ℝ) ≤ ((restrictThird H U').card : ℝ) := by
  classical
  have hc := card_restrict_of_uniform_fibers H U' (fun p : Triple => p.2.2)
    (t := d * ((F.card : ℝ) * G.card)) (by
      intro b hb
      obtain ⟨a, x, hp⟩ := hsupport b (hU' hb)
      exact ⟨(a, x, b), hp, rfl⟩) (by
      intro p hp
      convert h.row_third p hp using 1 <;> congr 2 <;> ext z <;> simp)
  have heq : ((restrictThird H U').card : ℝ) =
      ((H.filter (fun p => p.2.2 ∈ U')).card : ℝ) := by
    congr 2
  rw [heq]
  convert hc using 1 <;> first | ring | (congr 2 <;> ext p <;> simp)

theorem restrictSecond_contained {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (G' : Finset Plane) :
    restrictSecond H G' ⊆ F ×ˢ (G' ×ˢ U) := by
  classical
  intro p hp
  obtain ⟨hpH, hpG⟩ := Finset.mem_filter.mp hp
  have h := Finset.mem_product.mp (hH hpH)
  exact Finset.mem_product.mpr ⟨h.1, Finset.mem_product.mpr ⟨hpG, (Finset.mem_product.mp h.2).2⟩⟩

theorem restrictThird_contained {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (U' : Finset Plane) :
    restrictThird H U' ⊆ F ×ˢ (G ×ˢ U') := by
  classical
  intro p hp
  obtain ⟨hpH, hpU⟩ := Finset.mem_filter.mp hp
  have h := Finset.mem_product.mp (hH hpH)
  exact Finset.mem_product.mpr ⟨h.1, Finset.mem_product.mpr ⟨(Finset.mem_product.mp h.2).1, hpU⟩⟩

theorem restrictSecond_subset (H : Finset Triple) (G : Finset Plane) : restrictSecond H G ⊆ H :=
  Finset.filter_subset _ _

theorem restrictThird_subset (H : Finset Triple) (U : Finset Plane) : restrictThird H U ⊆ H :=
  Finset.filter_subset _ _

theorem restrictSecond_nonempty {H : Finset Triple} {G G' : Finset Plane}
    (hG' : G' ⊆ G) (hne : G'.Nonempty)
    (hsupport : ∀ x ∈ G, ∃ a b, (a, x, b) ∈ H) : (restrictSecond H G').Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨a, b, hp⟩ := hsupport x (hG' hx)
  exact ⟨(a, x, b), Finset.mem_filter.mpr ⟨hp, hx⟩⟩

theorem restrictThird_nonempty {H : Finset Triple} {U U' : Finset Plane}
    (hU' : U' ⊆ U) (hne : U'.Nonempty)
    (hsupport : ∀ b ∈ U, ∃ a x, (a, x, b) ∈ H) : (restrictThird H U').Nonempty := by
  obtain ⟨b, hb⟩ := hne
  obtain ⟨a, x, hp⟩ := hsupport b (hU' hb)
  exact ⟨(a, x, b), Finset.mem_filter.mpr ⟨hp, hb⟩⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
