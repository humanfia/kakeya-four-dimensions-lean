-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.LensDescent.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactOrder
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensLocation
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensNesting

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Any crossing on the short window equals one of two prescribed
crossings. This allows a lens constructed from contacts to be identified
with the unique lens belonging to that curve pair. -/
theorem crossing_eq_one_of_two {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {l u a b t v : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (ht : t ∈ Icc l u) (hab : a < b)
    (hv : |v| < dist (q i) (q j) / 480)
    (heqa : g i a - g j a = v) (heqb : g i b - g j b = v)
    (heqt : g i t - g j t = v) : t = a ∨ t = b := by
  have hmem {x : ℝ} (hx : x ∈ Icc l u) : x ∈ Icc (-1 : ℝ) 1 :=
    ⟨hl.trans hx.1, hx.2.trans hu⟩
  by_cases hta : t = a
  · exact Or.inl hta
  by_cases htb : t = b
  · exact Or.inr htb
  exfalso
  rcases lt_or_gt_of_ne hta with hta' | hat
  · exact no_three_close_level_crossings hg hjet i j hv (hmem ht) (hmem hb)
      hta' hab (by linarith [ht.1, hb.2]) heqt heqa heqb
  · rcases lt_or_gt_of_ne htb with htb' | hbt
    · exact no_three_close_level_crossings hg hjet i j hv (hmem ha) (hmem hb)
        hat htb' (by linarith [ha.1, hb.2]) heqa heqt heqb
    · exact no_three_close_level_crossings hg hjet i j hv (hmem ha) (hmem ht)
        hab hbt (by linarith [ha.1, ht.2]) heqa heqb heqt

/-- A contact cycle whose common-neighbor intervals have the same
orientation produces a shorter opposite-color lens, provided the parent
pair has two crossings in the ambient window. Unlike the earlier local
contraction lemma, no contact is assumed to lie in the parent lens. -/
theorem exists_child_lens_of_parent_lens {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j m : Fin n) {l u L U x₀ x₁ y₁ y₀ γ M δ η : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (hL : L ∈ Icc l u) (hU : U ∈ Icc l u) (hLU : L < U)
    (hik : 0 < dist (q i) (q k))
    (heqL : g i L = g k L) (heqU : g i U = g k U)
    (hwithin : ∀ t ∈ Icc L U,
      |deriv (deriv (g i)) t - deriv (deriv (g k)) t| ≤ M)
    (hc : 0 < γ)
    (hx₀ : x₀ ∈ Icc l u) (hx₁ : x₁ ∈ Icc l u)
    (hy₁ : y₁ ∈ Icc l u) (hy₀ : y₀ ∈ Icc l u)
    (hxx : x₀ < x₁) (hmid : x₁ < y₁) (hyy : y₁ < y₀)
    (hij : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g i)) t - deriv (deriv (g j)) t)
    (him : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g i)) t - deriv (deriv (g m)) t)
    (hkj : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hkm : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g k)) t - deriv (deriv (g m)) t)
    (hcx₀ : NearContact δ η (g i) (g j) x₀)
    (hcx₁ : NearContact δ η (g i) (g m) x₁)
    (hcy₁ : NearContact δ η (g k) (g m) y₁)
    (hcy₀ : NearContact δ η (g k) (g j) y₀)
    (hroomx : 2 * δ < γ / 2 * (x₁ - x₀) ^ 2 - η * (x₁ - x₀))
    (hroomy : 2 * δ < γ / 2 * (y₀ - y₁) ^ 2 - η * (y₀ - y₁))
    (hroomouter : 2 * δ < γ / 2 * (y₀ - x₀) ^ 2 - η * (y₀ - x₀)) :
    ∃ a ∈ Ioo x₀ x₁, ∃ b ∈ Ioo y₁ y₀,
      g j a = g m a ∧ g j b = g m b ∧ y₁ - x₁ < b - a ∧
        γ * (b - a) < M * (U - L) + 2 * η := by
  have hxy : x₀ < y₀ := hxx.trans (hmid.trans hyy)
  have hsign := contact_pair_upper_dominance (hg i) (hg k) (hg j)
    (fun t ht => hij t (uIcc_subset_Icc hx₀ hy₀ ht))
    (fun t ht => hkj t (uIcc_subset_Icc hx₀ hy₀ ht)) hcx₀ hcy₀
    (by simpa only [abs_of_pos (sub_pos.mpr hxy)] using hroomouter)
  have hin := one_mem_lens_of_opposite_signs hg hjet i k hl hu hshort hL hU hLU
    hik heqL heqU hx₀ hy₀ hsign.1 hsign.2
  have hwidth : γ * (y₀ - x₀) ≤ M * (U - L) + 2 * η := by
    rcases hin with hin | hin
    · have h := two_slope_contacts_lens_width (hg i) (hg k) (hg j) hLU
        ⟨hin.1.le, hin.2.le⟩ heqL heqU hwithin
        (fun t ht => hkj t (uIcc_subset_Icc hx₀ hy₀ ht)) hcx₀.2 hcy₀.2
      simpa only [abs_sub_comm x₀ y₀, abs_of_pos (sub_pos.mpr hxy)] using h
    · have h := two_slope_contacts_lens_width (hg k) (hg i) (hg j) hLU
        ⟨hin.1.le, hin.2.le⟩ heqL.symm heqU.symm
        (by simpa only [abs_sub_comm] using hwithin)
        (fun t ht => hij t (uIcc_subset_Icc hy₀ hx₀ ht)) hcy₀.2 hcx₀.2
      simpa only [abs_of_pos (sub_pos.mpr hxy)] using h
  obtain ⟨a, ha, b, hb, heqa, heqb, hab, hsmall⟩ :=
    exists_lens_of_opposite_contacts (hg i) (hg k) (hg j) (hg m) hxx hmid hyy
      (fun t ht => hij t (uIcc_subset_Icc hx₀ hx₁ ht))
      (fun t ht => him t (uIcc_subset_Icc hx₀ hx₁ ht))
      (fun t ht => hkm t (uIcc_subset_Icc hy₁ hy₀ ht))
      (fun t ht => hkj t (uIcc_subset_Icc hy₁ hy₀ ht))
      hcx₀ hcx₁ hcy₁ hcy₀ hroomx hroomy
  exact ⟨a, ha, b, hb, heqa, heqb, by linarith [ha.2, hb.1],
    (mul_lt_mul_of_pos_left hsmall hc).trans_le hwidth⟩

/-- Above four times the slope-error scale, the additive error in lens
contraction is absorbed by the child width itself. -/
theorem lens_contraction_of_slope_room {γ M L U a b s η : ℝ}
    (hγ : 0 < γ) (hwidth : γ * (b - a) < M * (U - L) + 2 * η)
    (hs : s ≤ b - a) (herror : 4 * η ≤ γ * s) :
    γ * (b - a) < 2 * M * (U - L) := by
  have h := mul_le_mul_of_nonneg_left hs hγ.le
  linarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
