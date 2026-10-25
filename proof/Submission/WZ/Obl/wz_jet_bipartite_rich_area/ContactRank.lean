-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactRank.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensRank

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The canonical rank strictly decreases across a separated contact
cycle in the same-orientation class. The small within-color curvature
bound supplies the contraction factor. Root-only parent pairs are covered. -/
theorem windowLensRank_lt_of_contact_cycle {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j m : Fin n) {l u x₀ x₁ y₁ y₀ γ M δ η B s : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (hik : 0 < dist (q i) (q k)) (hjm : 0 < dist (q j) (q m))
    (hwithin : ∀ t ∈ Icc l u,
      |deriv (deriv (g i)) t - deriv (deriv (g k)) t| ≤ M)
    (hc : 0 < γ) (hB : 1 < B) (hs : 0 < s)
    (hratio : 2 * M * B ≤ γ) (herror : 4 * η ≤ γ * s)
    (hx₀ : x₀ ∈ Icc l u) (hx₁ : x₁ ∈ Icc l u)
    (hy₁ : y₁ ∈ Icc l u) (hy₀ : y₀ ∈ Icc l u)
    (hxx : x₀ < x₁) (hmid : s ≤ y₁ - x₁) (hyy : y₁ < y₀)
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
    windowLensRank g B s l u j m < windowLensRank g B s l u i k := by
  have hmid' : x₁ < y₁ := by linarith
  obtain ⟨a, ha, b, hb, heqa, heqb, hab, hsmall⟩ :=
    exists_lens_of_opposite_contacts (hg i) (hg k) (hg j) (hg m) hxx hmid' hyy
      (fun t ht => hij t (uIcc_subset_Icc hx₀ hx₁ ht))
      (fun t ht => him t (uIcc_subset_Icc hx₀ hx₁ ht))
      (fun t ht => hkm t (uIcc_subset_Icc hy₁ hy₀ ht))
      (fun t ht => hkj t (uIcc_subset_Icc hy₁ hy₀ ht))
      hcx₀ hcx₁ hcy₁ hcy₀ hroomx hroomy
  have haw : a ∈ Icc l u := ⟨hx₀.1.trans ha.1.le, ha.2.le.trans hx₁.2⟩
  have hbw : b ∈ Icc l u := ⟨hy₁.1.trans hb.1.le, hb.2.le.trans hy₀.2⟩
  have hchild : HasWindowLens g l u j m := ⟨a, haw, b, hbw, hab, heqa, heqb⟩
  have hcw := windowLensWidth_eq_of_crossings hg hjet j m hl hu hshort haw hbw hab hjm heqa heqb
  have hwidth : s ≤ windowLensWidth g l u j m := by
    rw [hcw]
    linarith [ha.2, hb.1]
  apply windowLensRank_lt_of_contraction g hB hs (hx₀.1.trans hx₀.2) i k j m hchild hwidth
  intro hparent
  obtain ⟨L, hL, U, hU, hLU, heqL, heqU⟩ := hparent
  obtain ⟨a', ha', b', hb', heqa', heqb', hinner', hcontract⟩ :=
    exists_child_lens_of_parent_lens hg hjet i k j m hl hu hshort hL hU hLU
      hik heqL heqU (fun t ht => hwithin t ⟨hL.1.trans ht.1, ht.2.trans hU.2⟩)
      hc hx₀ hx₁ hy₁ hy₀ hxx hmid' hyy hij him hkj hkm
      hcx₀ hcx₁ hcy₁ hcy₀ hroomx hroomy hroomouter
  have ha'w : a' ∈ Icc l u := ⟨hx₀.1.trans ha'.1.le, ha'.2.le.trans hx₁.2⟩
  have hb'w : b' ∈ Icc l u := ⟨hy₁.1.trans hb'.1.le, hb'.2.le.trans hy₀.2⟩
  have ha'b' : a' < b' := ha'.2.trans (hmid'.trans hb'.1)
  have hcw' := windowLensWidth_eq_of_crossings hg hjet j m hl hu hshort
    ha'w hb'w ha'b' hjm heqa' heqb'
  have hpw := windowLensWidth_eq_of_crossings hg hjet i k hl hu hshort hL hU hLU hik heqL heqU
  rw [← hcw', ← hpw] at hcontract
  have hscaled : γ * windowLensWidth g l u j m < 2 * M * windowLensWidth g l u i k := by
    have h := mul_le_mul_of_nonneg_left hwidth hc.le
    linarith
  have hscaled' := mul_lt_mul_of_pos_left hscaled (zero_lt_one.trans hB)
  have hratio' := mul_le_mul_of_nonneg_right hratio (windowLensWidth_nonneg g l u i k)
  have hfinal : γ * (B * windowLensWidth g l u j m) < γ * windowLensWidth g l u i k := by
    nlinarith only [hscaled', hratio']
  exact (mul_lt_mul_iff_right₀ hc).mp hfinal

/-- Negation preserves the jet distance and thus allows the same rank
construction for either curvature orientation. -/
theorem jetDistance_neg (f h : ℝ → ℝ) (z : ℝ) : jetDistance (-f) (-h) z = jetDistance f h z := by
  have hneg (v : ℝ → ℝ) : deriv (-v) = -deriv v := by
    funext x
    exact deriv.neg
  simp only [jetDistance, hneg, Pi.neg_apply, neg_sub_neg, abs_sub_comm]

theorem jetControlled_neg {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)}
    {g : Fin n → ℝ → ℝ} (hjet : JetControlled q g) : JetControlled q (fun i => -g i) := by
  intro i j z hz
  simpa only [jetDistance_neg] using hjet i j z hz

theorem nearContact_neg {f h : ℝ → ℝ} {δ η z : ℝ} :
    NearContact δ η (-f) (-h) z ↔ NearContact δ η f h z := by
  simp only [NearContact, deriv.neg, Pi.neg_apply, neg_sub_neg, abs_sub_comm]

theorem windowLensRank_neg {n : ℕ} (g : Fin n → ℝ → ℝ) (B s l u : ℝ) (i j : Fin n) :
    windowLensRank (fun i => -g i) B s l u i j = windowLensRank g B s l u i j := by
  classical
  simp only [windowLensRank, HasWindowLens, windowLensWidth, windowCrossings,
    Pi.neg_apply, neg_inj]
  rfl

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
