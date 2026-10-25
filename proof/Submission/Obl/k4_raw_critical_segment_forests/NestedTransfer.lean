import Submission.Obl.k4_raw_critical_segment_forests.NestedInterface
import Submission.Obl.k4_finite_width_output_exclusion.Horizon

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The finite lifting conclusion, with its sample map and supplied parents. -/
def AtlasLift (G q : Data) (χ : ℕ → ℕ) (par : (n : ℕ) → Atlas G (χ n)) : Prop :=
  ∀ M' D' : ℕ, ∃ M'' D'' : ℕ, ∀ e : ℝ, 0 < e → ∃ e' : ℝ, 0 < e' ∧
    ∀ᶠ n in atTop, ∀ (κ' : ℝ) (a : Atlas q n), 1 ≤ κ' → q.K n ≤ κ' →
      κ' ≤ q.N n ^ e' → a.TrueAt M' D' κ' →
      ∃ (κ'' : ℝ) (c : Atlas G (χ n)) (pmap : Fin c.C → Fin (par n).C)
        (cmap : Fin c.C → Fin a.C),
        1 ≤ κ'' ∧ G.K (χ n) ≤ κ'' ∧ κ'' ≤ G.N (χ n) ^ e ∧
        c.T = (par n).T + a.T ∧ c.TrueAt M'' D'' κ'' ∧
        NestedIn c (par n) pmap ∧
        ∀ b, |Matrix.det (c.Q b)| * (4 : ℝ) ^ c.T =
          (|Matrix.det ((par n).Q (pmap b))| * (4 : ℝ) ^ (par n).T) *
            (|Matrix.det (a.Q (cmap b))| * (4 : ℝ) ^ a.T)

/-- Exact concatenation of time partitions transfers every remainder cost. -/
lemma AtlasLift.cost {G q : Data} {χ : ℕ → ℕ} {par : (n : ℕ) → Atlas G (χ n)}
    (hl : AtlasLift G q χ par) (hχ : Tendsto χ atTop atTop)
    (hN : ∀ n, q.N n = G.N (χ n)) {h h' : ℝ}
    (ht : ∀ n, (2 : ℝ) ^ (par n).T ≤ G.N (χ n) ^ h)
    (hq : Valid q) (hc : Cost q h') : Cost G (h + h') := by
  obtain ⟨M, D, hc⟩ := (cost_iff q h').mp hc
  obtain ⟨M', D', hl⟩ := hl M D
  apply (cost_iff G (h + h')).mpr
  refine ⟨M', D', ?_⟩
  intro e he
  obtain ⟨e', he', hlate⟩ := hl e he
  apply hχ.frequently
  apply ((hc e' he').and_eventually hlate).mono
  rintro n ⟨⟨κ, hκ, hK, hκN, a, haT, ha⟩, hn⟩
  obtain ⟨κ', c, pmap, cmap, hκ', hK', hκN', hT, hc, hnest, hwidth⟩ :=
    hn κ a hκ hK hκN ha
  refine ⟨κ', hκ', hK', hκN', c, ?_, hc⟩
  rw [hT, pow_add]
  have ht' : (2 : ℝ) ^ a.T ≤ G.N (χ n) ^ h' := by rwa [hN n] at haT
  exact (mul_le_mul (ht n) ht' (by positivity) (by
    rw [← hN n]; exact (Real.rpow_pos_of_pos (hq.scale_pos n) _).le)).trans_eq
      (Real.rpow_add (by rw [← hN n]; exact hq.scale_pos n) _ _).symm

lemma AtlasLift.horizon {G q : Data} {χ : ℕ → ℕ} {par : (n : ℕ) → Atlas G (χ n)}
    (hl : AtlasLift G q χ par) (hi : Initial) (hG : Valid G) (hq : Valid q)
    (hχ : Tendsto χ atTop atTop) (hN : ∀ n, q.N n = G.N (χ n)) {h : ℝ}
    (ht : ∀ n, (2 : ℝ) ^ (par n).T ≤ G.N (χ n) ^ h) :
    Horizon G ≤ h + Horizon q := by
  have hx := horizon_transfer hi hG hq (a := h) (b := 1) zero_lt_one
    (fun h' hc => by simpa only [one_mul] using hl.cost hχ hN ht hq hc)
  simpa only [one_mul] using hx

end
end Submission.Obl.k4_raw_critical_segment_forests
