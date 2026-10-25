/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ResidualLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ResidualZoom
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomParameterCount
import Submission.Lib.K4QuadraticSublevel

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

/-- One original fine parameter piece in one zoom cell has a bounded list
of canonical residual bins. The canonical value may depend on the original
fine state, provided it is within r of the actual residual. -/
theorem residual_bins_on_parameter_piece {ρ β r H L : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hr : 0 < r) (hscale : β ≤ ρ * r)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (q b : Fin 5 → ℤ) (z : Fin 3 → ℤ)
    (F : ℝ → ℝ) (S : ScalarIncidence → ℝ) (E : Set ScalarIncidence)
    (hpiece : ∀ p ∈ E, p.1 ∈ parameterPiece ρ β q b ∧ cell r (position ρ q p) = z)
    (htime : ∀ p ∈ E, |p.2| ≤ 1) (hrow : ∀ p ∈ E, |F p.2| ≤ H)
    (hvar : ∀ p ∈ E, ∀ p' ∈ E, |F p.2 - F p'.2| ≤ L * r)
    (hnear : ∀ p ∈ E, |S p - residual ρ q F p.1 p.2| ≤ r) :
    ∃ Q : Finset ℤ, (Q.card : ℝ) ≤ 2 * (7 + H + L) + 2 ∧
      ∀ p ∈ E, ⌊S p / r⌋ ∈ Q := by
  classical
  have hdiam (p : ScalarIncidence) (hp : p ∈ E) (p' : ScalarIncidence) (hp' : p' ∈ E) :
      |S p - S p'| ≤ (7 + H + L) * r := by
    have hb := hpiece p hp
    have hb' := hpiece p' hp'
    have hgap : |p.2 - p'.2| ≤ r := by
      have he := (norm_le_pi_norm (position ρ q p - position ρ q p') 0).trans
        (norm_sub_lt_of_cell_eq hr (hb.2.trans hb'.2.symm)).le
      exact he
    have hres := residual_piece_variation hρ hβ hscale q F p.1 p'.1 hb'.1.1
      (hb.1.2.trans hb'.1.2.symm) (htime p hp) hgap (hrow p hp) (hvar p hp p' hp')
    have htail : |residual ρ q F p.1 p.2 - S p'| ≤ (5 + H + L) * r + r :=
      (abs_sub_le _ (residual ρ q F p'.1 p'.2) _).trans
        (add_le_add hres (by simpa only [abs_sub_comm] using hnear p' hp'))
    exact (abs_sub_le _ (residual ρ q F p.1 p.2) _).trans
      ((add_le_add (hnear p hp) htail).trans_eq (by ring))
  have hb := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (S '' E) (by positivity : 0 ≤ (7 + H + L) * r) hr 0 (by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
      simpa only [Real.dist_eq] using hdiam p hp p' hp')
  let B := (fun x : ℝ => ⌊(x - 0) / r⌋) '' (S '' E)
  have hfin : B.Finite := hb.1
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hb.2.trans_eq (by field_simp)
  · intro p hp
    apply hfin.mem_toFinset.mpr
    exact ⟨S p, ⟨p, hp, rfl⟩, by simp only [sub_zero]⟩

/-- Combine the per-piece residual lists without replacing the original
coefficient bins by a new sampling distribution. -/
theorem residual_bins_of_parameter_list {ρ β r H L : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hr : 0 < r) (hscale : β ≤ ρ * r)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (q : Fin 5 → ℤ) (z : Fin 3 → ℤ)
    (F : ℝ → ℝ) (S : ScalarIncidence → ℝ) (E : Set ScalarIncidence)
    (B : Finset (Fin 5 → ℤ)) (hB : ∀ p ∈ E, cell β p.1.2 ∈ B)
    (hworld : ∀ p ∈ E, cell ρ p.1.2 = q ∧ cell r (position ρ q p) = z)
    (htime : ∀ p ∈ E, |p.2| ≤ 1) (hrow : ∀ p ∈ E, |F p.2| ≤ H)
    (hvar : ∀ p ∈ E, ∀ p' ∈ E, |F p.2 - F p'.2| ≤ L * r)
    (hnear : ∀ p ∈ E, |S p - residual ρ q F p.1 p.2| ≤ r) :
    ∃ Q : Finset ℤ, (Q.card : ℝ) ≤ (B.card : ℝ) * (2 * (7 + H + L) + 2) ∧
      ∀ p ∈ E, ⌊S p / r⌋ ∈ Q := by
  classical
  have hex (b : Fin 5 → ℤ) := residual_bins_on_parameter_piece hρ hβ hr hscale hH hL q b z
    F S {p ∈ E | cell β p.1.2 = b}
    (fun p hp => ⟨⟨(hworld p hp.1).1, hp.2⟩, (hworld p hp.1).2⟩)
    (fun p hp => htime p hp.1) (fun p hp => hrow p hp.1)
    (fun p hp p' hp' => hvar p hp.1 p' hp'.1) (fun p hp => hnear p hp.1)
  choose Q hcard hlist using hex
  refine ⟨B.biUnion Q, ?_, ?_⟩
  · calc
      ((B.biUnion Q).card : ℝ) ≤ ∑ b ∈ B, ((Q b).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ B, (2 * (7 + H + L) + 2) := Finset.sum_le_sum (fun b _ => hcard b)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  · intro p hp
    exact Finset.mem_biUnion.mpr ⟨cell β p.1.2, hB p hp, hlist _ p ⟨hp, rfl⟩⟩

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
