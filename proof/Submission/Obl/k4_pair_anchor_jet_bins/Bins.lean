import Submission.Obl.k4_pair_anchor_jet_bins.Interface

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Submission.Lib.K4QuadraticSheets

noncomputable section

abbrev Coord (J : ℕ) := JetIdx J × Bool
abbrev binDim (J : ℕ) := Fintype.card (Coord J)
abbrev Bin (J : ℕ) := Fin (binDim J) → ℤ

/-- Record each real and imaginary jet coordinate in a single integer tuple. -/
def flatJetBin (J : ℕ) (w : ℝ) (f : E3 → ℂ) (α : E3) : Bin J :=
  fun i => let p := (Fintype.equivFin (Coord J)).symm i
    if p.2 then (jetBin J w f α p.1).2 else (jetBin J w f α p.1).1

theorem flatJetBin_eq_iff {J : ℕ} {w : ℝ} {f g : E3 → ℂ} {α : E3} :
    flatJetBin J w f α = flatJetBin J w g α ↔ jetBin J w f α = jetBin J w g α := by
  constructor
  · intro h
    funext i
    apply Prod.ext
    · have h' := congrFun h (Fintype.equivFin (Coord J) (i, false))
      simpa [flatJetBin] using h'
    · have h' := congrFun h (Fintype.equivFin (Coord J) (i, true))
      simpa [flatJetBin] using h'
  · intro h
    funext i
    simp only [flatJetBin, h]

theorem flatJetBin_eq_of_eqOn_ball {J : ℕ} {w : ℝ} {f g : E3 → ℂ} {α : E3}
    {r : ℝ} (hr : 0 < r) (h : ∀ z ∈ Metric.ball α r, f z = g z) :
    flatJetBin J w f α = flatJetBin J w g α := by
  apply flatJetBin_eq_iff.mpr
  funext i
  simp only [jetBin, jetCoord, iteratedFDeriv_eq_of_eqOn_ball hr h]

theorem flatJetBin_near {J : ℕ} {w : ℝ} (hw : 0 < w) {f g : E3 → ℂ} {α : E3}
    (h : ∀ j : ℕ, j ≤ J → ‖iteratedFDeriv ℂ j f α - iteratedFDeriv ℂ j g α‖ ≤ w) :
    ∀ i, |flatJetBin J w f α i - flatJetBin J w g α i| ≤ 1 := by
  intro i
  let p := (Fintype.equivFin (Coord J)).symm i
  have hj : (p.1.1 : ℕ) ≤ J := Nat.lt_succ_iff.mp p.1.1.2
  have hcoord : ‖jetCoord J f α p.1 - jetCoord J g α p.1‖ ≤ w := by
    exact (norm_basis_le
      (iteratedFDeriv ℂ (p.1.1 : ℕ) f α - iteratedFDeriv ℂ (p.1.1 : ℕ) g α) p.1.2).trans
      (h _ hj)
  have hc := cbin_near hw hcoord
  change |(if p.2 then (jetBin J w f α p.1).2 else (jetBin J w f α p.1).1) -
    (if p.2 then (jetBin J w g α p.1).2 else (jetBin J w g α p.1).1)| ≤ 1
  cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact hc.1
  · exact hc.2

theorem jets_close_of_flatJetBin_eq {J : ℕ} {w : ℝ} (hw : 0 < w)
    {f g : E3 → ℂ} {α : E3} (h : flatJetBin J w f α = flatJetBin J w g α) :
    ∀ j : ℕ, j ≤ J →
      ‖iteratedFDeriv ℂ j f α - iteratedFDeriv ℂ j g α‖ ≤ (3 : ℝ) ^ J * (2 * w) := by
  intro j hj
  have hjet := norm_iteratedFDeriv_sub_le_of_jetBin_eq hw (flatJetBin_eq_iff.mp h) j hj
  exact hjet.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj)
    (by positivity))

def branchBin (J : ℕ) (w : ℝ) (P : Test) (α : R3) (ε : Bool) : Bin J :=
  flatJetBin J w (canonBranch (P.map (algebraMap ℝ ℂ)) (emb α) ε) (emb α)

/-- A quadratic has at most two canonical root jets at an anchor. -/
def bins (J : ℕ) (w : ℝ) (P : Test) (α : R3) : Finset (Bin J) :=
  Finset.univ.image (branchBin J w P α)

theorem card_bins (J : ℕ) (w : ℝ) (P : Test) (α : R3) : (bins J w P α).card ≤ 2 := by
  exact (Finset.card_image_le).trans (by simp)

theorem branchBin_mem (J : ℕ) (w : ℝ) (P : Test) (α : R3) (ε : Bool) :
    branchBin J w P α ε ∈ bins J w P α := by
  exact Finset.mem_image.mpr ⟨ε, Finset.mem_univ _, rfl⟩

theorem mem_bins {J : ℕ} {w : ℝ} {P : Test} {α : R3} {β : Bin J}
    (h : β ∈ bins J w P α) : ∃ ε : Bool, branchBin J w P α ε = β := by
  obtain ⟨ε, _, hε⟩ := Finset.mem_image.mp h
  exact ⟨ε, hε⟩

theorem jets_close_of_branchBin_eq {J : ℕ} {w : ℝ} (hw : 0 < w)
    {P R : Test} {α : R3} {ε ε' : Bool}
    (h : branchBin J w P α ε = branchBin J w R α ε') :
    ∀ j : ℕ, j ≤ J →
      ‖iteratedFDeriv ℂ j (canonBranch (P.map (algebraMap ℝ ℂ)) (emb α) ε) (emb α) -
        iteratedFDeriv ℂ j (canonBranch (R.map (algebraMap ℝ ℂ)) (emb α) ε') (emb α)‖ ≤
      (3 : ℝ) ^ J * (2 * w) :=
  jets_close_of_flatJetBin_eq hw h

end
end Submission.Obl.k4_pair_anchor_jet_bins
