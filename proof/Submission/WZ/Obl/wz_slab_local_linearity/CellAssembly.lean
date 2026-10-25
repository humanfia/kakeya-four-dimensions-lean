-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellDichotomy
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityLine

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric

/-- The denominator in the fourth-moment count, when uniform bottom-scale covers
supply the zero-dimensional AD conditions. -/
noncomputable def cellCountDenominator (M : ℕ) (NB K κ : ℝ) : ℝ :=
  (NB * (K * (16 / κ + 3))) ^ 2 * (M * (M * (3 * K))) * (M * (3 * K))

lemma cellCountDenominator_pos {M : ℕ} {NB K κ : ℝ}
    (hM : 0 < M) (hNB : 0 < NB) (hK : 0 < K) (hκ : 0 < κ) :
    0 < cellCountDenominator M NB K κ := by
  unfold cellCountDenominator
  positivity

/-- The cell count and the projection dichotomy produce affine values at occupied
heights. All quantitative choices are isolated as explicit scalar inequalities. -/
theorem CellHyp.exists_affine_of_bounds {ρ : ℝ} {M : ℕ} {K κ β σ C ε η δ NB N₀ : ℝ}
    {f : ℝ → ℝ} {V : Space → Space} {P : Finset (ℤ × ℤ × ℤ)}
    {A : ℤ → Set ℝ} {AL : ℤ × ℤ × ℤ → Set ℝ}
    (h : CellHyp ρ M 0 K κ β f V P A AL) (hP : P.Nonempty) (hK : 0 < K)
    (hNB : (#(P.image (blockOf M)) : ℝ) ≤ NB) (hNBpos : 0 < NB)
    (hτ : (3 * K) * M * (3 * K) * (1 + 16 / κ) < (#P : ℝ) / (2 * NB))
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hA : ∀ k, Assouad ρ (1 - σ) C (A k))
    (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hLD : LDInstance σ ε η δ)
    (hN₀a : 8 * δ * (M * ρ) / ρ + 1 ≤ N₀)
    (hN₀b : 12 * δ / (κ / 8 * (M * ρ)) + 1 ≤ N₀)
    (n4 : 11 ≤ δ ^ (-η)) (n5 : 12000 / κ ^ 2 ≤ δ ^ (-η))
    (n6 : cellCountDenominator M NB K κ * (2 * (N₀ ^ 3 * δ ^ (η - 3))) ≤
      ((#P : ℝ) / (2 * M)) ^ 4)
    (n7 : κ / 8 * ρ / (M * ρ) ≤ δ) (n8 : 6 * C ≤ δ ^ (-η))
    (n10 : 48 * (M * ρ) * δ ≤ ρ) :
    ∃ a b : ℝ, |b| ≤ 2 ∧ ∃ S : Finset ℤ,
      S ⊆ P.image (fun q => q.2.2) ∧ δ ^ (ε - 1) ≤ #S ∧
      ∀ k ∈ S, |f (ρ * k) - (a + b * (ρ * k))| ≤ ρ / 8 := by
  classical
  have hτ' : (3 * (K * ((40 * (M * ρ)) / ρ) ^ (0 : ℝ))) * M *
      (3 * (K * ((12 * (M * ρ)) / ρ) ^ (0 : ℝ))) * (1 + 16 / κ) <
      (#P : ℝ) / (2 * NB) := by simpa only [Real.rpow_zero, mul_one] using hτ
  obtain ⟨k0, w, Y, g, R, T, hT, hoccupied, hcount⟩ := h.exists_dotTriples hP hNB hNBpos hτ'
  have hcount' : ((#P : ℝ) / (2 * M)) ^ 4 ≤ cellCountDenominator M NB K κ * #T := by
    simpa only [cellCountDenominator, Real.rpow_zero, mul_one] using hcount
  have hn6 : 2 * (N₀ ^ 3 * δ ^ (η - 3)) ≤ #T :=
    le_of_mul_le_mul_left (n6.trans hcount') (cellCountDenominator_pos h.hM hNBpos hK h.hκ)
  obtain ⟨a, b, hb, S, hST, hScard, hSf⟩ := hT.exists_linear h.hρ h.hM h.hκ h.hκ1
    h.hf_lip hσ hσ1 hC (hA k0) hε1 hδ hδ1 hLD hN₀a hN₀b n4 n5 hn6 n7 n8 n10
  refine ⟨a, b, hb, S, ?_, hScard, hSf⟩
  intro k hk
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (hST hk)
  exact hoccupied t ht

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
