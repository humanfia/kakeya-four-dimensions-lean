import Submission.Obl.k4_raw_critical_segment_forests.Forest
import Submission.Obl.k4_raw_critical_segment_forests.OneLayer

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Certificate on a particular finite forest and its width exponents. -/
def Forest.RawData {p : Data} {k : ℕ} (a : Forest p k) (width : Fin a.C → ℝ)
    (kr w ε q σ : ℝ) (m : ℕ) (s r : ℕ → ℝ) (M D : ℕ) : Prop :=
  a.κ ≤ p.N k ^ σ ∧ a.Core M D m r ∧
    (∀ i, i < m → p.N k ^ (kr * s i - ε) ≤ (2 : ℝ) ^ a.T i ∧
      (2 : ℝ) ^ a.T i ≤ p.N k ^ (kr * s i + ε) ∧
      (2 : ℝ) ^ a.T i ≤ p.N k ^ M) ∧
    (∀ b, |width b| ≤ (M : ℝ) ∧
      p.N k ^ (-width b) = |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T (a.lev b) ∧
      (a.lev b = 0 → w * r 0 - q ≤ width b) ∧
      (0 < a.lev b → width (a.par b) +
        w * (r (a.lev b) - r (a.lev (a.par b))) - q ≤ width b))

/-- The full single-sample conclusion, packaged as a finite forest. -/
def RawAt (p : Data) (kr w ε q σ : ℝ) (m : ℕ) (s r : ℕ → ℝ) (M D k : ℕ) : Prop :=
  ∃ (a : Forest p k) (width : Fin a.C → ℝ), a.RawData width kr w ε q σ m s r M D

/-- The frozen raw-forest conclusion for a grid consisting only of its final
endpoint. -/
theorem raw_one_layer {ds kr S η w ε q : ℝ}
    (hkr : kr ≤ 1) (hunif : UniformWidth ds kr S η w)
    {s : ℕ → ℝ} (hs : s 0 = 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) :
    ∃ t : ℝ, 0 < t ∧ ∀ p : Data, Valid p → p.L = 1 → p.S = S → p.η = η →
      p.d < ds + t → kr - t < Horizon p →
      ∃ (r : ℕ → ℝ) (M D : ℕ), r 0 = 1 ∧
        (∀ i, i < 1 → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ 1) ∧
        ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop, RawAt p kr w ε q σ 1 s r M D k := by
  obtain ⟨t, ht, hsys⟩ := one_layer_systems hkr hunif hε hε1 hq
  refine ⟨t, ht, ?_⟩
  intro p hp hpL hpS hpη hpd hpH
  obtain ⟨M, D, hsystems⟩ := hsys p hp hpL hpS hpη hpd hpH
  refine ⟨fun _ => 1, M, D, rfl, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    simp only [hi0, hs, sub_self, abs_zero]
    exact ⟨hε.le, zero_lt_one, le_rfl⟩
  · intro σ hσ
    apply (hsystems σ hσ).mono
    rintro k ⟨κ, a, width, hκ, hKκ, hκN, ha, hTlo, hThi, hTM, hw⟩
    refine ⟨oneLayerForest a κ, width, hκN, oneLayerForest_core hpL hκ hKκ ha, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by omega
      simpa only [oneLayerForest, hi0, hs, mul_one] using ⟨hTlo, hThi, hTM⟩
    · intro b
      refine ⟨(hw b).1, (hw b).2.1, ?_, ?_⟩
      · intro hb
        simpa only [mul_one] using (hw b).2.2
      · intro hb
        exact False.elim (Nat.not_lt_zero _ hb)

end
end Submission.Obl.k4_raw_critical_segment_forests
