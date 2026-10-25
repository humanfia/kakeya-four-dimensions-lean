import Submission.Obl.k4_raw_critical_segment_forests.Append
import Submission.Obl.k4_raw_critical_segment_forests.Preparation

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

lemma Forest.Core.congr_depth {p : Data} {k M D m : ℕ} {a : Forest p k}
    {r r' : ℕ → ℝ} (ha : a.Core M D m r) (hr : ∀ i, i < m → r i = r' i) :
    a.Core M D m r' := by
  obtain ⟨hκ, hK, hC, hmass, hsep, hchart⟩ := ha
  refine ⟨hκ, hK, hC, hmass, hsep, ?_⟩
  intro b
  have hb := hchart b
  have hpb := hchart (a.par b)
  simpa only [← hr (a.lev b) hb.1, ← hr (a.lev (a.par b)) hpb.1] using hb

lemma Forest.RawData.congr_depth {p : Data} {k M D m : ℕ} {a : Forest p k}
    {v : Fin a.C → ℝ} {kr w ε q σ : ℝ} {s r r' : ℕ → ℝ}
    (hm : 0 < m) (ha : a.RawData v kr w ε q σ m s r M D)
    (hr : ∀ i, i < m → r i = r' i) : a.RawData v kr w ε q σ m s r' M D := by
  obtain ⟨hκ, hcore, htime, hwidth⟩ := ha
  refine ⟨hκ, hcore.congr_depth hr, htime, ?_⟩
  intro b
  have hb := hcore.2.2.2.2.2 b
  have hpb := hcore.2.2.2.2.2 (a.par b)
  simpa only [← hr 0 hm, ← hr (a.lev b) hb.1, ← hr (a.lev (a.par b)) hpb.1]
    using hwidth b

lemma Forest.RawData.mono {p : Data} (hp : Valid p) {k M M' D D' m : ℕ}
    {a : Forest p k} {v : Fin a.C → ℝ} {kr w ε ε' q σ σ' κ : ℝ} {s r : ℕ → ℝ}
    (ha : a.RawData v kr w ε q σ m s r M D)
    (hM : M ≤ M') (hD : D ≤ D') (hε : ε ≤ ε')
    (haκ : a.κ ≤ κ) (hκ : κ ≤ p.N k ^ σ') :
    (a.reslack κ).RawData v kr w ε' q σ' m s r M' D' := by
  obtain ⟨hκold, hcore, htime, hwidth⟩ := ha
  refine ⟨hκ, hcore.mono hp hM hD haκ, ?_, ?_⟩
  · intro i hi
    exact ⟨(Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k)
      (by linarith)).trans (htime i hi).1,
      (htime i hi).2.1.trans (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k)
        (by linarith)),
      (htime i hi).2.2.trans (pow_le_pow_right₀ (hp.scale_ge_one k) hM)⟩
  · intro b
    exact ⟨(hwidth b).1.trans (by exact_mod_cast hM), (hwidth b).2⟩

lemma append_card_bound {N : ℝ} (hN : 2 ≤ N) {Ca Cb Ma Mb M : ℕ}
    (ha : (Ca : ℝ) ≤ N ^ Ma) (hb : (Cb : ℝ) ≤ N ^ Mb)
    (hM : max Ma Mb + 1 ≤ M) : ((Ca + Cb : ℕ) : ℝ) ≤ N ^ M := by
  have hN1 : 1 ≤ N := by linarith
  have hNa := pow_le_pow_right₀ hN1 (le_max_left Ma Mb)
  have hNb := pow_le_pow_right₀ hN1 (le_max_right Ma Mb)
  calc
    ((Ca + Cb : ℕ) : ℝ) ≤ 2 * N ^ max Ma Mb := by push_cast; linarith
    _ ≤ N ^ (max Ma Mb + 1) := by rw [pow_succ]; nlinarith [pow_nonneg (by linarith : 0 ≤ N) (max Ma Mb)]
    _ ≤ N ^ M := pow_le_pow_right₀ hN1 hM

/-- Finite assembly retains all old widths and appends the new edge widths. -/
theorem append_rawData {p : Data} {k M D m : ℕ} {r s : ℕ → ℝ}
    {kr w ε q σ : ℝ} {a : Forest p k} {b : Atlas p k}
    {va : Fin a.C → ℝ} {vb : Fin b.C → ℝ}
    (parent : Fin b.C → Fin a.C) (hm : 0 < m)
    (ha : a.RawData va kr w ε q σ m s r M D)
    (hb : TrueDepth b M D a.κ (r m))
    (hC : ((a.C + b.C : ℕ) : ℝ) ≤ p.N k ^ M)
    (hlev : ∀ z, a.lev (parent z) + 1 = m)
    (hγ : ∀ z, a.γ (parent z) = b.γ z)
    (hA : ∀ z, b.A z ⊆ a.A (parent z))
    (hF : ∀ z, b.F z ⊆ a.F (parent z))
    (hlo : ∀ z, (a.j (parent z) : ℝ) / (2 : ℝ) ^ a.T (a.lev (parent z)) ≤
      (b.j z : ℝ) / (2 : ℝ) ^ b.T)
    (hhi : ∀ z, ((b.j z : ℝ) + 1) / (2 : ℝ) ^ b.T ≤
      ((a.j (parent z) : ℝ) + 1) / (2 : ℝ) ^ a.T (a.lev (parent z)))
    (hT : p.N k ^ (kr * s m - ε) ≤ (2 : ℝ) ^ b.T ∧
      (2 : ℝ) ^ b.T ≤ p.N k ^ (kr * s m + ε) ∧ (2 : ℝ) ^ b.T ≤ p.N k ^ M)
    (hv : ∀ z, |vb z| ≤ (M : ℝ) ∧
      p.N k ^ (-vb z) = |Matrix.det (b.Q z)| * (4 : ℝ) ^ b.T ∧
      va (parent z) + w * (r m - r (a.lev (parent z))) - q ≤ vb z) :
    (a.append b m parent).RawData (Fin.addCases va vb) kr w ε q σ (m + 1) s r M D := by
  classical
  obtain ⟨hκ, hcore, htime, hwidth⟩ := ha
  have hne (z : Fin a.C) : a.lev z ≠ m := (hcore.2.2.2.2.2 z).1.ne
  refine ⟨hκ, append_core parent hm hcore hb hC hlev hγ hA hF hlo hhi, ?_, ?_⟩
  · intro i hi
    by_cases him : i = m
    · subst i
      simpa only [Forest.append, ite_true] using hT
    · simpa only [Forest.append, if_neg him] using htime i (by omega)
  · intro z
    refine Fin.addCases ?_ ?_ z
    · intro z
      simpa only [Forest.append, Fin.addCases_left, if_neg (hne z),
        if_neg (hne (a.par z))] using hwidth z
    · intro z
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [Fin.addCases_right] using (hv z).1
      · simpa only [Forest.append, Fin.addCases_right, ite_true] using (hv z).2.1
      · intro hz
        simp only [Forest.append, Fin.addCases_right] at hz
        exact False.elim ((by omega : m ≠ 0) hz)
      · intro _
        simpa only [Forest.append, Fin.addCases_right, Fin.addCases_left] using (hv z).2.2

end
end Submission.Obl.k4_raw_critical_segment_forests
