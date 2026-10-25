import Submission.Obl.k4_scalar_true_atlas_terminal_lists.BinBounds
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.CrossingCutFormat

/-! One complexity exponent works for all time exponents and list cutoffs. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set MvPolynomial

noncomputable def listComplexity (p : Data) (B : ℕ) : ℕ := B + ⌈L p⌉₊ + 12

theorem listComplexity_ge (p : Data) (B : ℕ) : B ≤ listComplexity p B := by
  simp only [listComplexity]
  omega

theorem listComplexity_pos (p : Data) (B : ℕ) : 1 ≤ listComplexity p B := by
  simp only [listComplexity]
  omega

/-- No time exponent or tolerance enters the complexity chosen for the
geometric observation cutoff. -/
theorem RawChartData.cutoff_format {p : Data} (hp : Exact p)
    {B k T n : ℕ} {h δ Λ R : ℝ}
    {γ : Fin n → Fin (worlds p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Trajectory} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    (hd : RawChartData p B (L p) (L p) h δ true k T n γ j A C u v J P) (hδ : δ ≤ 1) :
    ∀ i z, Format 6 (N p k ^ (listComplexity p B : ℝ)) (listComplexity p B)
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C i ∧
        ((labelsAt γ
          (fun i => crossing (N p k ^ (-L p)) Λ ((j i : ℕ) / (2 : ℝ) ^ T)
            (1 / (2 : ℝ) ^ T) (u i) (v i) (J i) (P i)) (γ i)
          (observation p k (L p) ((z, fun e : Fin 5 => w e.castSucc), w 5))).card : ℝ) ≤ R} := by
  classical
  intro i z
  have hN : 2 ≤ N p k := hp.resolution_ge k
  have hN1 : 1 ≤ N p k := le_trans (by norm_num) hN
  have hN0 : 0 < N p k := by linarith
  let a := N p k ^ (-L p)
  let F := hiddenBins (3 * N p k / a + 1)
  let e : Fin F.card ≃ F := F.equivFin.symm
  let bins : Fin F.card → ℤ := fun i => (e i : ℤ)
  let D : Set (Fin 6 → ℝ) := {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C i}
  have hbins : ∀ w ∈ D, ∃ t, ⌊eval w hiddenPolynomial / a⌋ = bins t := by
    intro w hw
    have hb := hd.hidden_bins hp hδ i ((z, fun e : Fin 5 => w e.castSucc), w 5) hw
    have hb' : ⌊eval w hiddenPolynomial / a⌋ ∈ F := by
      simpa [F, a, hiddenPolynomial, x] using hb
    refine ⟨e.symm ⟨_, hb'⟩, ?_⟩
    simp [bins]
  have hP : ∀ i, (P i).totalDegree ≤ 2 := fun i => (hd.2.2.2.2.2.1 i).2.2.2.2.2.1
  have hD : Format 6 (N p k ^ (B : ℝ)) B D :=
    ((hd.2.2.2.2.2.1 i).2.2.2.2.2.2.2.2.2.1 z)
  have hm : (F.card : ℝ) ≤ N p k ^ (⌈L p⌉₊ + 5 : ℕ) :=
    hiddenBins_polynomial_bound hN hp.length_pos.le
  have hn : (n : ℝ) ≤ N p k ^ B := by simpa using hd.2.1
  have hcount : N p k ^ (B : ℝ) + (F.card : ℝ) * (2 + (n : ℝ) * 6) ≤
      N p k ^ (listComplexity p B : ℝ) := by
    simpa only [listComplexity, Real.rpow_natCast] using
      crossing_atom_budget hN hm (Nat.cast_nonneg F.card) hn (Nat.cast_nonneg n)
  have hBout : 1 ≤ N p k ^ (listComplexity p B : ℝ) :=
    Real.one_le_rpow hN1 (Nat.cast_nonneg _)
  have hf := crossing_cut_format (Real.rpow_pos_of_pos hN0 _) hBout hcount D hD γ (γ i) bins
    Λ R (fun i => ((j i : ℕ) : ℝ) / (2 : ℝ) ^ T) (fun _ => 1 / (2 : ℝ) ^ T)
    u v J P hP hbins
  have hf' := hf.mono le_rfl (show max B 4 ≤ listComplexity p B by dsimp [listComplexity]; omega)
  change Format 6 (N p k ^ (listComplexity p B : ℝ)) (listComplexity p B)
    {w | w ∈ D ∧
      ((labelsAt γ (fun i => crossing a Λ ((j i : ℕ) / (2 : ℝ) ^ T)
        (1 / (2 : ℝ) ^ T) (u i) (v i) (J i) (P i)) (γ i)
        (![w 5, w 0 + w 5 * w 1], ⌊(w 2 + w 5 * w 3 + w 5 ^ 2 * w 4) / a⌋)).card : ℝ) ≤ R}
  simpa only [hiddenPolynomial, eval_add, eval_mul, eval_pow, eval_X] using hf'

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
