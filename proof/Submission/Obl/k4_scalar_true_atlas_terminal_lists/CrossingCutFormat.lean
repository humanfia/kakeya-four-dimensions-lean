import Submission.Obl.k4_scalar_true_atlas_terminal_lists.FloorFormat
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.CrossingPolynomials
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Lists

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open Set MvPolynomial

/-- The crowding cutoff uses finitely many degree-four tests. Its numerical
threshold changes only a Boolean rule and hence adds no format cost. -/
theorem crossing_cut_format {n W m d : ℕ} {R B a : ℝ}
    (ha : 0 < a) (hB : 1 ≤ B) (hcount : R + (m : ℝ) * (2 + (n : ℝ) * 6) ≤ B)
    (D : Set (Fin 6 → ℝ)) (hD : Format 6 R d D)
    (γ : Fin n → Fin W) (world : Fin W) (bins : Fin m → ℤ)
    (Λ cutoff : ℝ) (s q u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (hP : ∀ i, (P i).totalDegree ≤ 2)
    (hbins : ∀ w ∈ D, ∃ i, ⌊eval w hiddenPolynomial / a⌋ = bins i) :
    Format 6 B (max d 4) {w | w ∈ D ∧
      ((labelsAt γ (fun i => crossing a Λ (s i) (q i) (u i) (v i) (J i) (P i)) world
        (![w 5, w 0 + w 5 * w 1], ⌊eval w hiddenPolynomial / a⌋)).card : ℝ) ≤ cutoff} := by
  classical
  choose Q hQ htest using fun (i : Fin m) (j : Fin n) =>
    crossing_polynomial_tests a Λ (s j) (q j) (u j) (v j) (J j) (bins i) (P j) (hP j)
  let e := Fintype.equivFin (Fin n × Fin 6)
  let Q' (i : Fin m) (j : Fin (Fintype.card (Fin n × Fin 6))) : MvPolynomial (Fin 6) ℝ :=
    Q i (e.symm j).1 (e.symm j).2
  let S (i : Fin m) : Set (Fin (Fintype.card (Fin n × Fin 6)) → SignType) :=
    {r | ((Finset.univ.filter (fun j : Fin n =>
      γ j = world ∧ ∀ k : Fin 6, 0 ≤ r (e (j, k)))).card : ℝ) ≤ cutoff}
  let X : Fin n → Set Observation :=
    fun i => crossing a Λ (s i) (q i) (u i) (v i) (J i) (P i)
  have hpolicy (i : Fin m) (w : Fin 6 → ℝ) :
      (fun j => SignType.sign (eval w (Q' i j))) ∈ S i ↔
        ((labelsAt γ X world (![w 5, w 0 + w 5 * w 1], bins i)).card : ℝ) ≤ cutoff := by
    change (((Finset.univ.filter (fun j : Fin n => γ j = world ∧
      ∀ k : Fin 6, 0 ≤ SignType.sign (eval w (Q' i (e (j, k)))))).card : ℝ) ≤ cutoff) ↔ _
    have heq : Finset.univ.filter (fun j : Fin n => γ j = world ∧
        ∀ k : Fin 6, 0 ≤ SignType.sign (eval w (Q' i (e (j, k))))) =
        labelsAt γ X world (![w 5, w 0 + w 5 * w 1], bins i) := by
      ext j
      simp only [labelsAt, Finset.mem_filter, Finset.mem_univ, true_and]
      apply and_congr_right
      intro hγ
      simp only [Q', Equiv.symm_apply_apply, sign_nonneg_iff]
      exact (htest i j w).symm
    rw [heq]
  have hcount' : R + (m : ℝ) * (2 + (Fintype.card (Fin n × Fin 6) : ℝ)) ≤ B := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using hcount
  have hf := Format.floor_piecewise hD hB hcount' ha hiddenPolynomial
    (hiddenPolynomial_degree.trans (by omega)) bins Q' (fun i j => hQ i _ _) S
  convert hf using 1
  ext w
  constructor
  · rintro ⟨hw, hcut⟩
    obtain ⟨i, hi⟩ := hbins w hw
    refine ⟨hw, i, hi, (hpolicy i w).mpr ?_⟩
    simpa only [hi] using hcut
  · rintro ⟨hw, i, hi, hsign⟩
    refine ⟨hw, ?_⟩
    have hcut := (hpolicy i w).mp hsign
    simpa only [hi] using hcut

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
