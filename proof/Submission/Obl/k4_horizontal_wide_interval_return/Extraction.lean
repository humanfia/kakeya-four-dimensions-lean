import Submission.Obl.k4_horizontal_wide_interval_return.CellReturn

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set Filter

noncomputable section

def originalBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc ((j : ℕ) / (2 : ℝ) ^ T) (((j : ℕ) + 1) / (2 : ℝ) ^ T)

/-- The precise remaining input at one original true label. The frame can be
chosen after selecting the label, but its coefficient exponent is fixed. -/
def ExtractionAt {α : Type} [MeasurableSpace α]
    (N η d s v m S U R₀ : ℝ) (ν : Measure α) (ρ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (T n : ℕ) (j : Fin n → Fin (2 ^ T))
    (A B : Fin n → Set α) : Prop :=
  ∃ (i : Fin n) (lam : Measure (α × ℝ)) (Bs : Set α) (F : CellFrame) (H : ℝ),
    CellInput N η d v m S U ν lam b (A i) Bs F ∧ lam ≤ ρ ∧ Bs ⊆ B i ∧
    1 ≤ H ∧ F.q ≤ 1 ∧ F.g ≤ 1 ∧ F.a ≤ 1 ∧ |F.t₀| ≤ H ∧
    (∀ i, |F.c i| ≤ H) ∧ (∀ i, |F.L i| ≤ H) ∧ (∀ i, |F.C i| ≤ H) ∧
    2160 * N ^ (5 : ℕ) ≤ H ∧
    53 * H ^ 3 * ((F.q * F.g)⁻¹) ^ 2 ≤ N ^ R₀ ∧
    F.a = N ^ (-s) ∧ F.q = ((2 : ℝ) ^ T)⁻¹ ∧
    F.t₀ = (j i : ℕ) / (2 : ℝ) ^ T

/-- Fixed positive depths and one fixed coefficient exponent work for all
input losses. This order of quantifiers gives the frozen uniform `R`. -/
def UniformCellExtraction {α : Type} [MeasurableSpace α]
    (N : ℕ → ℝ) (d U : ℝ) (ν : ℕ → Measure α)
    (ρ : ℕ → Measure (α × ℝ)) (b : ℕ → α → Fin 6 → ℝ)
    (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α) : Prop :=
  ∃ s v m S' U' R₀ : ℝ,
    0 < s ∧ 0 < v ∧ v < m ∧ 0 < S' ∧ 0 < U' ∧ U' < m ∧ s + v ≤ U ∧ 0 ≤ R₀ ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ExtractionAt (N k) η d s v m S' U' R₀ (ν k) (ρ k) (b k)
        (T k s) (n k s) (j k s) (A k s) (B k s)

/-- The polynomial branch of the original frozen conclusion. -/
def OriginalPolynomialCandidates {α : Type} [MeasurableSpace α]
    (N : ℕ → ℝ) (d U : ℝ) (ν : ℕ → Measure α)
    (ρ : ℕ → Measure (α × ℝ)) (b : ℕ → α → Fin 6 → ℝ)
    (P : ℕ → MvPolynomial (Fin 4) ℝ)
    (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
    (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ) : Prop :=
  ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ (s v : ℝ) (i : Fin (n k s)),
      R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ U ∧
      NativeCandidate (N k) d s v ε R (T k s) (ν k) (ρ k) (b k)
        (A k s i) (B k s i) (originalBlock (T k s) (j k s i)) (F k s i) (P k)

theorem NativeCandidate.mono_budget {α : Type} [MeasurableSpace α]
    {N d s v ε r R : ℝ} {T : ℕ} {ν : Measure α} {ρ : Measure (α × ℝ)}
    {b : α → Fin 6 → ℝ} {A B : Set α} {I : Set ℝ}
    {F₀ P₀ : MvPolynomial (Fin 4) ℝ}
    (h : NativeCandidate N d s v ε r T ν ρ b A B I F₀ P₀)
    (hN : 1 ≤ N) (hr : r ≤ R) :
    NativeCandidate N d s v ε R T ν ρ b A B I F₀ P₀ := by
  obtain ⟨Q, hdeg, hcoeff, hmass⟩ := h
  refine ⟨Q, hdeg, fun e => (hcoeff e).trans ?_, hmass⟩
  have hbase : 1 ≤
      (1 + ∑ e ∈ F₀.support, |F₀.coeff e|) + ∑ e ∈ P₀.support, |P₀.coeff e| := by
    linarith [Finset.sum_nonneg (fun e (_ : e ∈ F₀.support) => abs_nonneg (F₀.coeff e)),
      Finset.sum_nonneg (fun e (_ : e ∈ P₀.support) => abs_nonneg (P₀.coeff e))]
  gcongr

/-- Once the wide argument has supplied one normalized scalar input at fixed
depths for each loss, all original-label, dyadic-time and uniform-coefficient
bookkeeping follows from the scalar theorem. -/
theorem candidates_of_uniform_extraction {α : Type} [MeasurableSpace α]
    (hScalar : Scalar) (N : ℕ → ℝ) (d U : ℝ)
    (ν : ℕ → Measure α) (ρ : ℕ → Measure (α × ℝ)) (b : ℕ → α → Fin 6 → ℝ)
    (P : ℕ → MvPolynomial (Fin 4) ℝ)
    (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
    (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop) (hd : 0 ≤ d) (hd1 : d < 1)
    (hextract : UniformCellExtraction N d U ν ρ b T n j A B) :
    OriginalPolynomialCandidates N d U ν ρ b P T n j A B F := by
  obtain ⟨s, v, m, S', U', R₀, hs, hv, hvm, hS', hU', hUm, hsU, hR₀, hmain⟩ := hextract
  let R : ℝ := R₀ + 2 + s + v + s⁻¹ + v⁻¹ + 2
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
  have hRbound : R₀ + 2 ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
  have hsR : R⁻¹ ≤ s := by
    have h : s⁻¹ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hs) h
  have hvR : R⁻¹ ≤ v := by
    have h : v⁻¹ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hv) h
  have hsR' : s ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
  have hvR' : v ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
  refine ⟨R, hR, ?_⟩
  intro ε hε
  obtain ⟨η, hη, N₀, hN₀, hscalar⟩ :=
    native_candidate_of_cell_input hScalar hd hd1 hv hvm hS' hU' hUm hε
  have hlarge : ∀ᶠ k in atTop, N₀ ≤ N k := hNt.eventually (eventually_ge_atTop N₀)
  apply Filter.Eventually.frequently
  filter_upwards [hmain η hη, hlarge] with k hk hNk
  obtain ⟨i, lam, Bs, frame, H, hinput, hlam, hBs, hH, hq1, hg1, ha1, ht₀,
    hc, hL, hC, hsize, hbudget, ha, hq, hstart⟩ := hk
  have hcan := hscalar (N k) hNk α (ν k) (ρ k) lam (b k) (A k s i) (B k s i) Bs
    frame H s R₀ (T k s) (F k s i) (P k) hinput hlam hBs hH hq1 hg1 ha1 ht₀
    hc hL hC hsize hR₀ hbudget ha hq
  have hblock : Icc frame.t₀ (frame.t₀ + frame.q) = originalBlock (T k s) (j k s i) := by
    unfold originalBlock
    rw [hstart, hq, ← one_div, ← add_div]
  rw [hblock] at hcan
  exact ⟨s, v, i, hsR, hsR', hvR, hvR', hsU,
    hcan.mono_budget (by linarith [hN k]) hRbound⟩

end

end Submission.Obl.k4_horizontal_wide_interval_return
